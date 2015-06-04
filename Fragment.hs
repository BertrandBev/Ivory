{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

module Ivory.Tower.HAL.Bus.CAN.Fragment
  ( MessageType
  , messageType, messageType'
  , fragmentSender, fragmentSenderBlind
  , FragmentReceiveHandler
  , fragmentReceiveHandler
  , fragmentReceiver
  ) where

import Control.Monad (forM)
import Data.Either
import Data.List
import Data.Ord
import Ivory.Language
import Ivory.Serialize
import Ivory.Stdlib
import Ivory.Tower
import Ivory.Tower.HAL.Bus.CAN
import Ivory.Tower.HAL.Bus.Interface
import Numeric

--Message Type : id, Bool if extendedCANID or standardCANID, length and Ivory serialiser
data MessageType a = forall len. ANat len => MessageType
  { fragmentBaseID :: Int
  , fragmentIDExtended :: Bool
  , fragmentLength :: Proxy len
  , fragmentPackRep :: PackRep a
  }

--Secured constructor for the previously defined dataType, uses the default serializer 'packRep'
messageType :: (ANat len, Packable a)
            => Int
            -> Bool
            -> Proxy len
            -> MessageType a
messageType baseID ide bound = messageType' baseID ide bound packRep

--Secured constructor for the previously defined dataType
--Checks via the command packSize if the serializer expects a different buffer size than the one provided (bound attribute)
messageType' :: ANat len
             => Int
             -> Bool
             -> Proxy len
             -> PackRep a
             -> MessageType a
messageType' baseID ide bound rep
  | packSize rep /= fromTypeNat bound = error $
      "wrong buffer size " ++ show (fromTypeNat bound)
      ++ " given for CAN ID 0x" ++ showHex baseID ": should be "
      ++ show (packSize rep)
  | otherwise = MessageType
      { fragmentBaseID = baseID
      , fragmentIDExtended = ide
      , fragmentLength = bound
      , fragmentPackRep = rep
      }

serializeDeps :: Tower e ()
serializeDeps = do
  towerDepends serializeModule
  towerModule serializeModule
  mapM_ towerArtifact serializeArtifacts

--Main send function : takes a type (id : baseID, is extended : ide, length : bound, serializer : packRep)
--                     takes an abortable can message (tx : Abortable transmit) 
--                     returns a Tower 
fragmentSender :: (IvoryArea a, IvoryZero a)
               => MessageType a
               -> AbortableTransmit (Struct "can_message") (Stored IBool)
               -> Tower e (ChanInput a, ChanInput (Stored IBool), ChanOutput (Stored IBool))
fragmentSender (MessageType baseID ide bound rep) tx = do
  serializeDeps

  --channel local variables initialisation
  (reqChan, reqSrc) <- channel
  (abortChan, abortSrc) <- channel
  (resDst, resChan) <- channel

  --creates string hexadecimal representaion of the msg ID
  let idstr = "0x" ++ showHex baseID ""
  monitor ("fragment_" ++ idstr) $ do
    --initialize the key-value pair state variables corresponding to 
     --'sent' (Uint8) counts the number of packets sent till now
     --'buf' (Bits array of length 'bound') will be the full message buffer
     --'aborting' (Bool) stores the abort request
    sent <- stateInit ("fragment_sent_" ++ idstr) (izero :: Init (Stored Uint8))
    buf <- stateInit ("fragment_buf_" ++ idstr) (izerolen bound)
    aborting <- state ("fragment_aborting_" ++ idstr)

     --function to retrieve the 'idx'th 8 bits unit of the buffer 'buf'
    let sendFragment idx = do
          let remaining_len = arrayLen buf - 8 * idx
          let len = (remaining_len >? 8) ? (8, remaining_len)
          --structure for the actual packet to send
          --can_message_id = baseID + idx wrapped in either an extendedCANID or a standardCANID
          --can_message_length = MIN ( 8 , remaining_len )
          --can_message_buf => empty local buffer
          msg <- local $ istruct
            [ can_message_id .= ival (if ide
                then extendedCANID (fromRep $ fromIntegral baseID + safeCast idx) (boolToBit false)
                else standardCANID (fromRep $ fromIntegral baseID + safeCast idx) (boolToBit false))
            , can_message_len .= ival (toIx len)
            ]
          --loop to fill the buffer 'can_message_buf' with the relevant bits
          for (toIx len) $ \ i -> refCopy (msg ~> can_message_buf ! i) (buf ! toIx (safeCast idx * 8 + fromIx i))
          --increments the send counter
          store sent (idx + 1)
          return msg

    --handles the send message request
    handler reqSrc ("fragment_req_" ++ idstr) $ do
      --obtain an emitter
      txReq <- emitter (abortableTransmit tx) 1
      --get the request message in 'req'
      callback $ \ req -> do
        was_sent <- deref sent
        --makes sure that no message sending operation is running
        assert $ was_sent ==? 0

        --store the message in the buffer using the serialiser 'rep'
        packInto' rep buf 0 req
        --get the first 8-bits lump
        msg <- sendFragment 0
        --send it
        emit txReq $ constRef msg

    --handles the send message success callback
    handler (abortableComplete tx) ("fragment_complete_" ++ idstr) $ do
      txReq <- emitter (abortableTransmit tx) 1
      res <- emitter resDst 1
      callbackV $ \ success -> do
        --ending function to emit the success/failure boolean ('v') and to  clear the local state variables
        let finished v = do
              emitV res v
              store sent 0
              store aborting false
        
         --if (failure) then (send failure, reset state) else ..
        ifte_ (iNot success) (finished false) $ do
          already_sent <- deref sent
          --makes sure that the first message has been sent
          assert $ already_sent >? 0
          
          --if (the whole buffer has been processed) then  (send success, reset state) else ...
          ifte_ (arrayLen buf <=? 8 * (safeCast already_sent :: Uint16)) (finished true) $ do
            should_abort <- deref aborting
            --if (abort call received since last sending operation) then (send failure, reset state) else ...
            ifte_ should_abort (finished false) $ do
              --get the next 8-bits lump message
              msg <- sendFragment already_sent
              --send it
              emit txReq $ constRef msg

    --handles an abort request
    handler abortSrc ("fragment_abort_" ++ idstr) $ do
      txAbort <- emitter (abortableAbort tx) 1
      callback $ const $ do
        --stores the request, which will be processed during the next callback to ("fragment_complete_" ++ idstr)
        --which means before the attempt to send the next 8-bits lumb of the buffer
        store aborting true
        emitV txAbort true

  return (reqChan, abortChan, resChan)

-- | Like fragmentSender, but provides no feedback about the success or
-- failure of the transmission. Useful when the caller doesn't need to
-- know whether the message made it onto the bus.
fragmentSenderBlind :: (IvoryArea a, IvoryZero a)
                    => ChanOutput a
                    -> MessageType a
                    -> AbortableTransmit (Struct "can_message") (Stored IBool)
                    -> Tower e ()
fragmentSenderBlind src mt tx = do
  (fragReq, fragAbort, fragDone) <- fragmentSender mt tx

  let idstr = "0x" ++ showHex (fragmentBaseID mt) ""
  monitor ("fragment_blindly_" ++ idstr) $ do
    msg <- state ("msg_" ++ idstr)
    in_progress <- state ("in_progress_" ++ idstr)
    abort_pending <- state ("abort_pending_" ++ idstr)

    handler src "new_msg" $ do
      toFrag <- emitter fragReq 1
      doAbort <- emitter fragAbort 1
      callback $ \ new_msg -> do
        refCopy msg new_msg
        was_in_progress <- deref in_progress
        ifte_ was_in_progress (emitV doAbort true >> store abort_pending true) (emit toFrag (constRef msg) >> store in_progress true)

    handler fragDone "fragment_done" $ do
      toFrag <- emitter fragReq 1
      callback $ const $ do
        was_aborting <- deref abort_pending
        when was_aborting $ do
          emit toFrag $ constRef msg
          store abort_pending false
        store in_progress was_aborting

data FragmentReceiveHandler = forall a. (IvoryArea a, IvoryZero a) => FragmentReceiveHandler
  { fragmentReceiveChannel :: ChanInput a
  , fragmentReceiveType :: MessageType a
  }

-- | Associate reassembled messages of the given type with the given
-- channel.
fragmentReceiveHandler :: (IvoryArea a, IvoryZero a)
                       => ChanInput a
                       -> MessageType a
                       -> FragmentReceiveHandler
fragmentReceiveHandler chan mt = FragmentReceiveHandler
  { fragmentReceiveChannel = chan
  , fragmentReceiveType = mt
  }
        
--Structure to store the reassembled messages
data GeneratedHandler = GeneratedHandler
  { generatedBaseID :: Int
  --function that takes 
  , generatedHandler :: forall s s'. Uint8 -> ConstRef s (Struct "can_message") -> Ivory (AllocEffects s') ()
  }

-- | Attach all of the given 'FragmentReceiveHandler's to this stream
-- of incoming CAN messages, reassembling fragments appropriately.
fragmentReceiver :: ChanOutput (Struct "can_message")
                 -> [FragmentReceiveHandler]
                 -> Tower e ()
fragmentReceiver src handlers = do
  serializeDeps

  monitor "fragment_reassembly" $ do
  
    --Main loop over the FragmentReceiveHandlers contained in the list 'handlers'
    --pattern match the channel ober 'chan' message content over (id : baseID, is extended : ide, length : bound, serializer : rep)
    emitters <- forM handlers $ \ (FragmentReceiveHandler chan (MessageType baseID ide bound rep)) -> do
      --reconstruct the string hex representation of the current ID
      let idstr = "0x" ++ showHex baseID ""
      --initialize the key-value pair state variables corresponding to 
       -- the exepcted next_id of the current message
       -- its current buffer (containing all the previously stored incoming messages)
      next_idx <- stateInit ("reassembly_next_idx_" ++ idstr) (izero :: Init (Stored Uint8))
      buf <- stateInit ("reassembly_buf_" ++ idstr) (izerolen bound)
      
      --deduce from the size of the current buffer the expected last fragment id and length
      let last_fragment_idx = fromInteger $ (arrayLen buf - 1) `div` 8
      let last_fragment_length = fromInteger $ ((arrayLen buf + 7) `mod` 8) + 1

      return $ do
        e <- emitter chan 1
        --according to the exended attribute of the id, return a Left GeneratedHandler of a Right GeneratedHandler
        --(see Either in Haskell)
        return $ (if ide then Left else Right) $ GeneratedHandler
          { generatedBaseID = baseID
          --function that, given a msg and an id, will append it to the current buffer for this message
          , generatedHandler = \ idx msg -> do
              expected_idx <- deref next_idx
              --boolean that checks whether it is a retransmission
              let is_retransmit = idx + 1 ==? expected_idx
              --boolean that checks the validity of the id (it can't exess last fragment id)
              let is_not_mine = idx >? last_fragment_idx
              --in either case, ignore the message
              unless (is_retransmit .|| is_not_mine) $ do
                --retrieve the length, check if is new, expected, and deduce if the idx is valid
                len <- fmap fromIx $ deref $ msg ~> can_message_len
                let is_new_fragment = idx ==? 0
                let is_expected_fragment = idx ==? expected_idx
                let has_bad_idx = iNot (is_new_fragment .|| is_expected_fragment)
                 --get expected length, compare it with the actual one
                let expected_length = (idx ==? last_fragment_idx) ? (last_fragment_length, 8)
                let has_bad_length = len /=? expected_length
                --define a discard function that resets the nextId
                let discard = store next_idx 0
                --if (id or length is incorrect) then discard else ...
                ifte_ (has_bad_idx .|| has_bad_length) discard $ do
                  --copy the msg 8-bits buffer into the current buffer
                  arrayCopy buf (msg ~> can_message_buf) (safeCast idx * 8) len
                  --if (the message is not the last) then increment next_id else...
                  ifte_ (idx <? last_fragment_idx) (store next_idx $ idx + 1) $ do
                    --initialize an empty mem area, unpack the whole buffer inside, send it ti the emitter
                    assembled <- local izero
                    unpackFrom' rep (constRef buf) 0 assembled
                    emit e $ constRef assembled
          }

    --handles the receive message callback
    handler src "receive_msg" $ do
      --takes the handlers (Either GeneratedHandler), put the Left ones in the first case and the Right ones in the second case
      --The purpose is to separate the extended ids from the standard ones
      (ext, std) <- fmap partitionEithers $ sequence emitters
      callback $ \ msg -> do
        --get the message id : retrieve the value, get the id and the extended bit, and build the corresponding msgID 
        arbitration <- deref $ msg ~> can_message_id
        let rawMsgID = toRep $ arbitration #. can_arbitration_id
        let ide = bitToBool $ arbitration #. can_arbitration_ide
        let msgID = ide ? (rawMsgID, rawMsgID `iShiftR` 18)
        --one if a function that takes a handler, and gives it the messages if its id is greater than or equals to its base id with the corresponding relative id (idx) in that case
        let one (GeneratedHandler baseID f) = (msgID >=? fromIntegral baseID) ==> f (castDefault $ msgID - fromIntegral baseID) msg
        --main function that maps the previous distribution function to a list of handlers
        --the list is sorted by baseId
        let handle = cond_ . map one . sortBy (flip $ comparing generatedBaseID)
        --finally, run the previously defined handle function on the proper handle group, according to the type of the can Id b
