module Language.Nominal.Examples.IdealisedEUTxOSpec
    ( spec
    ) where

import Test.Hspec
import Test.QuickCheck

import Language.Nominal.Properties.SpecUtilities ()

import Language.Nominal.Properties.Examples.IdealisedEUTxOSpec

spec :: Spec
spec = do
    it "Sanity check: every arbitrary chunk is valid" $ property prop_arbitraryChunkIsValid 
    it "Sanity check: every arbitrary chunk is valid (alternate test)" $ property prop_arbitraryChunkIsValid' 
    it "Sanity check: not every chunk is a blockchain (might have UTxIs)" $ property prop_notEveryChunkBlockchain 
    it "Sanity check: an arbitary transaction is indeed a transaction" $ property prop_arbitraryTxIsValid
    it "Sanity check: an arbitary blockchain is indeed a valid blockchain" $ property prop_arbitraryBlockchainIsValid
    it "Sanity check: arbitrary instance of TB generates a blockchain, which is equal to itself" $ property prop_blockchainToChunkAndBack 
    it "Blockchain has no UTxIs" $ property prop_blockchainHasNoUTxIs 
    describe "Chunk is equal to itself" $ do
        it "atValFin"  $ property $ prop_chunkrefl atValFin
        it "atValTriv" $ property $ prop_chunkrefl atValTriv
    it "There are two different chunks" $ property prop_chunkneq 
    it "Empty chunk is prefix of any chunk" $ property prop_emptyIsPrefix 
    it "The tail of a chunk, is a chunk" $ property prop_chunkTail_is_chunk 
    it "The tail of a chunk, is a prefix of the original chunk" $ property prop_chunkTail_is_prefix
    it "The tail of a chunk, is a prefix of the original chunk.  Gotcha version, that doesn't have the Nom bindings: expect failure here" $ property prop_chunkTail_is_prefix_gotcha 
    it "Plausible-but-wrong @'warningNotChunkTail'@ is wrong: expect failure here" $ property prop_warningNotChunkTail_is_not_chunk 
    it "Underbinding check (not enough atoms bound)" $ property prop_underbinding
    it "Overbinding check (too many atoms bound)" $ property prop_overbinding
    it "Gotcha: Fails because loss of information from two Nom bindings" $ property prop_chunkHead_chunkTail_recombine 
    it "Succeeds because one Nom binding thus no loss of information" $ property prop_chunkHdTl_recombine 
    it "If you reverse the order of transactions in a chunk, it need not be valid" $ property prop_reverseIsNotValid 
-- slow to run
--  it "Subchunks of a valid chunk, are valid chunks" $ property prop_subchunksValid 
    it "If two transactions are apart, they can be validly combined" $ property prop_apart_is_valid_tx 
    it "If two chunks are apart, they can be validly combined" $ property prop_apart_is_valid_ch 
    it "If two chunks are apart, they can be validly commuted" $ property prop_chunk_apart_commutes
    it "Lemma 2.14(2)" $ property prop_validity_fresh 
