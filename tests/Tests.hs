module Main
    ( main
    ) where

import Algebra.Graph (Graph, overlays, path, edges)
import Linear.V3
import Math.SternBrocotTree (treeToLevel, branchToRatio)
import Numeric.Natural (Natural)
import Test.Tasty (TestTree, defaultMain)
import Test.Tasty.Hspec (testSpec, describe, it, shouldBe)

main :: IO ()
main = testTree >>= defaultMain

testTree :: IO TestTree
testTree = testSpec "(checked by Hspec)" $ do
    describe "Math.SternBrocotTree.branchToSequence" $
        it "returns the correct branch to 16:9:6" $
            branchToRatio (V3 16 9 6) `shouldBe` correctBranch
    describe "Math.SternBrocotTree.treeToLevel" $
        it "returns the correct 3-dimensional tree down to the 3rd level" $
            treeToLevel 2 `shouldBe` correctTree
    where correctBranch = path [ V3  1 1 1
                               , V3  2 2 1
                               , V3  4 3 2
                               , V3  5 3 2
                               , V3  6 3 2
                               , V3 11 6 4
                               , V3 16 9 6] :: Graph (V3 Natural)
          correctTree   = edges [ (V3 1 1 1, V3 2 1 1)
                                , (V3 1 1 1, V3 1 2 1)
                                , (V3 1 1 1, V3 1 1 2)
                                , (V3 1 1 1, V3 2 2 1)
                                , (V3 1 1 1, V3 2 1 2)
                                , (V3 1 1 1, V3 1 2 2)
                                , (V3 2 1 1, V3 3 1 1)
                                , (V3 2 1 1, V3 3 2 2)
                                , (V3 1 2 1, V3 1 3 1)
                                , (V3 1 2 1, V3 2 3 2)
                                , (V3 1 1 2, V3 1 1 3)
                                , (V3 1 1 2, V3 2 2 3)
                                , (V3 2 2 1, V3 3 2 1)
                                , (V3 2 2 1, V3 2 3 1)
                                , (V3 2 2 1, V3 3 3 2)
                                , (V3 2 2 1, V3 3 3 1)
                                , (V3 2 2 1, V3 4 3 2)
                                , (V3 2 2 1, V3 3 4 2)
                                , (V3 2 1 2, V3 3 1 2)
                                , (V3 2 1 2, V3 2 1 3)
                                , (V3 2 1 2, V3 3 2 3)
                                , (V3 2 1 2, V3 3 1 3)
                                , (V3 2 1 2, V3 4 2 3)
                                , (V3 2 1 2, V3 3 2 4)
                                , (V3 1 2 2, V3 1 3 2)
                                , (V3 1 2 2, V3 1 2 3)
                                , (V3 1 2 2, V3 2 3 3)
                                , (V3 1 2 2, V3 1 3 3)
                                , (V3 1 2 2, V3 2 4 3)
                                , (V3 1 2 2, V3 2 3 4)] :: Graph (V3 Natural)
