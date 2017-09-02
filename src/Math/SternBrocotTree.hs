{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}

{-|
Module      : Math.SternBrocotTree
Description : Branch-wise and generation-wise construction of the n-dimensional S-B tree
Copyright   : (c) Michal Hadrava, 2017
License     : BSD3
Maintainer  : mihadra@gmail.com
Stability   : experimental
Portability : POSIX

This module implements the algorithm for branch-wise and generation-wise construction of the /n/-dimensional
Stern-Brocot tree due to Hakan Lennerstad as specified in \"The n-dimensional Stern-Brocot tree\", Blekige
Institute of Technology, Research report No. 2012:04.
-}
module Math.SternBrocotTree
    ( Sequence
    , treeToLevel
    , branchToSequence
    ) where

import Algebra.Graph as G (Graph, empty, overlay, overlays, vertex, edge)
import Control.Monad (replicateM, (>=>))
import Control.Monad.Loops (iterateUntil)
import Control.Monad.Freer (Eff, Member, Members, run, runM, send)
import Control.Monad.Freer.State (State, evalState, get, put)
import Control.Monad.Freer.Writer (Writer, runWriter, tell)
import Data.Foldable as F (toList)
import Data.List as L (subsequences, init, tail, map)
import Data.Monoid ()
import Data.Proxy (Proxy (..))
import Data.Vector as V hiding (replicateM)
import GHC.TypeLits (KnownNat)
import Linear.V (Finite, Size, reflectDim)
import Linear.Vector (Additive, basisFor)

data SBTree a = SBTree {toGraph :: Graph a} deriving (Show, Eq)

instance Monoid (SBTree a) where
    mempty = SBTree G.empty
    mappend (SBTree g) (SBTree g') = SBTree $ overlay g g'

-- | Sequence of /n/ coprime positive integers.
type Sequence v = (Additive v, Traversable v, Foldable v, Finite v, KnownNat (Size v), Num (v Int), Eq (v Int))

-- | Subtree of the /n/-dimensional Stern-Brocot tree extending down to the /m/th level (generation). The first
-- level corresponds to the sequence of ones.
treeToLevel :: Sequence v => Int    -- ^ /m/
    -> Graph (v Int)
treeToLevel 0 = G.empty
treeToLevel 1 = vertex 1
treeToLevel m = overlays . L.map toGraph . runTreeEff $ treeEff m

-- | Branch of the /n/-dimensional Stern-Brocot tree leading to the sequence /s/.
branchToSequence :: Sequence v => v Int -- ^ /s/
    -> Graph (v Int)
branchToSequence 1  = 1
branchToSequence sq = toGraph $ runBranchEff sq (branchEff sq)


runTreeEff :: forall v. Sequence v =>
    Eff '[EdgeEff v, SequenceEff v, IndexEff, []] [(v Int, v Int)] -> [SBTree (v Int)]
runTreeEff = runM . evalIndex (reflectDim (Proxy :: Proxy (Size v))) . runGraphEff

treeEff :: Sequence v =>
    Int -> Eff '[EdgeEff v, SequenceEff v, IndexEff, []] [(v Int, v Int)]
treeEff = flip replicateM (indexEff >>= graphEff)


runBranchEff :: Sequence v =>
    v Int -> Eff '[EdgeEff v, SequenceEff v, FactorEff] (v Int, v Int) -> SBTree (v Int)
runBranchEff sq = run . evalFactor sq . runGraphEff

branchEff :: Sequence v => v Int -> Eff '[EdgeEff v, SequenceEff v, FactorEff] (v Int, v Int)
branchEff sq = iterateUntil ((== sq) . snd) (factorEff >>= graphEff)


runGraphEff :: Sequence v =>
    Eff (EdgeEff v ': SequenceEff v ': r) w -> Eff r (SBTree (v Int))
runGraphEff = evalSequence . runEdge

graphEff :: (Sequence v, Members '[EdgeEff v, SequenceEff v] r) =>
    Vector Int -> Eff r (v Int, v Int)
graphEff = sequenceEff >=> edgeEff


type EdgeEff v = Writer (SBTree (v Int))

runEdge :: Sequence v => Eff (EdgeEff v ': r) w -> Eff r (SBTree (v Int))
runEdge = fmap snd . runWriter

edgeEff :: (Sequence v, Member (EdgeEff v) r) => (v Int, v Int) -> Eff r (v Int, v Int)
edgeEff e = do
    tell . SBTree $ uncurry edge e
    return e


type SequenceEff v = State (v Int, Vector (v Int))

evalSequence :: Sequence v => Eff (SequenceEff v ': r) w -> Eff r w
evalSequence = flip evalState (ones, basis)
    where ones  = 1
          basis = V.fromList $ basisFor ones

sequenceEff :: (Sequence v, Member (SequenceEff v) r) => Vector Int -> Eff r (v Int, v Int)
sequenceEff indices = do
    (sq, mat) <- get
    let mat' = cons sq $ backpermute mat indices
        sq'  = V.sum mat'
    put (sq', mat')
    return (sq, sq')


type IndexEff = State Int

evalIndex :: Int -> Eff (IndexEff ': r) w -> Eff r w
evalIndex = flip evalState . subtract 1

indexEff :: (Members '[IndexEff, []] r) => Eff r (Vector Int)
indexEff = do
    n <- get
    indices <- send . L.map fromList . L.tail . L.init $ subsequences [0 .. n]
    put $ V.length indices
    return indices


type FactorEff = State (Vector Int)

evalFactor :: Sequence v => v Int -> Eff (FactorEff ': r) w -> Eff r w
evalFactor sq = flip evalState (V.fromList $ F.toList sq)

factorEff :: Member FactorEff r => Eff r (Vector Int)
factorEff = do
    (f :: Vector Int) <- get
    let fmin    = V.minimum f
        f'      = V.map (subtract fmin) f
        indices = V.filter ((> 0) . (f' !)) . enumFromN 0 $ V.length f'
    put . cons fmin $ backpermute f' indices
    return indices
