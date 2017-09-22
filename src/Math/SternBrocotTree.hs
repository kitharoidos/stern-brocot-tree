{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{-|
Module      : Math.SternBrocotTree
Description : Branch-wise and generation-wise construction of the n-dimensional Stern-Brocot tree
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
    ( Ratio
    , Vertex
    , treeToLevel
    , treeToSubratio
    , branchToRatio
    ) where

import Algebra.Graph as G (Graph, empty, overlay, overlays, edges)
import Control.Monad as M (msum, guard)
import Control.Monad.Loops (iterateUntil)
import Control.Monad.Freer (Eff, Member, Members, run, runM, send)
import Control.Monad.Freer.NonDet (NonDet, makeChoiceA)
import Control.Monad.Freer.State (State, evalState, get, put, modify)
import Control.Monad.Freer.Writer (Writer, runWriter, tell)
import Data.Foldable as F (foldl1)
import Data.List as L (subsequences, init, tail, map, head)
import Data.Monoid ()
import Data.Proxy (Proxy (..))
import Data.Vector as V hiding (replicateM, modify)
import GHC.TypeLits (Nat, KnownNat)
import Linear.V (V, toVector, reflectDim)
import Linear.Vector (basisFor)
import Numeric.Natural (Natural)
import Numeric.Positive (Positive)


-- | An /n/-part ratio, i.e. a node in the /n/-dimensional Stern-Brocot tree.
type Ratio (n :: Nat) = V n Positive

-- | A vertex in the /n/-dimensional Stern-Brocot tree.
type Vertex (n :: Nat) = V n Natural

-- | Subtree of the /n/-dimensional Stern-Brocot tree extending down to the /m/th level (generation). The first
-- level corresponds to the ratio 1:1:...1.
treeToLevel :: KnownNat n => Positive    -- ^ /m/
    -> Graph (Vertex n)
treeToLevel = overlays . runTreeToLevelEff . treeToLevelEff

treeToSubratio :: forall n. KnownNat n => Ratio n   -- ^ /r/
    -> Graph (Vertex n)
treeToSubratio = undefined

-- | Branch of the /n/-dimensional Stern-Brocot tree leading to the ratio /r/.
branchToRatio :: KnownNat n => Ratio n -- ^ /r/
    -> Graph (Vertex n)
branchToRatio r = runBranchToRatioEff r'' (branchToRatioEff r'')
    where r'  = fromIntegral <$> r
          r'' = flip div (F.foldl1 gcd r') <$> r'


data DimTooLow = DimTooLow deriving (Show, Eq)
          
instance Monoid (Graph (Vertex n)) where
    mempty  = G.empty
    mappend = overlay


runTreeToLevelEff :: forall n. KnownNat n =>
    Eff '[EdgeEff n, RatioEff n, NonDet, IndexEff, CounterEff, []] (Vertex n) -> [Graph (Vertex n)]
runTreeToLevelEff = runM . flip evalState 0 . evalIndex (reflectDim (Proxy :: Proxy n)) . runGraphEff

treeToLevelEff :: (KnownNat n, Members '[CounterEff, EdgeEff n, RatioEff n, NonDet, IndexEff, []] effs) =>
    Positive -> Eff effs (Vertex n)
treeToLevelEff m = fmap fst $ iterateUntil ((== m') . snd) (indexEff >>= graphEff >>= counterEff)
    where m' = fromIntegral m


type CounterEff = State Natural

counterEff :: (KnownNat n, Member CounterEff effs) => Vertex n -> Eff effs (Vertex n, Natural)
counterEff v = do
    modify (+ (1 :: Natural))
    i <- get
    return (v, i)


runBranchToRatioEff :: KnownNat n =>
    Vertex n -> Eff '[EdgeEff n, RatioEff n, NonDet, FactorEff] (Vertex n) -> Graph (Vertex n)
runBranchToRatioEff r = run . evalFactor r . runGraphEff

branchToRatioEff :: (KnownNat n, Members '[EdgeEff n, RatioEff n, NonDet, FactorEff] effs) =>
    Vertex n -> Eff effs (Vertex n)
branchToRatioEff r = iterateUntil (== r) (factorEff >>= graphEff)


runGraphEff :: forall n effs. KnownNat n =>
    Eff (EdgeEff n ': RatioEff n ': NonDet ': effs) (Vertex n) -> Eff effs (Graph (Vertex n))
runGraphEff eff = fmap msum eff'
    where eff' = makeChoiceA . evalRatio $ runEdge eff :: Eff effs (Maybe (Graph (Vertex n)))

graphEff :: forall n effs. (KnownNat n, Members '[EdgeEff n, RatioEff n, NonDet] effs) =>
    Vector Int -> Eff effs (Vertex n)
graphEff indices = do
    guard $ reflectDim (Proxy :: Proxy n) >= 2
    ratioEff indices >>= edgeEff


type EdgeEff n = Writer (Graph (Vertex n))

runEdge :: Eff (EdgeEff n ': effs) w -> Eff effs (Graph (Vertex n))
runEdge = fmap snd . runWriter

edgeEff :: forall n effs. (KnownNat n, Members [EdgeEff n, NonDet] effs) =>
    [(Vertex n, Vertex n)] -> Eff effs (Vertex n)
edgeEff e = do
    guard $ reflectDim (Proxy :: Proxy n) >= 1
    tell $ edges e
    return . snd $ L.head e


type RatioEff n = State (Vertex n, Vector (Vertex n))

evalRatio :: forall n effs w. KnownNat n => Eff (RatioEff n ': effs) w -> Eff effs w
evalRatio = flip evalState (ones, basis')
    where ones   = 1 :: Vertex n
          basis' = V.fromList $ basisFor ones

ratioEff :: KnownNat n => Member (RatioEff n) effs => Vector Int -> Eff effs [(Vertex n, Vertex n)]
ratioEff indices = do
    (r, mat) <- get
    let mat' = cons r $ backpermute mat indices
        r'  = V.sum mat'
    put (r', mat')
    return $ (, r) <$> V.toList mat


type IndexEff = State Int

evalIndex :: Int -> Eff (IndexEff ': effs) w -> Eff effs w
evalIndex = flip evalState . subtract 1

indexEff :: (Members '[IndexEff, NonDet, []] effs) => Eff effs (Vector Int)
indexEff = do
    n <- get
    guard $ n >= 0
    indices <- send . L.map fromList . L.tail . L.init $ subsequences [0 .. n]
    put $ V.length indices
    return indices


type FactorEff = State (Vector Natural)

evalFactor :: Vertex n -> Eff (FactorEff ': effs) w -> Eff effs w
evalFactor r = flip evalState (toVector r)

factorEff :: Member FactorEff effs => Eff effs (Vector Int)
factorEff = do
    (f :: Vector Natural) <- get
    let fmin    = V.minimum f
        f'      = V.map (subtract fmin) f
        indices = V.filter ((> 0) . (f' !)) . enumFromN 0 $ V.length f'
    put . cons fmin $ backpermute f' indices
    return indices
