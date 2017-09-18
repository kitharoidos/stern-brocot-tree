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

import Algebra.Graph as G (Graph, empty, overlay, overlays, vertices, edges)
import Control.Monad (replicateM)
import Control.Monad.Loops (iterateUntil)
import Control.Monad.Freer (Eff, Member, Members, run, runM, send)
import Control.Monad.Freer.Exception (Exc, throwError, runError)
import Control.Monad.Freer.State (State, evalState, get, put)
import Control.Monad.Freer.Writer (Writer, runWriter, tell)
import Data.Foldable as F (foldl1)
import Data.List as L (subsequences, init, tail, map, head)
import Data.Monoid ()
import Data.Proxy (Proxy (..))
import Data.Vector as V hiding (replicateM)
import GHC.TypeLits (Nat, KnownNat)
import Linear.V (V, toVector, reflectDim, dim)
import Linear.Vector (basis, basisFor)
import Numeric.Natural (Natural)
import Numeric.Positive (Positive)


-- | An /n/-part ratio, i.e. a node in the /n/-dimensional Stern-Brocot tree.
type Ratio (n :: Nat) = V n Positive

-- | A vertex in the /n/-dimensional Stern-Brocot tree.
type Vertex (n :: Nat) = V n Natural

data DimTooLow = DimTooLow deriving (Show, Eq)

instance Monoid (Graph (Vertex n)) where
    mempty  = G.empty
    mappend = overlay

-- | Subtree of the /n/-dimensional Stern-Brocot tree extending down to the /m/th level (generation). The first
-- level corresponds to the ratio 1:1:...1.
treeToLevel :: KnownNat n => Int    -- ^ /m/
    -> Graph (Vertex n)
treeToLevel = overlays . runTreeToLevelEff . treeToLevelEff

treeToSubratio :: forall n. KnownNat n => Ratio n   -- ^ /r/
    -> Graph (Vertex n)
treeToSubratio r
    | dim r >= 2 = undefined
    | otherwise = G.empty

-- | Branch of the /n/-dimensional Stern-Brocot tree leading to the ratio /r/.
branchToRatio :: KnownNat n => Ratio n -- ^ /r/
    -> Graph (Vertex n)
branchToRatio r = runBranchToRatioEff r'' (branchToRatioEff r'')
    where r'  = fromIntegral <$> r
          r'' = flip div (F.foldl1 gcd r') <$> r'


runTreeToLevelEff :: forall n w. KnownNat n =>
    Eff '[EdgeEff n, RatioEff n, Exc DimTooLow, IndexEff, []] w -> [Graph (Vertex n)]
runTreeToLevelEff = runM . evalIndex (reflectDim (Proxy :: Proxy n)) . runGraphEff

treeToLevelEff :: forall n. KnownNat n =>
    Int -> Eff '[EdgeEff n, RatioEff n, Exc DimTooLow, IndexEff, []] [Vertex n]
treeToLevelEff m = do
    tell $ vertices (basis :: [Vertex n])
    replicateM m (indexEff >>= graphEff)


runBranchToRatioEff :: KnownNat n =>
    Vertex n -> Eff '[EdgeEff n, RatioEff n, Exc DimTooLow, FactorEff] w -> Graph (Vertex n)
runBranchToRatioEff r = run . evalFactor r . runGraphEff

branchToRatioEff :: KnownNat n => Vertex n -> Eff '[EdgeEff n, RatioEff n, Exc DimTooLow, FactorEff] (Vertex n)
branchToRatioEff r = iterateUntil (== r) (factorEff >>= graphEff)


runGraphEff :: KnownNat n =>
    Eff (EdgeEff n ': RatioEff n ': Exc DimTooLow ': effs) w -> Eff effs (Graph (Vertex n))
runGraphEff eff = do
    x <- runError . evalRatio $ runEdge eff
    return $ case x of
        Left  DimTooLow -> G.empty
        Right g         -> g

graphEff :: forall n effs. (KnownNat n, Members '[EdgeEff n, RatioEff n, Exc DimTooLow] effs) =>
    Vector Int -> Eff effs (Vertex n)
graphEff indices
    | reflectDim (Proxy :: Proxy n) >= 2 = ratioEff indices >>= edgeEff
    | otherwise = throwError DimTooLow


type EdgeEff n = Writer (Graph (Vertex n))

runEdge :: Eff (EdgeEff n ': effs) w -> Eff effs (Graph (Vertex n))
runEdge = fmap snd . runWriter

edgeEff :: forall n effs. (KnownNat n, Members [EdgeEff n, Exc DimTooLow] effs) =>
    [(Vertex n, Vertex n)] -> Eff effs (Vertex n)
edgeEff e
    | reflectDim (Proxy :: Proxy n) >= 1 = do
        tell $ edges e
        return . snd $ L.head e
    | otherwise = throwError DimTooLow


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

indexEff :: (Members '[IndexEff, []] effs) => Eff effs (Vector Int)
indexEff = do
    n <- get
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
