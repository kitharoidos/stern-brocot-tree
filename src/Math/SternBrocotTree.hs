{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Math.SternBrocotTree
    ( treeToLevel
    , branchToSequence
    ) where

import Algebra.Graph as G (Graph, empty, overlay, overlays, edge)
import Control.Monad (replicateM, void)
import Control.Monad.Loops (iterateUntil)
import Control.Eff (Eff, Member, SetMember, (:>), run)
import Control.Eff.Lift (Lift, runLift, lift)
import Control.Eff.State.Lazy (State, evalState, get, put)
import Control.Eff.Writer.Lazy (Writer, runMonoidWriter, tell)
import Data.Monoid
import Data.Typeable
import Data.Void (Void)
import Data.List as L (subsequences, init, map, replicate)
import Data.Vector.Unboxed as V hiding (replicateM)
import Linear.V (V, Dim, reflectDim, toVector)
import Linear.Vector (basisFor)


type SBTree n = Graph (V n Int)

instance Monoid (SBTree n) where
    mempty  = G.empty
    mappend = overlay


treeToLevel :: (Dim n, Typeable n) => Int -> SBTree n
treeToLevel = runTreeEff . treeEff

branchToSequence :: (Dim n, Typeable n) => V n Int -> SBTree n
branchToSequence sq = runBranchEff sq (branchEff sq)


runTreeEff :: forall n v. (Dim n, Typeable n) =>
    Eff (EdgeEff n :> SequenceEff n :> IndexEff :> Lift [] :> Void) v -> SBTree n
runTreeEff = overlays . runLift . evalIndex (reflectDim (Proxy :: Proxy n)) . runGraphEff

treeEff :: (Dim n, Typeable n) =>
    Int -> Eff (EdgeEff n :> SequenceEff n :> IndexEff :> Lift [] :> Void) [(V n Int, V n Int)]
treeEff = flip replicateM (indexEff >>= graphEff)


runBranchEff :: (Dim n, Typeable n) =>
    V n Int -> Eff (EdgeEff n :> SequenceEff n :> FactorEff :> Void) v -> SBTree n
runBranchEff sq = run . evalFactor sq . runGraphEff

branchEff :: (Dim n, Typeable n) =>
    V n Int -> Eff (EdgeEff n :> SequenceEff n :> FactorEff :> Void) ()
branchEff sq = void $ iterateUntil ((== sq) . snd) (factorEff >>= graphEff)


runGraphEff :: (Dim n, Typeable n) => Eff (EdgeEff n :> SequenceEff n :> r) a -> Eff r (SBTree n)
runGraphEff = evalSequence . runEdge

graphEff :: (Dim n, Typeable n, Member (EdgeEff n) r, Member (SequenceEff n) r) =>
    Vector Int -> Eff r (V n Int, V n Int)
graphEff indices = sequenceEff indices >>= edgeEff


type EdgeEff n = Writer (SBTree n)

runEdge :: (Dim n, Typeable n) => Eff (EdgeEff n :> r) a -> Eff r (SBTree n)
runEdge = fmap fst . runMonoidWriter

edgeEff :: (Dim n, Typeable n, Member (EdgeEff n) r) =>
    (V n Int, V n Int) -> Eff r (V n Int, V n Int)
edgeEff e = do
    tell $ uncurry edge e
    return e


type SequenceEff n = State (V n Int, Vector (V n Int))

evalSequence :: forall n r w. (Dim n, Typeable n) => Eff (SequenceEff n :> r) w -> Eff r w
evalSequence = evalState (ones, basis)
    where ones  = 1 :: V n Int
          basis = V.fromList $ basisFor ones

sequenceEff :: (Dim n, Typeable n, Member (SequenceEff n) r) =>
    Vector Int -> Eff r (V n Int, V n Int)
sequenceEff indices = do
    (sq, mat) <- get
    let mat' = cons sq $ backpermute mat indices
        sq'  = V.sum mat'
    put (sq', mat')
    return (sq, sq')


type IndexEff = State (Vector Int)

evalIndex :: Int -> Eff (IndexEff :> Lift [] :> Void) w -> Eff (Lift [] :> Void) w
evalIndex n = evalState (enumFromN 0 n)

indexEff :: (Member IndexEff r, SetMember Lift (Lift []) r) => Eff r (Vector Int)
indexEff = do
    indices <- lift . L.map fromList . L.init . subsequences . toList =<< get
    put indices
    return indices


type FactorEff = State (Vector Int)

evalFactor :: Dim n => V n Int -> Eff (FactorEff :> Void) w -> Eff Void w
evalFactor sq = evalState (convert $ toVector sq)

factorEff :: Member FactorEff r => Eff r (Vector Int)
factorEff = do
    (f :: Vector Int) <- get
    let fmin    = V.minimum f
        f'      = V.map (subtract fmin) f
        indices = V.filter ((> 0) . (f' !)) . enumFromN 0 $ V.length f'
    put . cons fmin $ backpermute f' indices
    return indices
