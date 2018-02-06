{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}
module A where
import qualified Text.Show.Functions
import qualified Data.Constraint as QS
import qualified Data.Ratio as R
import qualified Data.Typeable as T
import qualified GHC.Generics as G
import qualified Prelude as P
import qualified QuickSpec as QS
import qualified QuickSpec.Signature as QS
import qualified QuickSpec.Term as QS
import qualified Test.Feat as F
import qualified Test.QuickCheck as QC
import qualified Tip.Haskell.GenericArbitrary
import qualified Tip.Haskell.Observers
data Stream a = SCons a (Stream a)
  deriving (P.Eq, P.Ord, P.Show, G.Generic, T.Typeable)
F.deriveEnumerable (''Stream)
instance
  ((T.Typeable a, QC.Arbitrary a)) => QC.Arbitrary (Stream a)
  where
  arbitrary = Tip.Haskell.GenericArbitrary.genericArbitrary
instance ((QC.CoArbitrary a)) => QC.CoArbitrary (Stream a) where
  coarbitrary = QC.genericCoarbitrary
data ObsStream a = ObsSCons a (ObsStream a) | NullConsStream
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
obsFunStream :: P.Int -> Stream a -> ObsStream a
obsFunStream 0 _ = NullConsStream
obsFunStream n x =
  case n P.< (0) of
    P.True -> obsFunStream (P.negate n) x
    P.False ->
      case x of
        SCons x0 x1 -> ObsSCons x0 (obsFunStream (n P.- (1)) x1)
        _ -> NullConsStream
stl ::
  forall b .
    (QC.Arbitrary b, QC.CoArbitrary b, T.Typeable b) =>
      Stream b -> Stream b
stl (SCons x12 x2) = x2
siterate ::
  forall c .
    (QC.Arbitrary c, QC.CoArbitrary c, T.Typeable c) =>
      (c -> c) -> c -> Stream c
siterate y z = SCons z (siterate y (P.id y z))
shd ::
  forall a2 .
    (QC.Arbitrary a2, QC.CoArbitrary a2, T.Typeable a2) =>
      Stream a2 -> a2
shd (SCons x13 x22) = x13
smap ::
  forall a3 b2 .
    (QC.Arbitrary a3, QC.CoArbitrary a3, T.Typeable a3,
     QC.Arbitrary b2, QC.CoArbitrary b2, T.Typeable b2) =>
      (a3 -> b2) -> Stream a3 -> Stream b2
smap x3 y2 = SCons (P.id x3 (shd y2)) (smap x3 (stl y2))
sig =
  ([((QS.constant
        "stl"
        ((\ QS.Dict -> stl) ::
           QS.Dict
             (QC.Arbitrary QS.A, QC.CoArbitrary QS.A, T.Typeable QS.A) ->
             Stream QS.A -> Stream QS.A))
       {QS.conSize = 0},
     [(2) :: P.Int, (3) :: P.Int, (4) :: P.Int]),
    ((QS.constant
        "siterate"
        ((\ QS.Dict -> siterate) ::
           QS.Dict
             (QC.Arbitrary QS.A, QC.CoArbitrary QS.A, T.Typeable QS.A) ->
             (QS.A -> QS.A) -> QS.A -> Stream QS.A))
       {QS.conSize = 0},
     [(1) :: P.Int, (4) :: P.Int]),
    ((QS.constant
        "shd"
        ((\ QS.Dict -> shd) ::
           QS.Dict
             (QC.Arbitrary QS.A, QC.CoArbitrary QS.A, T.Typeable QS.A) ->
             Stream QS.A -> QS.A))
       {QS.conSize = 0},
     [(0) :: P.Int, (3) :: P.Int, (4) :: P.Int]),
    ((QS.constant
        "smap"
        ((\ QS.Dict -> smap) ::
           QS.Dict
             (QC.Arbitrary QS.A, QC.CoArbitrary QS.A, T.Typeable QS.A,
              QC.Arbitrary QS.B, QC.CoArbitrary QS.B, T.Typeable QS.B) ->
             (QS.A -> QS.B) -> Stream QS.A -> Stream QS.B))
       {QS.conSize = 0},
     [(3) :: P.Int, (4) :: P.Int])],
   QS.signature
     {QS.constants =
        [(QS.constant
            "SCons"
            ((\ QS.Dict -> SCons) ::
               QS.Dict
                 (QC.Arbitrary QS.A, QC.CoArbitrary QS.A, T.Typeable QS.A) ->
                 QS.A -> Stream QS.A -> Stream QS.A))
           {QS.conSize = 0, QS.conIsBackground = P.True}],
      QS.instances =
        [QS.makeInstance
           ((\ (QS.Dict, (QS.Dict, (QS.Dict, ()))) -> P.return QS.Dict) ::
              (QS.Dict (QC.Arbitrary QS.A),
               (QS.Dict (QC.CoArbitrary QS.A),
                (QS.Dict (T.Typeable QS.A), ()))) ->
                QC.Gen
                  (QS.Dict
                     (QC.Arbitrary QS.A, QC.CoArbitrary QS.A, T.Typeable QS.A))),
         QS.makeInstance
           ((\ (QS.Dict, (QS.Dict, (QS.Dict, ()))) -> P.return QS.Dict) ::
              (QS.Dict (QC.Arbitrary QS.A),
               (QS.Dict (QC.CoArbitrary QS.A),
                (QS.Dict (T.Typeable QS.A), ()))) ->
                QC.Gen
                  (QS.Dict
                     (QC.Arbitrary QS.A, QC.CoArbitrary QS.A, T.Typeable QS.A))),
         QS.makeInstance
           ((\ (QS.Dict, (QS.Dict, (QS.Dict, ()))) -> P.return QS.Dict) ::
              (QS.Dict (QC.Arbitrary QS.A),
               (QS.Dict (QC.CoArbitrary QS.A),
                (QS.Dict (T.Typeable QS.A), ()))) ->
                QC.Gen
                  (QS.Dict
                     (QC.Arbitrary QS.A, QC.CoArbitrary QS.A, T.Typeable QS.A))),
         QS.makeInstance
           ((\ (QS.Dict, (QS.Dict, (QS.Dict, ()))) -> P.return QS.Dict) ::
              (QS.Dict (QC.Arbitrary QS.A),
               (QS.Dict (QC.CoArbitrary QS.A),
                (QS.Dict (T.Typeable QS.A), ()))) ->
                QC.Gen
                  (QS.Dict
                     (QC.Arbitrary QS.A, QC.CoArbitrary QS.A, T.Typeable QS.A))),
         QS.makeInstance
           ((\ (QS.Dict,
                (QS.Dict, (QS.Dict, (QS.Dict, (QS.Dict, (QS.Dict, ())))))) ->
               P.return QS.Dict) ::
              (QS.Dict (QC.Arbitrary QS.A),
               (QS.Dict (QC.CoArbitrary QS.A),
                (QS.Dict (T.Typeable QS.A),
                 (QS.Dict (QC.Arbitrary QS.B),
                  (QS.Dict (QC.CoArbitrary QS.B),
                   (QS.Dict (T.Typeable QS.B), ())))))) ->
                QC.Gen
                  (QS.Dict
                     (QC.Arbitrary QS.A, QC.CoArbitrary QS.A, T.Typeable QS.A,
                      QC.Arbitrary QS.B, QC.CoArbitrary QS.B, T.Typeable QS.B))),
         QS.baseType (P.undefined :: R.Rational),
         QS.inst ((QS.Sub QS.Dict) :: () QS.:- (F.Enumerable P.Int)),
         QS.inst ((QS.Sub QS.Dict) :: () QS.:- (T.Typeable P.Int)),
         QS.inst ((QS.Sub QS.Dict) :: () QS.:- (QC.CoArbitrary P.Int)),
         QS.inst
           ((QS.Sub QS.Dict) :: (P.Ord QS.A) QS.:- (P.Ord (Stream QS.A))),
         QS.inst
           ((QS.Sub QS.Dict) ::
              (F.Enumerable QS.A) QS.:- (F.Enumerable (Stream QS.A))),
         QS.inst
           ((QS.Sub QS.Dict) ::
              (QC.CoArbitrary QS.A) QS.:- (QC.CoArbitrary (Stream QS.A))),
         QS.inst
           ((QS.Sub QS.Dict) ::
              (T.Typeable QS.A) QS.:- (T.Typeable (Stream QS.A))),
         QS.inst2
           ((QS.Sub QS.Dict) ::
              (T.Typeable QS.A, QC.Arbitrary QS.A) QS.:-
                (QC.Arbitrary (Stream QS.A))),
         QS.makeInstance
           ((\ (QS.Dict, QS.Dict) ->
               QS.observe (Tip.Haskell.Observers.mkObserve obsFunStream)) ::
              (QS.Dict (QC.Arbitrary QS.A), QS.Dict (P.Ord QS.A)) ->
                QS.Observe (Stream QS.A) (ObsStream QS.A))],
      QS.maxTermSize = P.Just (7),
      QS.maxTermDepth = P.Just (4),
      QS.testTimeout = P.Just (1000000)})
