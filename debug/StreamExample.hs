{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Stream_Demo(Stream, smap, siterate) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Stream a = SCons a (Stream a);

stl :: forall a. Stream a -> Stream a;
stl (SCons x1 x2) = x2;

shd :: forall a. Stream a -> a;
shd (SCons x1 x2) = x1;

smap :: forall a b. (a -> b) -> Stream a -> Stream b;
smap f xs = SCons (f (shd xs)) (smap f (stl xs));

siterate :: forall a. (a -> a) -> a -> Stream a;
siterate f x = SCons x (siterate f (f x));


}
