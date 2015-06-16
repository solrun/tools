{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
module Tip.Utils.Specialiser (specialise, Rule(..), Expr(..), Void, absurd, Closed, subtermRules, subterms, Subst, Inst) where

import Tip.Fresh
import Tip.Utils
import Tip.Pretty

import Control.Monad
import Data.Maybe
import Data.List
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Text.PrettyPrint

data Void = Void !Void
  deriving (Eq,Ord,Show)

instance Pretty Void where
  pp = absurd

absurd :: Void -> a
absurd (Void v) = absurd v

data Rule c a = Rule
  { rule_pre  :: Expr c a
  -- ^ The trigger. All the variables present here...
  , rule_post :: Expr c a
  -- ^ ...must be present in this activated expression
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance (Pretty c,Pretty a) => Pretty (Rule c a) where
  pp (Rule p q) = pp p <+> "=>" $\ pp q

subtermRules :: Rule c a -> [Rule c a]
subtermRules (Rule p q) = map (Rule p) (subterms q)

subterms :: Expr c a -> [Expr c a]
subterms e = e : case e of Var a    -> []
                           Con _ es -> concatMap subterms es

mapRuleCtx :: (c -> c') -> Rule c a -> Rule c' a
mapRuleCtx c = bimapRule c id

mapExprCtx :: (c -> c') -> Expr c a -> Expr c' a
mapExprCtx c = bimapExpr c id

bimapRule :: (c -> c') -> (a -> a') -> Rule c a -> Rule c' a'
bimapRule c a (Rule p q) = Rule (bimapExpr c a p) (bimapExpr c a q)

bimapExpr :: (c -> c') -> (a -> a') -> Expr c a -> Expr c' a'
bimapExpr _ a (Var x) = Var (a x)
bimapExpr c a (Con k es) = Con (c k) (map (bimapExpr c a) es)

unSkolem :: Closed (Sk c) -> Expr c Int
unSkolem (Con (Old k) es) = Con k (map unSkolem es)
unSkolem (Con (Sk i) [])  = Var i

ruleVars :: Ord a => Rule c a -> [a]
ruleVars (Rule p q) = usort $ concatMap go [p,q]
  where
  go (Var x) = [x]
  go (Con c es) = concatMap go es

data Expr c a = Var a | Con c [Expr c a]
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance (Pretty c,Pretty a) => Pretty (Expr c a) where
  pp (Var x)    = pp x
  pp (Con k es) = parens (pp k <+> fsep (map pp es))

type Closed c = Expr c Void

data Sk c = Old c | Sk Int
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance Pretty c => Pretty (Sk c) where
  pp (Old c) = pp c
  pp (Sk i)  = int i

instance Ord c => Name (Sk c) where
  fresh = Sk <$> fresh

instance PrettyVar (Sk c) where
  varStr _ = show ""

varOf :: Eq a => a -> Expr c a -> Bool
x `varOf` Var y        = x == y
x `varOf` Con _ es = any (x `varOf`) es

specialise :: forall d c a . (Ord d,Ord c,Ord a) =>
    [(d,[Rule c a])] -> [Closed c] -> ([(d,Subst a Void c)],[d])
specialise decl_rules seeds = (which (usort (go seeds)), scary)
  where
  free0,free,scary :: [d]
  (usort -> free0,usort -> scary) = separate [ (d,r) | (d,rs) <- decl_rules, r <- rs ]
  free = free0 \\ scary

  named_rules :: [(d,Rule c a)]
  named_rules = [ (d,r) | (d,rules) <- decl_rules, d `elem` free, r <- rules ]

  go :: [Closed c] -> [Closed c]
  go insts
    | null (new_insts \\ insts) = []
    | otherwise                 = new_insts `union` go (new_insts `union` insts)
    where
    new_insts = usort $ map (snd . snd) new
    new = step named_rules insts

  which :: [Closed c] -> [(d,Subst a Void c)]
  which cls = usort [ (d,i) | (d,(i,_)) <- step named_rules cls ]

-- Return the safe rules, and the scary rules
separate :: (Ord a,Ord c) => [(name,Rule c a)] -> ([name],[name])
separate = go []
  where
  go rs ((n,r):xs)
    | isJust (terminating (r:rs)) = let (a,b) = go (r:rs) xs in (n:a,b  )
    | otherwise                   = let (a,b) = go rs     xs in (  a,n:b)
  go _ _ = ([],[])

cyclic :: (Ord a,Ord c) => Expr c a -> Expr c a -> Bool
cyclic e1 e2 | Just m0 <- match e1 e2
             = or [ x `varOf` e | (x,e) <- m0, e /= Var x ]
cyclic _  _  = False

terminating :: forall a c . (Ord a,Ord c) => [Rule c a] -> Maybe [Closed (Sk c)]
terminating (map (mapRuleCtx Old) -> rs) = go [] (inst rs)
  where
  go :: [Closed (Sk c)] -> [Closed (Sk c)] -> Maybe [Closed (Sk c)]
  go old []  = Just old
  go old new | or [ cyclic (unSkolem o) (unSkolem n) | o <- old, n <- new ] = Nothing
  go old new = let both = old `union` new in go both (unnamedStep rs new \\ both)

inst :: (Ord a,Ord c) => [Rule (Sk c) a] -> [Closed (Sk c)]
inst = runFresh . mapM instPre

instPre :: (Ord a,Ord c) => Rule (Sk c) a -> Fresh (Closed (Sk c))
instPre r =
  do su <- sequence [ (,) v . (`Con` []) <$> fresh | v <- ruleVars r ]
     return (close su (rule_pre r))

close :: Eq a => [(a,Closed c)] -> Expr c a -> Closed c
close su (Var v)    = fromMaybe (error "close") (lookup v su)
close su (Con c es) = Con c (map (close su) es)

unnamedStep :: (Ord c,Ord a) => [Rule c a] -> [Closed c] -> [Closed c]
unnamedStep rs = usort . map (snd . snd) . step (map ((,) ()) rs)

step :: (Ord name,Ord c,Ord a) => [(name,Rule c a)] -> [Closed c] -> [(name,Inst a c)]
step rs = usort . concatMap (activateAll rs)

activateAll :: (Ord c,Ord a) => [(name,Rule c a)] -> Closed c -> [(name,Inst a c)]
activateAll rs c = [ (name,c') | (name,rul) <- rs, Just c' <- [activateOne rul c] ]

type Inst a c = (Subst a Void c,Closed c)

activateOne :: (Ord c,Ord a) => Rule c a -> Closed c -> Maybe (Inst a c)
activateOne r@(Rule p q) e
  = fmap (\ su -> (su, close su q)) (match p e)

type Subst a b c = [(a,Expr c b)]

merge :: (Ord a,Ord b,Ord c) => Subst a b c -> Subst a b c -> Maybe (Subst a b c)
merge xs ys =
  do guard (and [ maybe True (e ==) (lookup v ys) | (v,e) <- xs ])
     Just (unionOn fst xs ys)

merges :: (Ord a,Ord b,Ord c) => [Subst a b c] -> Maybe (Subst a b c)
merges = foldM merge []

match :: (Ord a,Ord b,Ord c) => Expr c a -> Expr c b -> Maybe (Subst a b c)
match (Var x) e = Just [(x,e)]
match (Con c xs) (Con d ys)
  | c == d
  , length xs == length ys
  = merges =<< zipWithM match xs ys
match _ _ = Nothing

test_rules = [("list",testList),("mdef",test1),("f_ok",test2),("f_bad",test3),("fg",test4)]

test_seeds = [Con "map" [Con "A" [],Con "B" []]
             ,Con "f" [Con "X" []]
             ]

testList =
  [ Rule (Con "cons" [Var "a"]) (Con "nil" [Var "a"])
  , Rule (Con "nil" [Var "a"])  (Con "cons" [Var "a"])
  ]

test1 =
  [ Rule (Con "map" [Var "a",Var "b"]) (Con "cons" [Var "a"])
  , Rule (Con "map" [Var "a",Var "b"]) (Con "cons" [Var "b"])
  , Rule (Con "map" [Var "a",Var "b"]) (Con "nil" [Var "a"])
  , Rule (Con "map" [Var "a",Var "b"]) (Con "nil" [Var "b"])
  , Rule (Con "map" [Var "a",Var "b"]) (Con "map" [Var "a",Var "b"])
  ]

test2 =
  [ Rule (Con "f" [Var "a"]) (Con "f" [Var "a"])
  ]

test3 =
  [ Rule (Con "f" [Var "a"]) (Con "f" [Con "f'" [Var "a"]])
  ]

test4 =
  [ Rule (Con "f" [Var "a"]) (Con "g" [Con "g'" [Var "a"]])
  , Rule (Con "g" [Var "b"]) (Con "f" [Var "b"])
  ]
