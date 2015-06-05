{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
module Tip.Haskell.Translate where

#include "errors.h"
import Tip.Haskell.Repr as H
import Tip.Core as T hiding (Formula(..),globals,Type(..))
import Tip.Core (Type((:=>:),BuiltinType))
import qualified Tip.Core as T
import Tip.Pretty
import Tip.Utils
import Tip.Scope

import Tip.CallGraph

import Control.Monad

import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import qualified Data.Map as M

import Data.Generics.Geniplate

import Data.List (nub,partition)

prelude :: String -> HsId a
prelude = Qualified "Prelude" (Just "P")

tipDSL :: String -> HsId a
tipDSL = Qualified "Tip" Nothing

quickCheck :: String -> HsId a
quickCheck = Qualified "Test.QuickCheck" (Just "QC")

quickCheckUnsafe :: String -> HsId a
quickCheckUnsafe = Qualified "Test.QuickCheck.Gen.Unsafe" (Just "QU")

quickCheckAll :: String -> HsId a
quickCheckAll = Qualified "Test.QuickCheck.All" (Just "QC")

quickSpec :: String -> HsId a
quickSpec = Qualified "QuickSpec" (Just "QS")

feat :: String -> HsId a
feat = Qualified "Test.Feat" (Just "F")

typeable :: String -> HsId a
typeable = Qualified "Data.Typeable" (Just "T")

data HsId a
    = Qualified
         { qual_module       :: String
         , qual_module_short :: Maybe String
         , qual_func         :: String
         }
    -- ^ A qualified import
    | Exact String
    -- ^ The current module defines something with this very important name
    | Other a
    -- ^ From the theory
    | Derived (HsId a) String
    -- ^ For various purposes...
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

instance PrettyVar a => PrettyVar (HsId a) where
  varStr (Qualified _ (Just m) s) = m ++ "." ++ s
  varStr (Qualified m Nothing  s) = m ++ "." ++ s
  varStr (Exact s) = s
  varStr (Other x) = varStr x
  varStr (Derived o s) = s ++ varStr o

addHeader :: Decls a -> Decls a
addHeader (Decls ds) =
    Decls (map LANGUAGE ["TemplateHaskell","DeriveDataTypeable","TypeOperators","ImplicitParams","RankNTypes"] ++ Module "A" : ds)

addImports :: Ord a => Decls (HsId a) -> Decls (HsId a)
addImports d@(Decls ds) = Decls (QualImport "Text.Show.Functions" Nothing : imps ++ ds)
  where
  imps = usort [ QualImport m short | Qualified m short _ <- F.toList d ]

trTheory :: (Ord a,PrettyVar a) => Theory a -> Decls (HsId a)
trTheory = trTheory' . fmap Other

data Kind = Expr | Formula deriving Eq

theorySigs :: Theory (HsId a) -> [HsId a]
theorySigs Theory{..} = map sig_name thy_sigs

ufInfo :: Theory (HsId a) -> (Bool,[H.Type (HsId a)])
ufInfo Theory{thy_sigs} = (not (null imps),imps)
  where
  imps = [TyImp (Derived f "imp") (H.TyCon (Derived f "") []) | Signature f _ <- thy_sigs]

trTheory' :: forall a b . (a ~ HsId b,Ord b,PrettyVar b) => Theory a -> Decls a
trTheory' thy@Theory{..} =
  Decls $
    concatMap tr_datatype thy_datatypes ++
    map tr_sort thy_sorts ++
    concatMap tr_sig thy_sigs ++
    concatMap tr_func thy_funcs ++
    tr_asserts thy_asserts ++
    [makeSig thy]
  where
  (translate_UFs,imps) = ufInfo thy

  tr_datatype :: Datatype a -> [Decl a]
  tr_datatype (Datatype tc tvs cons) =
    [ DataDecl tc tvs
        [ (c,map (trType . snd) args) | Constructor c _ args <- cons ]
        (map prelude ["Eq","Ord","Show"] ++ [typeable "Typeable"])
    , TH (Apply (feat "deriveEnumerable") [QuoteTyCon tc])
    , InstDecl [H.TyCon (feat "Enumerable") [H.TyVar a] | a <- tvs]
               (H.TyCon (quickCheck "Arbitrary") [H.TyCon tc (map H.TyVar tvs)])
               [funDecl
                  (quickCheck "arbitrary") []
                  (Apply (quickCheck "sized") [Apply (feat "uniform") []])]
    ]

  tr_sort :: Sort a -> Decl a
  tr_sort (Sort _ i) | i /= 0 = error "Higher-kinded abstract sort"
  tr_sort (Sort s i) = TypeDef (TyCon s []) (TyCon (prelude "Int") [])

  tr_sig :: Signature a -> [Decl a]
  tr_sig (Signature f pt) =
    -- newtype f_NT = f_Mk (forall tvs . (Arbitrary a, CoArbitrary a) => T)
    [ DataDecl (Derived f "") [] [ (Derived f "Mk",[tr_polyTypeArbitrary pt]) ] []
    , FunDecl (Derived f "get")
       [( [H.ConPat (Derived f "Mk") [VarPat (Derived f "x")]]
        , var (Derived f "x")
        )]

    -- f :: (?f_imp :: f_NT) => T
    -- f = f_get ?f_imp
    , TySig f [] (tr_polyType pt)
    , funDecl f [] (Apply (Derived f "get") [ImpVar (Derived f "imp")])

    -- instance Arbitrary f_NT where
    --   arbitrary = do
    --      Capture x <- capture
    --      return (f_Mk (x arbitrary))
    , InstDecl [] (TyCon (quickCheck "Arbitrary") [TyCon (Derived f "") []])
        [ funDecl (quickCheck "arbitrary") []
          (mkDo [Bind (Derived f "x") (Apply (quickCheckUnsafe "capture") [])]
                (H.Case (var (Derived f "x"))
                   [(H.ConPat (quickCheckUnsafe "Capture") [VarPat (Derived f "y")]
                    ,Apply (prelude "return")
                    [Apply (Derived f "Mk")
                    [Apply (Derived f "y")
                    [Apply (quickCheck "arbitrary") []]]]
                    )]
                )
          )
        ]

    -- gen :: Gen (Dict (?f_imp :: f_NT))
    -- gen = do
    --   x <- arbitrary
    --   let ?f_imp = x
    --   return Dict
    , TySig (Derived f "gen") []
        (TyCon (quickCheck "Gen")
          [TyCon (quickSpec "Dict")
            [TyImp (Derived f "imp") (TyCon (Derived f "") [])]])
    , funDecl (Derived f "gen") []
        (mkDo [Bind (Derived f "x") (Apply (quickCheck "arbitrary") [])]
              (ImpLet (Derived f "imp") (var (Derived f "x"))
                (Apply (prelude "return") [Apply (quickSpec "Dict") []])))
    ]

  tr_func :: Function a -> [Decl a]
  tr_func fn@Function{..} =
    [ TySig func_name [] (tr_polyType (funcType fn))
    , FunDecl
        func_name
        [ (map tr_deepPattern dps,tr_expr Expr rhs)
        | (dps,rhs) <- patternMatchingView func_args func_body
        ]
    ]

  tr_asserts :: [T.Formula a] -> [Decl a]
  tr_asserts fms =
    let (names,decls) = unzip (zipWith tr_assert [1..] fms)
    in  decls {- ++
          [ TH (Apply (prelude "return") [List []])
          , funDecl (Exact "main") []
              (mkDo [ Stmt (THSplice (Apply (quickCheckAll "polyQuickCheck")
                                            [QuoteName name]))
                    | name <- names ]
                    Noop)
          ] -}

  tr_assert :: Int -> T.Formula a -> (a,Decl a)
  tr_assert i (T.Formula r _ b) =
    (prop_name,funDecl prop_name args (assume (tr_expr Formula body)))
    where
    prop_name | i == 1    = Exact "prop"
              | otherwise = Exact ("prop" ++ show i)
    (args,body) =
      case b of
        Quant _ Forall lcls term -> (map lcl_name lcls,term)
        _                        -> ([],b)

    assume e =
      case r of
        Prove  -> e
        Assert -> Apply (tipDSL "assume") [e]

  tr_deepPattern :: DeepPattern a -> H.Pat a
  tr_deepPattern (DeepConPat Global{..} dps) = H.ConPat gbl_name (map tr_deepPattern dps)
  tr_deepPattern (DeepVarPat Local{..})      = VarPat lcl_name
  tr_deepPattern (DeepLitPat (T.Int i))      = IntPat i
  tr_deepPattern (DeepLitPat (Bool b))       = withBool H.ConPat b

  tr_pattern :: T.Pattern a -> H.Pat a
  tr_pattern Default = WildPat
  tr_pattern (T.ConPat Global{..} xs) = H.ConPat gbl_name (map (VarPat . lcl_name) xs)
  tr_pattern (T.LitPat (T.Int i))     = H.IntPat i
  tr_pattern (T.LitPat (Bool b))      = withBool H.ConPat b

  tr_expr :: Kind -> T.Expr a -> H.Expr a
  tr_expr k e0 =
    case e0 of
      Builtin (Lit (T.Int i)) :@: [] -> H.Int i
      Builtin (Lit (Bool b)) :@: []  -> withBool Apply b
      hd :@: es -> let (f,k') = tr_head k hd
                   in Apply f (map (tr_expr k') es)
      Lcl x -> var (lcl_name x)
      T.Lam xs b  -> H.Lam (map (VarPat . lcl_name) xs) (tr_expr Expr b)
      Match e alts -> H.Case (tr_expr Expr e) [ (tr_pattern p,tr_expr Expr rhs) | T.Case p rhs <- default_last alts ]
      T.Let x e b -> H.Let (lcl_name x) (tr_expr Expr e) (tr_expr k b)
      T.Quant _ q xs b ->
        foldr
          (\ x e ->
              Apply (tipDSL (case q of Forall -> "forAll"; Exists -> "exists"))
                [H.Lam [VarPat (lcl_name x)] e])
          (tr_expr Formula b)
          xs

    where
    default_last (def@(T.Case Default _):alts) = alts ++ [def]
    default_last alts = alts

  tr_head :: Kind -> T.Head a -> (a,Kind)
  tr_head k (Gbl Global{..}) = (gbl_name,Expr)
  tr_head k (Builtin b)      = tr_builtin k b

  tr_builtin :: Kind -> T.Builtin -> (a,Kind)
  tr_builtin k b =
    case b of
      At        -> (prelude "id",Expr)
      Lit{}     -> error "tr_builtin"
      And       -> case_kind ".&&."
      Or        -> case_kind ".||."
      Not       -> case_kind "neg"
      Implies   -> case_kind "==>"
      Equal     -> case_kind "==="
      Distinct  -> case_kind "=/="
      _         -> prelude_fn
    where
    Just prelude_str_ = lookup b hsBuiltins
    prelude_fn = (prelude prelude_str_,Expr)

    case_kind sf =
      case k of
        Expr    -> prelude_fn
        Formula -> (tipDSL sf,Formula)

  -- ignores the type variables
  tr_polyType_inner :: T.PolyType a -> H.Type a
  tr_polyType_inner (PolyType _ ts t) = trType (ts :=>: t)

  tr_polyType :: T.PolyType a -> H.Type a
  tr_polyType pt@(PolyType tvs _ _)
    | translate_UFs = TyForall tvs (TyCtx (arb tvs ++ imps) (tr_polyType_inner pt))
    | otherwise     = tr_polyType_inner pt

  -- translate type and add Arbitrary a, CoArbitrary a in the context for
  -- all type variables a
  tr_polyTypeArbitrary :: T.PolyType a -> H.Type a
  tr_polyTypeArbitrary pt@(PolyType tvs _ _) = TyForall tvs (TyCtx (arb tvs) (tr_polyType_inner pt))

  arb = arbitrary . map H.TyVar

arbitrary :: [H.Type (HsId a)] -> [H.Type (HsId a)]
arbitrary ts =
  [ TyCon (quickCheck tc) [t]
  | t <- ts
  , tc <- ["Arbitrary","CoArbitrary"]
  ]

trType :: (a ~ HsId b) => T.Type a -> H.Type a
trType (T.TyVar x)     = H.TyVar x
trType (T.TyCon tc ts) = H.TyCon tc (map trType ts)
trType (ts :=>: t)     = foldr TyArr (trType t) (map trType ts)
trType (BuiltinType b) = trBuiltinType b

trBuiltinType :: BuiltinType -> H.Type (HsId a)
trBuiltinType t | Just s <- lookup t hsBuiltinTys = H.TyCon (prelude s) []

withBool :: (a ~ HsId b) => (a -> [c] -> d) -> Bool -> d
withBool k b = k (prelude (show b)) []

-- * Builtins

hsBuiltinTys :: [(T.BuiltinType,String)]
hsBuiltinTys =
  [ (Integer, "Int")
  , (Boolean, "Bool")
  ]

hsBuiltins :: [(T.Builtin,String)]
hsBuiltins =
  [ (And      , "&&" )
  , (Or       , "||" )
  , (Not      , "not")
  , (Implies  , "<=" )
  , (Equal    , "==" )
  , (Distinct , "/=" )
  , (IntAdd   , "+"  )
  , (IntSub   , "-"  )
  , (IntMul   , "*"  )
  , (IntDiv   , "div")
  , (IntMod   , "mod")
  , (IntGt    , ">"  )
  , (IntGe    , ">=" )
  , (IntLt    , "<"  )
  , (IntLe    , "<=" )
  ]

typeOfBuiltin :: Builtin -> T.Type a
typeOfBuiltin b = case b of
  And      -> bbb
  Or       -> bbb
  Not      -> bb
  Implies  -> bbb
  Equal    -> iib -- TODO: equality could be used on other types than int
  Distinct -> iib -- ditto
  IntAdd   -> iii
  IntSub   -> iii
  IntMul   -> iii
  IntDiv   -> iii
  IntMod   -> iii
  IntGt    -> iib
  IntGe    -> iib
  IntLt    -> iib
  IntLe    -> iib
  _        -> __
  where
  bb  = [boolType] :=>: boolType
  bbb = [boolType,boolType] :=>: boolType
  iii = [intType,intType] :=>: intType
  iib = [intType,intType] :=>: boolType


-- * QuickSpec signatures

makeSig :: forall a . (PrettyVar a,Ord a) => Theory (HsId a) -> Decl (HsId a)
makeSig thy@Theory{..} =
  funDecl (Exact "sig") [] $
    Tup
      [ List
          [ Tup
              [ constant_decl ft
              , List $
                  if use_cg
                    then
                      [ int_lit num
                      | (members,num) <- cg `zip` [0..]
                      , f `elem` members
                      ]
                    else
                      [int_lit 0]

              ]
          | ft@(f,_) <- func_constants
          ]
      , Apply (quickSpec "signature") [] `Record`
          [ (quickSpec "constants",
               List $
                 builtin_decls ++
                 map constant_decl
                   (ctor_constants ++ builtin_constants))
          , (quickSpec "instances", List $
               [ mk_inst [] (mk_class (feat "Enumerable") (H.TyCon (prelude "Int") [])) ] ++
               [ mk_inst (map (mk_class c1) tys) (mk_class c2 (H.TyCon t tys))
               | (t,n) <- type_univ
               , (c1, c2) <- [(prelude "Ord", prelude "Ord"),
                              (feat "Enumerable", feat "Enumerable"),
                              (feat "Enumerable",quickCheck "Arbitrary")]
               , let tys = map trType (qsTvs n)
               ] ++
               [ Apply (quickSpec "makeInstance") [H.Lam [TupPat []] (Apply (Derived f "gen") [])]
               | Signature f _ <- thy_sigs
               ])
          , (quickSpec "maxTermSize", Apply (prelude "Just") [H.Int (if translate_UFs then 11 else 7)])
          , (quickSpec "testTimeout", Apply (prelude "Just") [H.Int 100000])
          ]
      ]
  where
  (translate_UFs,imps) = ufInfo thy

  use_cg = True

  int_lit x = H.Int x ::: H.TyCon (prelude "Int") []

  mk_inst ctx res =
    Apply (quickSpec ("inst" ++ concat [ show (length ctx) | length ctx >= 2 ]))
                 [ Apply (quickSpec "Sub") [Apply (quickSpec "Dict") []] :::
                   H.TyCon (quickSpec ":-") [TyTup ctx,res] ]

  mk_class c x = H.TyCon c [x]

  scp = scope thy

  cg = map (map defines) (flatCallGraph (CallGraphOpts True False) thy)

  poly_type (PolyType _ args res) = args :=>: res

  constant_decl (f,t) =
    Apply (quickSpec "constant") [H.String f,lam (Apply f []) ::: qs_type]
    where
    (pre,qs_type) = qsType t
    lam | null pre  = id
        | otherwise = H.Lam (replicate (length pre) (H.ConPat (quickSpec "Dict") []))

  int_lit_decl x =
    Apply (quickSpec "constant") [H.String (Exact (show x)),int_lit x]

  bool_lit_decl b =
    Apply (quickSpec "constant") [H.String (prelude (show b)),withBool Apply b]

  ctor_constants =
    [ (f,poly_type (globalType g))
    | (f,g@ConstructorInfo{}) <- M.toList (globals scp)
    ]

  func_constants =
    [ (f,poly_type (globalType g))
    | (f,g@FunctionInfo{}) <- M.toList (globals scp)
    ]

  type_univ =
    [ (data_name, length data_tvs)
    | (_,DatatypeInfo Datatype{..}) <- M.toList (types scp)
    ]

  -- builtins

  (builtin_lits,builtin_funs) =
    partition litBuiltin $
      usort
        [ b
        | Builtin b :@: args <- universeBi thy

        -- only count equality if argument is int:
        , let is_int = case args of
                         a1:_ -> exprType a1 == (intType :: T.Type (HsId a))
                         _    -> __
        , case b of
            Equal    -> is_int
            Distinct -> is_int
            _         -> True
        ]

  used_builtin_types :: [BuiltinType]
  used_builtin_types =
    usort [ t | BuiltinType t :: T.Type (HsId a) <- universeBi thy ]

  bool_used = Boolean `elem` used_builtin_types
  int_used  = -- Integer `elem` used_builtin_types
              or [ op `elem` builtin_funs | op <- [IntAdd,IntSub,IntMul,IntDiv,IntMod] ]

  builtin_decls
    =  [ bool_lit_decl b | bool_used, b <- [False,True] ]
    ++ [ int_lit_decl x  | int_used,  x <- [0,1] ++
                                           [ x
                                           | Lit (T.Int x) <- builtin_lits ]]

  builtin_constants
    =  [ (prelude s,typeOfBuiltin b)
       | b <- nub $
              [ b      | bool_used, b <- [And,Or,Not] ]
           -- [ IntAdd | int_used ]
           -- [ Equal  | bool_used && int_used ]
           ++ [ b | b <- builtin_funs, intBuiltin b || eqRelatedBuiltin b ]
       , Just s <- [lookup b hsBuiltins]
       ]

  qsType :: Ord a => T.Type (HsId a) -> ([H.Type (HsId a)],H.Type (HsId a))
  qsType t = (pre,foldr TyArr inner [ TyCon (quickSpec "Dict") [p] | p <- pre ])
    where
    pre | translate_UFs = arbitrary (map trType qtvs) ++ imps
        | otherwise     = []
    inner = trType (applyType tvs qtvs t)
    qtvs = qsTvs (length tvs)
    tvs = tyVars t

  qsTvs :: Int -> [T.Type (HsId a)]
  qsTvs n = take n (cycle [ T.TyCon (quickSpec qs_tv) [] | qs_tv <- ["A","B","C","D","E"] ])

theoryBuiltins :: Ord a => Theory a -> [T.Builtin]
theoryBuiltins = usort . universeBi
