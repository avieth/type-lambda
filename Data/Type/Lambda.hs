{-|
Module      : Data.Type.Lambda
Description : Type level functions.
Copyright   : (c) Alexander Vieth, 2016
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Lambda where

import GHC.TypeLits
import Data.Kind
import Data.Proxy

-- | It's good to have a special kind to parameterize Lambda, so that we can
--   distinguish abstractions from fully-applied types. This way a type of kind
--
--     Lambda (LBase (s -> t -> r))
--
--   means it holds a type of kind s -> t -> r, contrasted with a type of kind
--
--     Lambda (LArrow (LBase s) (LArrow (LBase t) (LBase r)))
--
--   which is the lifted kind of the type s -> (t -> r)
data LambdaType where
    LBase :: s -> LambdaType
    LArrow :: LambdaType -> LambdaType -> LambdaType

type Ty = 'LBase
infixr 0 :->
type (:->) = 'LArrow

data Lambda (t :: LambdaType) where
    -- Type annotation.
    LAnn :: Lambda t -> Proxy t -> Lambda t
    -- Type constructor (includes 0-arity type constructors like 'True).
    LCon :: t -> Lambda ('LBase t)
    -- Type constructor application.
    LCap :: Lambda (LBase (s -> t)) -> Lambda (LBase s) -> Lambda (LBase t)
    -- Named variable.
    LVar :: Proxy (name :: Symbol) -> Lambda t
    -- Lambda abstraction. Note the type variable @s@ which appears only in the
    -- rightmost part. It can be constrained by using 'LAnn.
    LAbs :: Proxy (name :: Symbol) -> Lambda t -> Lambda (LArrow s t)
    -- Lambda application. Contrast with LCap, which does application within
    -- the arrow kind.
    LApp :: Lambda (LArrow s t) -> Lambda s -> Lambda t
    -- Let bindings (recursive).
    LLet :: Proxy (name :: Symbol) -> Lambda t -> Lambda u -> Lambda u
    -- Embedding of type families.
    -- Since type families are not types, we proxy them with actual types.
    -- A saturated type family proxy must have kind Type. An unsaturated proxy
    -- embedded here in Lambda may have any kind as its rightmost kind.
    -- Do not use this constructor directly; instead, use @F@, which by way
    -- of @LFamType@ computes the proper type parameter.
    LFam :: (Lambda s -> t) -> Lambda ('LArrow s u)
    -- Analyse (pattern matching).
    LYse :: Patterns against body -> Lambda ('LBase against) -> Lambda body

infixl 0 :@
type x :@ y = 'LCap x y
infixl 9 :$
type x :$ y = 'LApp x y
infixr 0 :$:
type x :$: y = 'LApp x y
type x ::: y = 'LAnn x y
type L (x :: Symbol) y = 'LAbs ('Proxy :: Proxy x) y
type V (x :: Symbol) = 'LVar ('Proxy :: Proxy x)

type family LFamType (l :: Type) :: LambdaType where
    LFamType (Proxy (t :: LambdaType) -> Type) = t
    LFamType (Lambda t -> r) = 'LArrow t (LFamType r)

type family F (l :: Lambda s -> t) :: Lambda ('LArrow s (LFamType t)) where
    F l = 'LFam l

type family EvalFamily (d :: Proxy (t :: LambdaType) -> Type) :: Lambda t

data Times (m :: Lambda (Ty Nat)) (n :: Lambda (Ty Nat)) (pl :: Proxy (Ty Nat))
type instance EvalFamily (Times lm ln) = 'LCon ((RunLambda lm) GHC.TypeLits.* (RunLambda ln))

data Plus (m :: Lambda (Ty Nat)) (n :: Lambda (Ty Nat)) (pl :: Proxy (Ty Nat))
type instance EvalFamily (Plus lm ln) = 'LCon ((RunLambda lm) GHC.TypeLits.+ (RunLambda ln))

data FmapProxy (g :: Lambda (s :-> t)) (x :: Lambda (Ty (f (Lambda s)))) (px :: Proxy (Ty (f (Lambda t))))
type instance EvalFamily (FmapProxy g x) = FmapInstance g (RunLambda x)
type f :<$> x = F FmapProxy :$ f :$ x

-- Notice that the second parameter is stripped of the outer lambda, so that the
-- family can match directly.
type family FmapInstance (g :: Lambda (s :-> t)) (x :: f (Lambda s)) :: Lambda (Ty (f (Lambda t)))

type instance FmapInstance g 'Nothing = 'LCon 'Nothing
type instance FmapInstance g ('Just x) = 'LCon ('Just (g :$ x))

type instance FmapInstance g ('Left x) = 'LCon ('Left x)
type instance FmapInstance g ('Right x) = 'LCon ('Right (g :$ x))

type instance FmapInstance g '[] = 'LCon '[]
type instance FmapInstance g (x ': xs) =
    'LCon ((g :$ x) ': RunLambda (FmapInstance g xs))

data SemigroupAp (pt :: Proxy t) (l :: Lambda (Ty t)) (r :: Lambda (Ty t)) (pr :: Proxy (Ty t))
type instance EvalFamily (SemigroupAp pt l r) =
    'LCon (SemigroupApInstance (RunLambda l) (RunLambda r))

type family SemigroupApInstance (l :: k) (r :: k) :: k

data And where
    And :: Bool -> And
type instance SemigroupApInstance ('And 'True) ('And b) = 'And b
type instance SemigroupApInstance ('And 'False) ('And b) = 'And 'False

type Ex = F (SemigroupAp 'Proxy) :$ 'LCon ('And 'True) :$ 'LCon ('And 'True)

data FoldrProxy (f :: Lambda (Ty a :-> Ty b :-> Ty b)) (e :: Lambda (Ty b)) (xs :: Lambda (Ty [a])) (p :: Proxy (Ty b))
type instance EvalFamily (FoldrProxy f e xs) = FoldrInstance f (RunLambda e) (RunLambda xs)
type family FoldrInstance (f :: Lambda (Ty a :-> Ty b :-> Ty b)) (e :: b) (xs :: [a]) :: Lambda (Ty b)
type instance FoldrInstance f e '[] = 'LCon e
type instance FoldrInstance f e (x ': xs) = f :$ 'LCon x :$ (FoldrInstance f e xs)
type Foldr = F FoldrProxy

data ApProxy (mf :: Lambda (Ty (f (Lambda (a :-> b))))) (mx :: Lambda (Ty (f (Lambda a)))) (p :: Proxy (Ty (f (Lambda b))))
type instance EvalFamily (ApProxy mf mx) = ApInstance (RunLambda mf) (RunLambda mx)
type family ApInstance (mf :: f (Lambda (a :-> b))) (mx :: f (Lambda a)) :: Lambda (Ty (f (Lambda b)))
type instance ApInstance 'Nothing 'Nothing = 'LCon 'Nothing
type instance ApInstance ('Just f) 'Nothing = 'LCon 'Nothing
type instance ApInstance 'Nothing ('Just f) = 'LCon 'Nothing
type instance ApInstance ('Just f) ('Just x) = 'LCon ('Just (f :$ x))
type instance ApInstance ('Left x) ('Left y) = 'LCon ('Left x)
type instance ApInstance ('Left x) ('Right y) = 'LCon ('Left x)
type instance ApInstance ('Right f) ('Left y) = 'LCon ('Left y)
type instance ApInstance ('Right f) ('Right x) = 'LCon ('Right (f :$ x))
type mf :<*> mx = F ApProxy :$ mf :$ mx

-- | Evaluation of a Lambda to normal form makes use of an environment mapping
--   names (Symbols) to Lambdas.
data BoundNames where
    BoundNamesNil :: BoundNames
    BoundNamesCons :: Proxy (name :: Symbol) -> (BoundNames, Lambda t) -> BoundNames -> BoundNames
    BoundNamesRecCons :: Proxy (name :: Symbol) -> Lambda t -> BoundNames -> BoundNames

-- | Try to resolve a name from a binding environment. If not found, give back
--   an 'LVar.
type family LookupName (name :: Symbol) (t :: LambdaType) (env :: BoundNames) :: (BoundNames, Lambda t) where
    LookupName name t env = LookupNameRec env name t env

-- | Keep the original environment around. Useful for when it gets stuck, so we
--   can see the whole input.
type family LookupNameRec (origEnv :: BoundNames) (name :: Symbol) (t :: LambdaType) (env :: BoundNames) :: (BoundNames, Lambda t) where
    LookupNameRec origEnv name t ('BoundNamesCons ('Proxy :: Proxy name) '(env, (x :: Lambda t)) rest) = '(env, x)
    LookupNameRec origEnv name t ('BoundNamesRecCons ('Proxy :: Proxy name) (x :: Lambda t) rest) =
        NormalForm ('BoundNamesRecCons ('Proxy :: Proxy name) x rest) x
    LookupNameRec origEnv name t ('BoundNamesCons ('Proxy :: Proxy name') '(env, (x :: Lambda t')) rest) =
        LookupNameRec origEnv name t rest
    LookupNameRec origEnv name t ('BoundNamesRecCons ('Proxy :: Proxy name') (x :: Lambda t') rest) =
        LookupNameRec origEnv name t rest

type family AppendBoundNames (a :: BoundNames) (b :: BoundNames) :: BoundNames where
    AppendBoundNames 'BoundNamesNil b = b
    AppendBoundNames ('BoundNamesCons proxy t rest) b =
        'BoundNamesCons proxy t (AppendBoundNames rest b)
    AppendBoundNames ('BoundNamesRecCons proxy t rest) b =
        'BoundNamesRecCons proxy t (AppendBoundNames rest b)

-- | Evaluate a Lambda to normal form.
type family NormalForm (env :: BoundNames) (l :: Lambda t) :: (BoundNames, Lambda t) where
    NormalForm env ('LAnn l proxy) = NormalForm env l
    NormalForm env ('LCon c) = '(env, 'LCon c)
    NormalForm env ('LCap left right) =
        NormalFormCap env (NormalForm env left) (NormalForm env right)
    NormalForm env ('LVar ('Proxy :: Proxy name) :: Lambda t) = LookupName name t env
    NormalForm env ('LAbs proxyName body) = '(env, 'LAbs proxyName body)
    NormalForm env ('LApp left right) =
        NormalFormApp env (NormalForm env left) (NormalForm env right)
    -- Let is recursive. We get the normal form of the rhs with a recursive
    -- binding to itself, and give a nonrecursive binding to that when
    -- computing the normal form of the body.
    NormalForm env ('LLet proxyName rhs body) =
        NormalForm ('BoundNamesCons proxyName (NormalForm ('BoundNamesRecCons proxyName rhs env) rhs) env) body
    -- Type families are in normal form, just like lambda abstractions. Only
    -- when applied to something will they be reduced.
    NormalForm env ('LFam l) = '(env, 'LFam l)
    NormalForm env ('LYse pats t) =
        NormalFormYse env pats (NormalForm env t)

-- | The normal form of an application. Takes the normal form left-hand part
--   and the normal form right-hand part.
type family NormalFormApp (env :: BoundNames) (left :: (BoundNames, Lambda (LArrow s t))) (right :: (BoundNames, Lambda s)) :: (BoundNames, Lambda t) where
    NormalFormApp env '(env', 'LAbs proxyName body) '(env'', right) =
        NormalForm ('BoundNamesCons proxyName '(env'', right) (AppendBoundNames env' env)) body
    NormalFormApp env '(env', 'LFam (l :: Lambda s -> Proxy t -> Type)) '(env'', right) =
        NormalForm env (EvalFamily (l right))
    NormalFormApp env '(env', 'LFam (l :: Lambda s -> Lambda t -> r)) '(env'', right) =
        NormalForm env ('LFam (l right))

type family NormalFormCap (env :: BoundNames) (left :: (BoundNames, Lambda (LBase (s -> t)))) (right :: (BoundNames, Lambda (LBase s))) :: (BoundNames, Lambda (LBase t)) where
    -- In order to apply right to con, we need to evaluate right to a
    -- non-Lambda. This works only if right is an 'LCon.
    NormalFormCap env '(env', 'LCon con) '(env'', right) =
        NormalForm env ('LCon (con (GetLambda right)))

type family NormalFormYse (env :: BoundNames) (pats :: Patterns s t) (l :: (BoundNames, Lambda ('LBase s))) :: (BoundNames, Lambda t) where
    NormalFormYse env ('Patterns ( '(clause, body) ': rest )) '(env', l) =
        NormalFormYseContinue env ('Patterns rest) '(env', l) (MatchClause clause (RunLambda l)) body

type family NormalFormYseContinue (env :: BoundNames) (pats :: Patterns s t) (l :: (BoundNames, Lambda ('LBase s))) (match :: Maybe BoundNames) (body :: Lambda t) :: (BoundNames, Lambda t) where
    NormalFormYseContinue env pats '(env', l) 'Nothing body =
        NormalFormYse env pats '(env', l)
    NormalFormYseContinue env pats '(env', l) ('Just env'') body =
        NormalForm (AppendBoundNames env'' env) body

-- | A normal form Lambda can sometimes be eliminated to yield a non-Lambda
--   type.
type family GetLambda (l :: Lambda (LBase s)) :: s where
    GetLambda ('LCon c) = c

type family RunLambda (l :: Lambda (LBase s)) :: s where
    RunLambda l = GetLambda (DropEnv (NormalForm 'BoundNamesNil l))

type family DropEnv (t :: (BoundNames, l)) :: l where
    DropEnv '(env, l) = l

type Id (pk :: Proxy k) =
    (L "x" (V "x")) ::: ('Proxy :: Proxy (Ty k :-> Ty k))

-- Const is weird. We have it as Lambda (k -> l -> k) but shouldn't it be
-- Lambda (k -> Lambda (l -> k)) ???
type Const (pk :: Proxy k) (pl :: Proxy l) =
    (L "x" (L "y" (V "x"))) ::: ('Proxy :: Proxy (Ty k :-> Ty l :-> Ty k))

-- |
-- == Pattern matching on types of algebraic kinds.
--
--   If we define a (generalized) algebraic datatype, of course we can pattern
--   match on terms thereof. But what about the promoted types? There is no
--   pattern matching construct at the type level, but we can hack one up.
--
--   

data Patterns (against :: Type) (body :: LambdaType) where
    Patterns :: [(PatternClause against, Lambda body)] -> Patterns against body

-- | This GADT is formed in such a way that a poly-kinded type constructor will
--   be specialized according to the kinds which compose a @PatternBindings@
--   type.
data PatternClause (against :: Type) where
    PatternClause
        :: Proxy rightmost
        -> constructor
        -> PatternBindings constructor rightmost
        -> PatternClause rightmost

-- | Describes the arguments of a constructor. The first parameter is a
--   type with as many arrows as there are @PatternBindingsCons@'s in the
--   term, and the second parameter is the type that the first parameter will
--   have when it is saturated with arguments.
--   Each @PatternBindingsCons@ indicates the type (kind) expected and also
--   names it using a @Symbol@.
data PatternBindings (constructor :: Type) (rightmost :: Type) where
    PatternBindingsNil :: PatternBindings rightmost rightmost
    PatternBindingsCons
        :: Symbol
        -> Proxy t
        -> PatternBindings l r
        -> PatternBindings (t -> l) r

-- | Describes a match of a @PatternBindings@ against a type, and holds the
--   actual types that were found.
data PatternMatch (args :: [(Symbol, Type)]) (rightmost :: Type) where
    PatternMatchNil :: PatternMatch '[] rightmost
    PatternMatchCons
        :: Proxy (name :: Symbol)
        -> t
        -> PatternMatch ts (t -> r)
        -> PatternMatch ( '(name, t) ': ts ) r

type family PatternMatchConsMaybe (n :: Symbol) (t :: Type) (k :: t) (pm :: Maybe (PatternMatch ts (t -> r))) :: Maybe (PatternMatch ( '(n, t) ': ts) r ) where
    PatternMatchConsMaybe n t k 'Nothing = 'Nothing
    PatternMatchConsMaybe n t k ('Just rest) = 'Just ('PatternMatchCons 'Proxy k rest)

-- | Here's where we match: give the names and argument types in reverse
--   argument order, and then the rightmost kind and something of that kind.
--   If you get @'Just@, then the @PatternMatch@ type contains the actual
--   types found in the type called @rightmost@, and their associated names as
--   determined by the names list.
type family MatchAgainst (args :: [(Symbol, Type)]) (constructor :: k) (rightmost :: Type) (t :: rightmost) :: Maybe (PatternMatch args rightmost) where
    MatchAgainst ( '(n, k) ': ks ) constructor l ((q :: k -> l) (x :: k)) =
        PatternMatchConsMaybe n k x (MatchAgainst ks constructor (k -> l) q)
    MatchAgainst '[] q l (q :: l) = 'Just 'PatternMatchNil
    MatchAgainst a b c d = 'Nothing

-- | Convert a @PatternBindings@ into a list suitable for use as the first
--   parameter to @MatchAgainst@.
type family PatternBindingsForm (p :: PatternBindings constructor rightmost) :: [(Symbol, Type)] where
    PatternBindingsForm 'PatternBindingsNil = '[]
    PatternBindingsForm ('PatternBindingsCons sym ('Proxy :: Proxy t) rest) =
        Snoc '(sym, t) (PatternBindingsForm rest)

type family Snoc (t :: k) (ts :: [k]) :: [k] where
    Snoc t '[] = '[t]
    Snoc t (s ': ss) = s ': Snoc t ss

-- | BoundNames is just a PatternMatch without type information. This family
--   shows how.
type family PatternMatchToBoundNames (pm :: PatternMatch args rightmost) :: BoundNames where
    PatternMatchToBoundNames 'PatternMatchNil = 'BoundNamesNil
    PatternMatchToBoundNames ('PatternMatchCons proxyName t rest) =
        'BoundNamesCons proxyName '( 'BoundNamesNil, 'LCon t ) (PatternMatchToBoundNames rest)

type family PatternMatchToBoundNamesMaybe (pm :: Maybe (PatternMatch args rightmost)) :: Maybe BoundNames where
    PatternMatchToBoundNamesMaybe 'Nothing = 'Nothing
    PatternMatchToBoundNamesMaybe ('Just pm) = 'Just (PatternMatchToBoundNames pm)

type family MatchClause (pc :: PatternClause against) (t :: against) :: Maybe BoundNames where
    MatchClause ('PatternClause (proxy :: Proxy k) constructor pbindings) t =
        PatternMatchToBoundNamesMaybe (MatchAgainst (PatternBindingsForm pbindings) constructor k t)

type IsJust (p :: Proxy t) = 
    (L "x" (
    'LYse ('Patterns '[
            '( 'PatternClause ('Proxy :: Proxy (Maybe t)) 'Just ('PatternBindingsCons "x" ('Proxy :: Proxy t) 'PatternBindingsNil), 'LCon 'True)
          , '( 'PatternClause ('Proxy :: Proxy (Maybe t)) 'Nothing 'PatternBindingsNil, 'LCon 'False)
          ])
          (V "x")
    ))
    ::: ('Proxy :: Proxy (Ty (Maybe t) :-> Ty Bool))

type BoolNot =
    L "x" (
    'LYse ('Patterns '[
            '( 'PatternClause 'Proxy 'True 'PatternBindingsNil, 'LCon 'False )
          , '( 'PatternClause 'Proxy 'False 'PatternBindingsNil, 'LCon 'True )
          ])
          (V "x")
    )
    :::
    ('Proxy :: Proxy (Ty Bool :-> Ty Bool))

type BoolAnd =
    L "x" (
    L "y" (
    ('LYse ('Patterns '[
             '( 'PatternClause 'Proxy 'True 'PatternBindingsNil, V "y")
           , '( 'PatternClause 'Proxy 'False 'PatternBindingsNil, 'LCon 'False )
           ])
          (V "x")
    )))
    :::
    ('Proxy :: Proxy (Ty Bool :-> Ty Bool :-> Ty Bool))

type Dot (ps :: Proxy s) (pt :: Proxy t) (pu :: Proxy u) =
    L "g" (
    L "f" (
    L "x" (
    ((V "g") ::: ('Proxy :: Proxy (t :-> u))) :$ (
    ((V "f") ::: ('Proxy :: Proxy (s :-> t))) :$ (
    ((V "x") ::: ('Proxy :: Proxy s)))))))
    :::
    ('Proxy :: Proxy ((t :-> u) :-> (s :-> t) :-> (s :-> u)))

infixr 9 :.
type g :. f = Dot 'Proxy 'Proxy 'Proxy :$ g :$ f

data List t where
    Nil :: List t
    Cons :: t -> List t -> List t

-- Safe list head
-- Here it seems the kind proxying is necessary.
type SafeHead (pt :: Proxy t) =
    L "xs" (
    'LYse ('Patterns '[
            '( 'PatternClause 'Proxy 'Nil 'PatternBindingsNil, 'LCon 'Nothing )
          , '( 'PatternClause 'Proxy 'Cons ('PatternBindingsCons "x" ('Proxy :: Proxy t) ('PatternBindingsCons "xs" ('Proxy :: Proxy (List t)) 'PatternBindingsNil))
          , 'LCon 'Just :@ V "x")
          ])
          (V "xs")
    )
    :::
    ('Proxy :: Proxy (Ty (List t) :-> Ty (Maybe t)))

-- List length
type Length (pt :: Proxy t) =
    'LLet ('Proxy :: Proxy "length") 
          ((L "xs" (
          'LYse ('Patterns '[
                  '( 'PatternClause 'Proxy 'Nil 'PatternBindingsNil, 'LCon 0 )
                , '( 'PatternClause 'Proxy 'Cons ('PatternBindingsCons "x" ('Proxy :: Proxy t) ('PatternBindingsCons "xs'" ('Proxy :: Proxy (List t)) 'PatternBindingsNil))
                   , F Plus :$ 'LCon 1 :$ ((V "length" ::: ('Proxy :: Proxy (Ty (List t) :-> Ty Nat))) :$ (V "xs'" ::: ('Proxy :: Proxy (Ty (List t)))))
                   )
                ])
                (V "xs" ::: ('Proxy :: Proxy (Ty (List t))))
          ))
          ::: ('Proxy :: Proxy (Ty (List t) :-> Ty Nat)))
          (V "length" ::: ('Proxy :: Proxy (Ty (List t) :-> (Ty Nat))))
    ::: ('Proxy :: Proxy (Ty (List t) :-> Ty Nat))
