# Promoting the arrow type

With the upcoming GHC 8.0 release, the `DataKinds` extension promotes GADTs,
giving us access to vastly greater numbers of even richer types and kinds.
I can confirm that this makes programming at the type level much more fun, but
it's still a bit awkward. At the term level, we work with datatype constructors
and with first-class functions, but at the type level we really only have
type constructors (promoted datatype constructors as well as the vanilla
type constructors); there's no built-in first-class type-level function. So it's
difficult to come up with even very simple functional programming motifs at the
type level, like a right-fold for instance:

```Haskell
Foldr :: (a -> b -> b) -> b -> [a] -> b
Foldr (+) 0 '[1,2,3] :: Nat
```

Wouldn't it be cool if we could do that? What's written just won't work, because
`(+)` is a type family, and type families are not types, so it just makes no
sense. But with a little bit of work, and help from GADT promotion, we can
capture the same idea but with a bit of syntactic overhead:

```Haskell
Foldr :$ F Plus :: Lambda (Ty Nat :-> Ty [Nat] :-> Ty Nat)
Foldr :$ F Plus :$ 'LCon 0 :$ 'LCon '[1,2,3] :: Lambda (Ty Nat)
RunLambda (Foldr :$ F Plus :$ 'LCon 0 :$ 'LCon '[1,2,3] :: Nat
= 6
```

We can even simulate function overloading, and give functor and applicative
"instances" to types:

```Haskell
RunLambda (F Plus :<$> 'LCon ('Just ('LCon 2)) :<*> 'LCon ('Just ('LCon 2)))
= 'Just ('LCon 2)

RunLambda (F Plus :<$> 'LCon ('Left ('LCon 1)) :<*> 'LCon ('Right ('LCon 2)))
= 'Left ('LCon 1)
```

What follows is an explanation of how this can be done.
The idea is straightforward: describe a lambda calculus as a GADT and promote
it. An [implementation](https://www.github.com/avieth/type-lambda/) is available
on github. It requires a [patch](https://phabricator.haskell.org/D1762) for GHC
bug [#11348](https://ghc.haskell.org/trac/ghc/ticket/11348) which is submitted
but awaiting review.

## The impotent arrow kind

The arrow type `(->) s t` is of course not an algebraic datatype, and so
it's not promoted by `DataKinds`, but there is ostensibly a corresponding
kind which happens to look exactly the same. The arrow *kind* describes
type constructors, but it's sparsely populated. Type constructors and promoted
data constructors are its only inhabitants, and these don't admit very many
possibilities because they can't do analysis (pattern matching) of types.
If we wish to write a type-level boolean not, for instance, our only option is
to add a new constructor to `Bool`.

Analysis of types is offered by type families, but these are in fact not types
in the arrow kind! Although GHC represents type family names in the same way
as type constructors, and GHCi will tell you that the kind of an unsaturated
type family is an arrow kind, only *saturated* type families really are types
(and that's according to GHC, not just me).

## Algebraic type-level functions

### Construction

Let's dive right in. To start, we give the definition of our own special
arrow kind. It follows the same recursive pattern as the existing arrow kind,
except that the nonrecursive case is any kind, including existing arrow kinds.

```Haskell
data LambdaType where
    LBase :: s -> LambdaType
    LArrow :: LambdaType -> LambdaType -> LambdaType

type Ty = 'LBase

infixr 0 :->
type (:->) = 'LArrow
```

Thus we have two levels of arrows: those which appear in `'LBase`, and our new
invented arrows called `'LArrow`. This really is a sane thing to do, because
when `LambdaType`s are used to parameterize our lambda calculus, we'll see
that `'LBase` picks out exactly the forms which can be "run" to produce a
type.

```Haskell
-- | A lambda calculus with primitive terms corresponding to type constructors,
data Lambda (t :: LambdaType) where
    -- Type annotation.
    LAnn :: Lambda t -> Proxy t -> Lambda t
    -- Type constructor.
    LCon :: t -> Lambda ('LBase t)
    -- Type constructor application (application within the unpromoted arrow
    -- kind).
    LCap :: Lambda ('LBase (s -> t)) -> Lamba ('LBase s) -> Lambda ('LBase t)
    -- Named variable.
    LVar :: Proxy (name :: Symbol) -> Lambda t
    -- Lambda abstraction. Note the type variable @s@ which appears only in the
    -- rightmost part. It can be constrained by using 'LAnn.
    LAbs :: Proxy (name :: Symbol) -> Lambda t -> Lambda ('LArrow s t)
    -- Lambda application.
    LApp :: Lambda ('LArrow s t) -> Lambda s -> Lambda t
    -- Let bindings.
    LLet :: Proxy (name :: Symbol) -> Lambda t -> Lambda u -> Lambda u

type x :@ y = 'LCap x y
type x :$ y = 'LApp x y
type x ::: y = 'LAnn x y
type L (x :: Symbol) y = 'LAbs ('Proxy :: Proxy x) y
type V (x :: Symbol) = 'LVar ('Proxy :: Proxy x)
```

This `Lambda t` is capable of expressing every type of arrow kind and even more!
Given any type constructor or promoted data constructor, we can wrap it in
`'LCon` to obtain the corresponding type in `Lambda t`.

```Haskell
'LCon Maybe :: Lambda ('LBase (Type -> Type))
'LCon Maybe :@ 'LCon Bool :: Lambda ('LBase Type)
'LCon 'Just :: Lambda ('LBase (a -> Maybe a))
'LCon ('Just 'True) :: Lambda ('LBase (Maybe Bool))
'LCon 'Just :@ 'LCon 'True :: Lambda ('LBase (Maybe Bool))
```

A certain class of functions--those which do not analyse their arguments--are
also in `Lambda t`, such as counterparts of term-level `id :: a -> a` and
`const :: a -> b -> a`.

```Haskell
L "x" (V "x") :: Lambda ('LArrow s t)
L "x" (L "y" (V "x")) :: Lambda ('LArrow s ('LArrow s1 t))
```

The kinds of these types are all wrong, because `'LVar` is not sensitive to the
kind of the variable which it mentions (all it carries is a symbol to identify
some other `Lambda`). To fix this, we can give a type synonym which takes a
proxy to constrain the kind of the whole term, like so:

```Haskell
type Id (pk :: Proxy k) =

    (L "x" (V "x")) ::: ('Proxy :: Proxy (Ty k :-> Ty k))

type Const (pk :: Proxy k) (pl :: Proxy l) =

    (L "x" (L "y" (V "x"))) ::: ('Proxy :: Proxy (Ty k :-> Ty l :-> Ty k))
```

When a such polymorphic function is applied to a `Lambda t` where `t` is known,
the kind of the proxy can be inferred. This reminds me of implicit parameters
in Agda or Idris.
From now forward we'll use the shorthand `Ty` and `:->` to write `LambdaType`s.

```Haskell
Id 'Proxy :@ 'LCon 'True :: Lambda Bool
Const 'Proxy 'Proxy :@ 'LCon 42 :@ 'LCon 'True :: Lambda Nat
```

It's even possible to construct higher-order functions, like this one which
applies a lifted type function to the type `'True`.

```Haskell
type ApplyToTrue =
        (L "f" (V "f" :$ 'LCon 'True))
    ::: ('Proxy :: Proxy ((Ty Bool :-> Ty Bool) :-> Ty Bool))
```

#### Embedding type families

It is possible to give a type-level pattern matching construction, and this
can be found in the [repository](https://www.github.com/avieth/type-lambda/).
But this only works on algebraic types; we can't pattern match against a `Nat`
or a `Symbol`, as these types are built-in to GHC and reveal none of their
structure. The only way to work with these kinds is via type families, so in
any case, we'll need some way to embed type families into `Lambda`.

Since an unsaturated type family is not a type, we need to come up with some
other way of identifying a type family and any arguments applied to it. The
solution used here is to define a new datatype, call it a type family proxy,
which follows a special form: every one of its parameters except for the final
is a `Lambda`, its final parameter is a `Proxy (t :: LambdaType)`, and it
constructs a `Type`. So we're looking at things like

```Haskell
data PlusProxy (m :: Lambda (Ty Nat)) (n :: Lambda (Ty Nat)) (p :: Proxy (Ty Nat))
data TimesProxy (m :: Lambda (Ty Nat)) (n :: Lambda (Ty Nat)) (p :: Proxy (Ty Nat))
data FmapProxy (g :: Lambda (s :-> t)) (x :: Lambda (Ty (f (Lambda s)))) (p :: Proxy (Ty (f (Lambda t))))
data ApProxy (mf :: Lambda (Ty (f (Lambda (a :-> b))))) (mx :: Lambda (Ty (f (Lambda a)))) (p :: Proxy (Ty (f (Lambda b))))
```

The final parameter serves to indicate the codomain of the family which the
datatype proxies. This parameter should never be filled in. The point is to use
the earlier arguments to constrain this proxied `LambdaType` so that when all
of the other parameters are given, the kind is `Proxy (t :: LambdaType) -> Type`.
We'll see how that's useful when we try to evaluate `Lambda`s.

Embedding a type family proxy into `Lambda` yields an `'LArrow`, and we apply
arguments to these proxies in the same way we apply arguments to `'LAbs`s.
Whereas `'LAbs` leaves the domain of its `'LArrow` parameter free, `'LFam`
leaves the codomain free, because we need a type family in order to compute
that kind. It can be set correctly by using the "smart constructor" `F` which
chooses the appropritate `LambdaType` based on the kind of the family proxy
datatype.

```Haskell
    -- In the GADT for Lambda.
    -- Type family embedding.
    LFam :: (Lambda s -> t) -> Lambda ('LArrow s u)

type family LFamType (l :: Type) :: LambdaType where
    LFamType (Proxy (t :: LambdaType) -> Type) = t
    LFamType (Lambda t -> r) = 'LArrow t (LFamType r)

type family F (l :: Lambda s -> t) :: Lambda ('LArrow s (LFamType t)) where
    F l = 'LFam l

F Plus :: Lambda (Ty Nat :-> Ty Nat :-> Ty Nat)
F Times :$ 'LCon 2 :: Lambda (Ty Nat :-> Ty Nat)
F Times :$ 'LCon 2 :$ 'LCon 2 :: Lambda (Ty Nat)
```

### Evaluation

With type-level functions formally expressed by `Lambda t`, it's important to
have a way to strip off the `Lambda` constructor and return to the world of
ordinary types. If we're dealing with a `Lambda (s :-> t)` then this just can't
be done, since types of this kind represent type-level functions more
general than those in the arrow kind. After all, if every `Lambda (s :-> t)`
had a corresponding type of kind `s -> t` then `Lambda` wouldn't yield any
new type level functions and this whole exercise would be trivial.

So ultimately what we're after is the following type family:

```Haskell
type family RunLambda (l :: Lambda ('LBase s)) :: s where
    RunLambda l = GetLambda (DropEnv (NormalForm 'BoundNamesNil l))

type family GetLambda (l :: Lambda (LBase s)) :: s where
    GetLambda ('LCon c) = c

type family DropEnv (t :: (BoundNames, l)) :: l where
    DropEnv '(env, l) = l

type family NormalForm (env :: BoundNames) (l :: Lambda t) :: (BoundNames, Lambda t) where
```

It accepts only `Lambda (Ty s)`, i.e. `Lambda`s which have a corresponding type,
and it's implemented by reducing the `Lambda` to a normal form, which is
always an `'LCon`, and then stripping away that constructor.

To facilitate name bindings in lambda abstractions and let clauses, we need a
kind whose types associate `Symbol`s with closures. This is called `BoundNames`:

```Haskell
data BoundNames where
    BoundNamesNil :: BoundNames
    BoundNamesCons :: Proxy (name :: Symbol) -> (BoundNames, Lambda t) -> BoundNames -> BoundNames

type family LookupName (name :: Symbol) (t :: LambdaType) (env :: BoundNames) :: (BoundNames, Lambda t) where
    LookupName name t env = LookupNameRec env name t env

-- | Keep the original environment around. Useful for when it gets stuck, so we
--   can see the whole input.
type family LookupNameRec (origEnv :: BoundNames) (name :: Symbol) (t :: LambdaType) (env :: BoundNames) :: (BoundNames, Lambda t) where
    LookupNameRec origEnv name t ('BoundNamesCons ('Proxy :: Proxy name) '(env, (x :: Lambda t)) rest) = '(env, x)
    LookupNameRec origEnv name t ('BoundNamesCons ('Proxy :: Proxy name') '(env, (x :: Lambda t')) rest) =
        LookupNameRec origEnv name t rest

type family AppendBoundNames (a :: BoundNames) (b :: BoundNames) :: BoundNames where
    AppendBoundNames 'BoundNamesNil b = b
    AppendBoundNames ('BoundNamesCons proxy t rest) b =
        'BoundNamesCons proxy t (AppendBoundNames rest b)
```

Computing the normal form is straightforward for some of the `Lambda`
constructors:

```Haskell
    -- Type annotations are removed.
    NormalForm env ('LAnn l proxy) = NormalForm env l
    -- Type constructors are in normal form.
    NormalForm env ('LCon c) = '(env, 'LCon c)
    -- Abstractions and type families are in normal form. Only when applied to
    -- something will they be reduced.
    NormalForm env ('LAbs proxyName body) = '(env, 'LAbs proxyName body)
    NormalForm env ('LFam l) = '(env, 'LFam l)
    -- Variables are resolved, and the associated Lambda is assumed to be
    -- already in normal form.
    NormalForm env ('LVar ('Proxy :: Proxy name) :: Lambda t) = LookupName name t env
```

Normal forms of the remaining constructors require more involvement from the
`BoundNames` environment.

```Haskell
    -- Type constructor application
    NormalForm env ('LCap left right) =
        NormalFormCap env (NormalForm env left) (NormalForm env right)
    NormalForm env ('LApp left right) =
        NormalFormApp env (NormalForm env left) (NormalForm env right)
    NormalForm env ('LLet proxyName rhs body) =
        NormalForm ('BoundNamesCons proxyName (NormalForm env rhs) env) body

-- | The normal form of an application. Takes the normal form left-hand part
--   and the normal form right-hand part.
type family NormalFormApp (env :: BoundNames) (left :: (BoundNames, Lambda (LArrow s t))) (right :: (BoundNames, Lambda s)) :: (BoundNames, Lambda t) where
    NormalFormApp env '(env', 'LAbs proxyName body) '(env'', right) =
        NormalForm ('BoundNamesCons proxyName '(env'', right) (AppendBoundNames env' env)) body
    NormalFormApp env '(env', 'LFam (l :: Lambda s -> Proxy t -> Type)) '(env'', right) =
        --NormalForm (AppendBoundNames env' (AppendBoundNames env'' env)) (EvalFamily (l right))
        NormalForm env (EvalFamily (l right))
    NormalFormApp env '(env', 'LFam (l :: Lambda s -> Lambda t -> r)) '(env'', right) =
        --NormalForm (AppendBoundNames env' (AppendBoundNames env'' env)) ('LFam (l right))
        NormalForm env ('LFam (l right))

type family NormalFormCap (env :: BoundNames) (left :: (BoundNames, Lambda (LBase (s -> t)))) (right :: (BoundNames, Lambda (LBase s))) :: (BoundNames, Lambda (LBase t)) where
    -- In order to apply right to con, we need to evaluate right to a
    -- non-Lambda. This works only if right is an 'LCon.
    NormalFormCap env '(env', 'LCon con) '(env'', right) =
        NormalForm env ('LCon (con (GetLambda right)))

```
