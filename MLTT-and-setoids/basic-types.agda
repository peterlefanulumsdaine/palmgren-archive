
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- {-# OPTIONS --no-fast-reduce #-}

-- {-# OPTIONS --no-eta-equality #-}

-- Agda version 2.5.2

module basic-types where


-- For MLTT  we are building on
-- Peter Dybjer's formalization from Agda Wiki page

data N₀ : Set where

R₀ : {C : N₀ -> Set} -> (c : N₀) -> C c
R₀ ()

data  N₁ : Set where
  0₁ : N₁

R₁ : {C : N₁ -> Set} -> C 0₁ -> (c : N₁) -> C c
R₁ d 0₁ = d

infix 2 _+_

data _+_ (A B : Set) : Set where
    inl : A -> A + B
    inr : B -> A + B

D : {A B : Set} -> {C : A + B -> Set}
   -> ((a : A) -> C (inl a)) -> ((b : B) -> C (inr b)) -> (c : A + B) -> C c
D d e (inl a) = d a
D d e (inr b) = e b



record prod (A B : Set) : Set where
  constructor pair
  field
    prj1 : A
    prj2 : B
open prod public

{-- the above record replaces:

data prod (A : Set) (B : Set) : Set where
   pair : A -> B -> prod A B

prodL :  {A : Set} -> {B : Set} -> (prod A B) -> A
prodL {A} {B} (pair a b) = a

prj1 :  {A : Set} -> {B : Set} -> (prod A B) -> A
prj1 {A} {B} (pair a b) = a

prodR :  {A : Set} -> {B : Set} -> (prod A B) -> B
prodR {A} {B} (pair a b) = b

prj2 :  {A : Set} -> {B : Set} -> (prod A B) -> B
prj2 {A} {B} (pair a b) = b
--}

infix 3 _,_

record  Σ  (A : Set) (B : A -> Set) : Set where
  constructor  _,_
  field
    pj1 : A
    pj2 : B pj1
open Σ public


{--
data Σ (A : Set) (B : A -> Set) : Set where
   _,_ : (a : A) -> B a -> Σ A B

pj1 :  {A : Set} -> {B : A -> Set}  -> Σ A B -> A
pj1 {A} {B} (a , b) =  a

pj2 :  {A : Set} -> {B : A -> Set}  -> (z : Σ A B) -> B (pj1 z)
pj2 {A} {B} (a , b) =   b
--}

-- data Σ10 (A : Set1) (B : A -> Set) : Set1 where
--   _,_ : (a : A) -> B a -> Σ10 A B

record  Σ10  (A : Set1) (B : A -> Set) : Set1 where
  constructor  _,_
  field
    pj1 : A
    pj2 : B pj1
open Σ10 public



data N : Set where
   O : N
   s : N -> N

rec : {C : N -> Set} -> C O -> ((n : N) -> C n -> C (s n)) -> (c : N) -> C c
rec d e O = d
rec d e (s n) = e n (rec d e n)

data W (A : Set) (B : A -> Set) : Set where
   sup : (a : A) -> (b : B a -> W A B) -> W A B

wrec : {A : Set} -> {B : A -> Set} -> {C : W A B -> Set}
      -> ((a : A) -> (b : B a -> W A B) -> ((x : B a) -> C (b x)) -> C (sup a b))
      -> (c : W A B) -> C c
wrec {C = C} d (sup a b) = d a b (\x -> wrec {C = C} d (b x))

data Id (A : Set) : A -> A -> Set where
   rf : {a : A} -> Id A a a

J : {A : Set} -> {a b : A} -> {C : (x y : A) -> (z : Id A x y) -> Set}
   -> ({x : A} -> C x x rf)
   -> (c : Id A a b) -> C a b c
J d rf = d


{-- Universe operators and super universe from "On universes in
 type theory", Palmgren 1998 --}

{-- universe operator --}

mutual
  data Uo (A : Set) (B : A -> Set) : Set where
     n₀ : Uo A B
     n₁ : Uo A B
     ix : Uo A B
     lft : A -> Uo A B
     _⊕_ : Uo A B -> Uo A B -> Uo A B  -- \oplus
     _⊗_ : Uo A B -> Uo A B -> Uo A B  -- \otimes
     σ : (a : Uo A B) -> (To a -> Uo A B) -> Uo A B
     π : (a : Uo A B) -> (To a -> Uo A B) -> Uo A B
     n : Uo A B
     w : (a : Uo A B) -> (To a -> Uo A B) -> Uo A B
--     id : (a : Uo A B) -> To a -> To a -> Uo A B   ** do not need this for Aczel's V-construction

  To : {A : Set} {B : A -> Set} ->  Uo A B -> Set
  To n₀              = N₀
  To n₁              = N₁
  To {A} {B} ix      = A
  To {A} {B} (lft a)  = B a
  To (a ⊕ b)         = To a + To b
  To (a ⊗ b)         = prod (To a) (To b)
  To (σ a b)         = Σ (To a) (\x -> To (b x))
  To (π a b)         = (x  : To a) -> To (b x)  -- Π (To a) (\x -> To (b x))
  To n               = N
  To (w a b)         = W (To a) (\x -> To (b x))
--   To (id a b c)       = Id (To a) b c   ** do not need this for Aczel's V-construction

-- First universe is now constructed by

U : Set
U = Uo N₀ (\x -> N₀)


T : U -> Set
T = To {N₀} {\x -> N₀}


{-- nth Universe, internally indexed; see also notes by C McBride
"Dependently Typed Metaprogramming (in Agda)"  2013 --}

data Setfam : Set1 where
   setfam : (A : Set) -> (B : A -> Set) -> Setfam

ind : Setfam  -> Set
ind (setfam A B) = A

fam : (F : Setfam) -> (ind F) -> Set
fam (setfam A B) x = B x

Emptyfam : Setfam
Emptyfam = setfam N₀ (\x -> N₀)

NextUT : Setfam -> Setfam
NextUT F = setfam (Uo (ind F) (fam F)) (To {ind F} {fam F})

nthUT : N -> Setfam
nthUT O = NextUT Emptyfam
nthUT (s k) = NextUT (nthUT k)

{-- The nth universe is now given by this sequence of families of sets --}

nthU : N -> Set
nthU k = ind (nthUT k)

nthT : (k : N) -> (nthU k) -> Set
nthT k = fam (nthUT k)





-- Axiom for forming families over a disjoint union
-- provable for A B in U




LD : (A B : Set) -> (P : A -> Set) -> (Q : B -> Set) -> (u : A + B) -> Set
LD A B P Q (inl a) = P a
LD A B P Q (inr b) = Q b


-- Below we take care not to introduce any further
-- constructions into Set. In Set1 we introduce
-- only records which corresponds to considering
-- schemas of types



Jrec : (A : Set) -> (a b : A) -> (C : (x y : A) -> (z : Id A x y) -> Set)
   -> ({x : A} -> C x x rf)
   -> (c : Id A a b) -> C a b c
Jrec A a b C d c =  J {A} {a} {b} {C} d c


Isub : {A : Set} -> (P : A -> Set)  ->  {x y : A} -> (Id A x y) -> (P x) -> (P y)
Isub {A} P {x} {y} p = Jrec A x y (\u -> \v -> \w -> (P u) -> (P v)) ((\v -> v)) p

Ifunext : {A  B : Set} -> (f : A -> B)  ->  {x y : A} -> (Id A x y) -> Id B (f x) (f y)
Ifunext {A} {B} f {x} {y} p  = Jrec A x y (\x -> \y -> \z -> Id B (f x) (f y)) rf p

Idepfunext : (A : Set) -> (B : A -> Set) -> (f : (u : A) -> B u) ->
           (x y : A) -> (p : (Id A x y)) -> Id (B y) (Isub B p (f x)) (f y)
Idepfunext A B f x y p = Jrec A x y (\u -> \v -> \w -> Id (B v) (Isub B w (f u)) (f v)) rf p

False : Set
False = N₀

exfalso : (A : Set) -> False -> A
exfalso A u = R₀ {\z -> A} u

True : Set
True = N₁

tt : True
tt = 0₁

implies : (A : Set) -> (B : Set)  -> Set
implies A B = A -> B

impI : {A : Set} -> {B : Set} -> (A -> B) -> implies A B
impI f =  f

impE : {A : Set} -> {B : Set} -> (implies A B) -> A -> B
impE f a = f a

fun : (A : Set) -> (B : Set)  -> Set
fun A B = A -> B

all : (A : Set) -> (B : A -> Set) -> Set
all A B = (x : A) -> B x

allI : {A : Set} -> {B : A -> Set} -> ((a : A) -> B a) -> all A B
allI f =  f



and : (A : Set) -> (B : Set) -> Set
and A B = prod A B

andI :  {A : Set} -> {B : Set} -> (a : A) -> (b : B) -> and A B
andI a b = pair a b

andL :  {A : Set} -> {B : Set} -> (and A B) -> A
andL {A} {B} c = prj1 c

andR :  {A : Set} -> {B : Set} -> (and A B) -> B
andR {A} {B} c = prj2 c

exists : (A : Set) -> (B : A -> Set) -> Set
exists A B =  Σ A B

existsI : {A : Set} -> {B : A -> Set} ->
          (a : A) -> (b : B a) -> exists A B
existsI a b = ( a , b )

or  : (A : Set) -> (B : Set) -> Set
or A B = A + B

orL  : {A : Set} -> {B : Set} -> A -> or A B
orL a = inl a

orR  : {A : Set} -> {B : Set} -> B -> or A B
orR b = inr b

orE : {A B : Set} -> {C : (or A B) -> Set}
   -> ((a : A) -> C (orL a)) -> ((b : B) -> C (orR b)) -> (c : or A B) -> C c
orE = D

orEweak : {A B C : Set}
   -> (A -> C) -> (B -> C)  -> (c : or A B) -> C
orEweak f g (inl a) = f a
orEweak f g (inr b) = g b



iff :  (A : Set) -> (B : Set) -> Set
iff A B = and (implies A B) (implies B A)

triviff : (A : Set) -> iff A A
triviff A = andI (impI (\x -> x)) (impI (\x -> x))

not : (A : Set) -> Set
not A = implies A False

Bool : Set
Bool = N₁ + N₁

true : Bool
true = inl 0₁

false : Bool
false = inr 0₁

if :  (A : Set) ->  Bool -> (a : A) -> (b : A) -> A
if A (inl x)  a b = a
if A (inr x)  a b = b

-- use the universe to relate Bool to True and False

val : (x : Bool) -> U
val x = D {N₁} {N₁} {\z -> U} (\x -> n₁) (\y -> n₀) x

Val : (x : Bool) -> Set
Val x = T (val x)

non-trivial-Bool : not (Id Bool true false)
non-trivial-Bool = impI (λ p → Isub Val p tt)

-- sums are disjoint.

is-inl :  (A B : Set) -> (u : A + B) -> Bool
is-inl A B u = D (\a -> true) (\b -> false) u

is-inr :  (A B : Set) -> (u : A + B) -> Bool
is-inr A B u = D (\a -> false) (\b -> true) u

disjointness-sum :  (A B : Set) -> (a : A) -> (b : B)
            -> not (Id (A + B) (inl a) (inr b))
disjointness-sum A B a b = impI (λ p → impE non-trivial-Bool (Ifunext (is-inl A B) p))

disjointness-sum2 :  (A B : Set) -> (a : A) -> (b : B)
            -> not (Id (A + B) (inr b) (inl a))
disjointness-sum2 A B a b = impI (λ p → impE non-trivial-Bool (Ifunext (is-inr A B) p))

-- inl and inr are injective proved using code-encode of
-- p 85-86 in HoTT (but use  LD instead of full universe).
-- Vaguely seen this before. Wilander's paper?

code-inl : (A B : Set) -> (a : A) -> (u : (A + B)) -> Set
code-inl A B a = (LD A B (\x -> Id A a x)  (\y -> False))

code-inr : (A B : Set) -> (b : B) -> (u : (A + B)) -> Set
code-inr A B b = (LD A B (\x -> False)  (\y -> Id B b y))

encode-inl :  (A B : Set) -> (a : A) -> (u : A + B) -> (Id (A + B) (inl a) u) -> (code-inl A B a u)
encode-inl A B a u p  = Isub (code-inl A B a) p rf

encode-inr :  (A B : Set) -> (b : B) -> (u : A + B) -> (Id (A + B) (inr b) u) -> (code-inr A B b u)
encode-inr A B b u p  = Isub (code-inr A B b) p rf

inl-injective  : (A B : Set) -> (a : A) -> (c : A) -> Id (A + B) (inl a) (inl c) -> Id A a c
inl-injective A B a c p = encode-inl A B a (inl c) p

inr-injective  : (A B : Set) -> (b : B) -> (d : B) -> Id (A + B) (inr b) (inr d) -> Id B b d
inr-injective A B b d p = encode-inr A B b (inr d) p


Isym : (A : Set) -> (x y : A) -> Id A x y -> Id A y x
Isym A x y p = Jrec A x y ((\x -> \y ->  \z -> Id A y x)) rf p

Itra : (A : Set) -> (x y z : A) -> Id A x y -> Id A y z -> Id A x z
Itra A x y z p q =  impE (Jrec A x y ((\u -> \v ->  \w -> implies (Id A v z) (Id A u z) ))
                              (impI (\v -> v)) p) q

