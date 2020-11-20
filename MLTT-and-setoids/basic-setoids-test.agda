
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.2

module basic-setoids-test where

open import basic-types

{--

-- We are building on
-- Peter Dybjer's standard MLTT formalization from Agda Wiki page

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


infix 3 _,_

data Σ (A : Set) (B : A -> Set) : Set where
   _,_ : (a : A) -> B a -> Σ A B

data Σ10 (A : Set1) (B : A -> Set) : Set1 where
   _,_ : (a : A) -> B a -> Σ10 A B

Erec : {A : Set} -> {B : A -> Set} -> {C : Σ A B -> Set}
   -> ((x : A) -> (y : B x) -> C (x , y))
   -> (z : Σ A B) -> C z
Erec d (x , y) = d x y

data Σ' (A : Set1) (B : A -> Set1) : Set1 where
   _,_ : (a : A) -> B a -> Σ' A B

-- data Π (A : Set) (B : A -> Set) : Set where
--   Λ : ((a : A) -> B a) -> Π A B
-- app :   {A : Set} -> {B : A -> Set} -> (Π A B) -> (x : A) -> B x
-- app (Λ f) a = f a

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



mutual
  data U : Set where
     n₀ : U
     n₁ : U
     _⊕_ : U -> U -> U    -- \oplus
     _⊗_ : U -> U -> U    -- \otimes
     σ : (a : U) -> (T a -> U) -> U
     π : (a : U) -> (T a -> U) -> U
     n : U
     w : (a : U) -> (T a -> U) -> U
     id : (a : U) -> T a -> T a -> U

  T : U -> Set
  T n₀        = N₀
  T n₁        = N₁
  T (a ⊕ b)   = T a + T b
  T (a ⊗ b)   = prod (T a) (T b)
  T (σ a b)   = Σ (T a) (\x -> T (b x))
  T (π a b)   = (x  : T a) -> T (b x)
  T n         = N
  T (w a b)   = W (T a) (\x -> T (b x))
  T (id a b c) = Id (T a) b c

-- Axiom for forming families over a disjoint union 
-- provable for A B in U


LD : (A B : Set) -> (P : A -> Set) -> (Q : B -> Set) -> (u : A + B) -> Set
LD A B P Q (inl a) = P a
LD A B P Q (inr b) = Q b


-- Below we take care not to introduce any further
-- constructions into Set. In Set1 we introduce
-- only records which corresponds to considering
-- schemas of types

pj1 :  {A : Set} -> {B : A -> Set}  -> Σ A B -> A
pj1 {A} {B} (a , b) =  a

pj2 :  {A : Set} -> {B : A -> Set}  -> (z : Σ A B) -> B (pj1 z)
pj2 {A} {B} (a , b) =   b


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


--}

-- setoids

reflexive : (A : Set) -> (R : A -> A -> Set) -> Set
reflexive A R = all A (\x -> R x x)

symmetric : (A : Set) -> (R : A -> A -> Set) -> Set
symmetric A R = all A (\x ->  all A (\y ->  implies (R x y) (R y x)))

transitive : (A : Set) -> (R : A -> A -> Set) -> Set
transitive A R = all A (\x ->  all A ( (\y ->  all A (\z -> implies (R x y) (implies (R y z) (R x z))))))

Eqrel : (A : Set) -> (R : A -> A -> Set) -> Set
Eqrel A R = and (reflexive A R) (and (symmetric A R) (transitive A R))

Refl : {A : Set} -> {R : A -> A -> Set} -> (Eqrel A R) -> (reflexive A R)
Refl {A} {R} c = andL {reflexive A R} {and (symmetric A R) (transitive A R)}  c

Sym : {A : Set} -> {R : A -> A -> Set} -> (Eqrel A R) -> (symmetric A R)
Sym {A} {R} c = andL {symmetric A R} {transitive A R} (andR {reflexive A R} {and (symmetric A R) (transitive A R)} c)

Tra : {A : Set} -> {R : A -> A -> Set} -> (Eqrel A R) -> (transitive A R)
Tra {A} {R} c = andR {symmetric A R} {transitive A R} (andR {reflexive A R} {and (symmetric A R) (transitive A R)} c)

record setoid : Set1  where
 infix 2 _∼_
 field
   object : Set
   _∼_ : object -> object -> Set
   eqrel : Eqrel object (_∼_)


infix 3 ||_||

||_|| : setoid -> Set
|| X || = setoid.object X

-- <_>_~_ : (X : setoid) -> || X || -> || X || -> Set
-- < X > a ~ b = setoid._∼_ X a b


record <_>_~_ (X : setoid) (a b : || X ||) : Set where
 constructor <>
 field
   pf-eq : setoid._∼_ X a b

>< : {X : setoid} -> {a b : || X ||} ->  (< X > a ~ b) ->  setoid._∼_ X a b
>< {X} {a} {b} p =  <_>_~_.pf-eq p



refl : (X : setoid) -> (a : || X ||) ->  < X > a ~ a
refl X a = <> ((Refl (setoid.eqrel X)) a)

sym :  {X : setoid} -> {a : || X ||} -> {b : || X ||} -> < X > a ~ b  ->  < X > b ~ a 
sym {X} {a} {b} p = <> (impE (((Sym (setoid.eqrel X)) a) b) (>< p))

tra :  {X : setoid} -> {a : || X ||} -> {b : || X ||} -> {c : || X ||} -> < X > a ~ b  -> < X > b ~ c ->  < X > a ~ c
tra {X} {a} {b} {c} p q = <> (impE (impE ((((Tra (setoid.eqrel X)) a) b) c) (>< p)) (>< q))


-- classoids


reflexive' : (A : Set1) -> (R : A -> A -> Set) -> Set1
reflexive' A R = (x : A) -> R x x

symmetric' : (A : Set1) -> (R : A -> A -> Set) -> Set1
symmetric' A R = (x y : A) ->  (R x y) -> (R y x)

transitive' : (A : Set1) -> (R : A -> A -> Set) -> Set1
transitive' A R = (x y z : A) ->  (R x y) -> (R y z) -> (R x z)

record Eqrel' (A : Set1) (R : A -> A -> Set) : Set1 where
  field
    rf' : reflexive' A R
    sy' : symmetric' A R
    tr' : transitive' A R


record classoid : Set2  where
 infix 2 _∼_
 field
   object : Set1
   _∼_ : object -> object -> Set
   eqrel : Eqrel' object (_∼_)


infix 3 |||_|||

|||_||| : classoid -> Set1
||| X ||| = classoid.object X

-- <<_>>_~_ : (X : classoid) -> ||| X ||| -> ||| X ||| -> Set
-- << X >> a ~ b = classoid._∼_ X a b

record <<_>>_~_ (X : classoid) (a b : ||| X |||) : Set where
 constructor <<>>
 field
   pf-eq : classoid._∼_ X a b


>><< : {X : classoid} -> {a b : ||| X |||} ->  (<< X >> a ~ b) ->  classoid._∼_ X a b
>><< {X} {a} {b} p =  <<_>>_~_.pf-eq p




refl' : (X : classoid) -> (a : ||| X |||) ->  << X >> a ~ a
refl' X a = <<>> (Eqrel'.rf' (classoid.eqrel X) a)

sym' :  {X : classoid} -> {a : ||| X |||} -> {b : ||| X |||} -> << X >> a ~ b  ->  << X >> b ~ a 
sym' {X} {a} {b} p = <<>> (Eqrel'.sy' (classoid.eqrel X) a b (>><< p ))

tra' :  {X : classoid} -> {a : ||| X |||} -> {b : ||| X |||} -> {c : ||| X |||} -> << X >> a ~ b  -> << X >> b ~ c ->  << X >> a ~ c
tra' {X} {a} {b} {c} p q = <<>> (Eqrel'.tr' (classoid.eqrel X) a b c (>><< p) (>><< q))

-- setoid
-- constructions

Id-to-Eq :  (X : setoid) -> {x y : || X ||} ->
           Id || X || x y -> < X > x ~ y
Id-to-Eq X {x} {y} p = Jrec || X || x y (λ u v z →  < X > u ~ v) (refl X _) p




-- trivial setoid on a type - all elements are equal

triv-setoid : Set -> setoid
triv-setoid A = record { object = A
                       ; _∼_  =  (\x ->  (\y -> True))
                       ; eqrel = andI (allI (λ a → tt)) 
                         (andI (allI (λ a → allI (λ b → impI (λ p → tt)))) 
                            (allI (λ a → allI (λ b → allI (λ c → impI (λ p → impI (λ q → tt))))))) } 


-- free setoid on a type

free-setoid : Set -> setoid
free-setoid A = record { object = A
                          ; _∼_  =  (\x ->  (\y -> Id A x y))
                          ; eqrel = andI (allI (λ a → rf)) 
                          (andI (allI (λ a → allI (λ b → impI (λ p → Isym A a b p)))) 
                            (allI (λ a → allI (λ b → allI (λ c → impI (λ p → impI (λ q → Itra A a b c p q))))))) } 





record setoidmap (A B : setoid) : Set where
  field
    op : fun || A || || B ||
    ext : all || A || (\x ->  all || A ||  (\y ->  (implies  (< A > x ~ y)  (< B > (op x) ~ (op y)))))



exteq : {A B : setoid} -> (f g : setoidmap A B) -> Set
exteq {A} {B} f g = (x : || A ||) ->  < B > ((setoidmap.op f) x) ~ ((setoidmap.op g) x)

setoidmaps : (A B : setoid) -> setoid
setoidmaps A B = record {object = setoidmap A B
                          ; _∼_  =  exteq {A} {B}
                          ; eqrel = andI (allI (λ a x → refl B _))
                                         (andI (allI (λ a → allI (λ b → impI (λ p x →  
                                                       sym (p x))))) 
                                              ((allI (λ a → allI (λ b → (allI (λ c → 
                                                 impI (λ p → impI (λ q x → 
                                          tra (p x) (q x))) )))))))                         
                         }



_=>_ : setoid -> setoid -> setoid
A => B = setoidmaps A B


ap : {A B : setoid} -> (f : || A => B ||) -> (a : || A ||) -> || B ||
ap f a  = setoidmap.op f a

extensionality : {A B : setoid} -> (f : || A => B ||) -> (x y : || A ||) -> 
             (< A > x ~ y) ->  (< B > (ap f x) ~ (ap f y))
extensionality {A} {B} f x y p = impE (setoidmap.ext f x y) p

is-injective : (A B : setoid) -> (f : || A => B ||) -> Set
is-injective A B f = (x y : || A ||) -> (< B > (ap f x) ~ (ap f y)) ->  < A > x ~ y


{-- to correct or delete

binsetoidmap-helper : {A B C : setoid} -> (f : || A || -> || B || -> || C ||)
  -> (p : (a a' : || A ||) -> (< A > a ~ a' -> (b : || B ||) -> < C > f a b ~ f a' b))
  -> (q : (a : || A ||) ->  (b b' : || B ||) -> (< B > b ~ b' ->  < C > f a b ~ f a b'))
  -> || A => (B => C) ||
binsetoidmap-helper {A} {B} {C} f p q 
             = record { op =  (\x -> record { op =   (\y -> f x y)
                                           ; ext = allI (\u ->  allI (\v -> impI (\p ->  (q x u v (<> p)))))
                                           })
                      ; ext = allI (\u ->  allI (\v -> impI (\p' -> λ x → p u v p' x)))
                      }

trinsetoidmap-helper : {A B C D : setoid} -> (f : || A || -> || B || -> || C || -> || D ||)
 ->  (p : (a a' : || A ||) -> < A > a ~ a' -> (b : || B ||) -> (c : || C ||) 
      -> < D > f a b c ~ f a' b c)
 ->  (q : (a : || A ||) -> (b b' : || B ||) ->   < B > b ~ b' -> (c : || C ||) -> < D > f a b c ~ f a b' c)
 ->  (t : (a : || A ||) -> (b : || B ||) -> (c c' : || C ||) -> < C >  c ~ c' -> < D > f a b c ~ f a b c')
 -> || A => (B => (C => D)) ||
trinsetoidmap-helper {A} {B} {C} {D} f p q t 
                    = record { op = (\x -> record { op = (\y -> record { op = (\z -> f x y z)
                                                                            ; ext = allI (\u ->  
                                                                                    allI (\v -> 
                                                                                      impI (\p' -> t x y u v p')))
                                                                            })
                                                     ; ext = allI (\u ->  
                                                              allI (\v -> 
                                                                impI (\p' -> λ x' → q x u v p' x')))
                                                     })
                             ; ext =  allI (\u ->  
                                        allI (\v -> 
                                          impI (\p' -> λ x x' → p u v p' x x')))
                              }

--}

idmap : {A : setoid} -> || A => A ||
idmap {A} = record { op =  (\x -> x)
                   ; ext = allI (λ a → allI (λ b → impI (λ p → p)))
                   }


infix 5 _°_

_°_ : {A B C : setoid} -> (f : || B => C ||) -> (g : || A => B ||) -> || A => C ||
_°_ {A} {B} {C} f g =  record { op =   (\x -> ap f (ap g x)) 
                              ; ext =  allI (λ u → allI (λ v → 
                                   impI (λ p →    (setoidmap.ext f (ap g u) (ap g v)) 
                                                         (setoidmap.ext g u v p)    
                                      )))
                               }
                                                 
_≅_ : setoid -> setoid -> Set
A ≅ B = Σ || A => B || (\f ->  
        Σ || B => A || (\g -> 
           (and ((x : || A ||) -> < A > ap g (ap f x) ~ x)
                ((y : || B ||) -> < B > ap f (ap g y) ~ y))))
    
fwd : {A B : setoid} -> (A ≅ B) -> || A => B ||
fwd p = pj1 p

bck : {A B : setoid} -> (A ≅ B) -> || B => A ||
bck p = pj1 (pj2 p)






record setoidmap1 (A : setoid) (B : classoid) : Set1 where
  field
    op : || A || ->  ||| B |||
    ext : (x y : || A ||) -> (< A > x ~ y)  -> (<< B >> (op x) ~ (op y))

ap1 : {A : setoid} -> {B : classoid} -> (f : setoidmap1 A B) -> (a : || A ||) -> ||| B |||
ap1 f a = setoidmap1.op f a

infix 10 _•_

-- •  is  \bu2
_•_ : {A : setoid} -> {B : classoid} -> (f : setoidmap1 A B) -> (a : || A ||) -> ||| B |||
_•_ f a = ap1 f a

exteq1 : {A : setoid}->  {B : classoid} -> (f g : setoidmap1 A B) -> Set
exteq1 {A} {B} f g = (x : || A ||) ->  << B >> (f • x) ~ (g • x)

setoidmaps1 : (A : setoid) -> (B : classoid) -> classoid
setoidmaps1 A B = record {object = setoidmap1 A B
                          ; _∼_  =  exteq1 {A} {B}
                          ; eqrel = record { rf' = λ f x → refl' B (f • x) 
                                           ; sy' = λ f g p x → sym' {B} (p x) 
                                           ; tr' = λ f g h p q x → tra' {B} (p x) (q x) }
                         }

_=>01_ : setoid -> classoid -> classoid
A =>01 B = setoidmaps1 A B

extensionality1 : {A : setoid} -> {B : classoid} -> (f : ||| A =>01 B |||) -> (x y : || A ||) -> 
             (< A > x ~ y) ->  (<< B >> (f • x) ~ (f • y))
extensionality1 {A} {B} f x y p = (setoidmap1.ext f x y) p

is-injective1 : {A : setoid} -> {B : classoid} -> (f : setoidmap1 A B) -> Set
is-injective1 {A} {B} f = (x y : || A ||) -> (<< B >> (f • x) ~ (f • y)) ->  < A > x ~ y




comp1 : {A B : setoid} -> {C : classoid} -> (f : setoidmap1 B C) -> (g : || A => B ||) -> setoidmap1 A C
comp1 {A} {B} {C} f g =  record { op =   (\x -> ap1 f (ap g x)) 
                                ; ext = λ x y p → setoidmap1.ext f (ap g x) (ap g y) 
                                                                    (setoidmap.ext g x y p)
                               }
        


record setoidmap11 (A B : classoid) : Set1 where
  field
    op : ||| A ||| ->  ||| B |||
    ext : (x y : ||| A |||) -> (<< A >> x ~ y)  -> (<< B >> (op x) ~ (op y))

ap11 : {A B : classoid} -> (f : setoidmap11 A B) -> (a : ||| A  |||) -> ||| B |||
ap11 f a = setoidmap11.op f a


extensionality11 : {A B : classoid} -> (f : setoidmap11 A B) -> (x y : ||| A |||) -> 
             (<< A >> x ~ y) ->  (<< B >> (ap11 f x) ~ (ap11 f  y))
extensionality11 {A} {B} f x y p = (setoidmap11.ext f x y) p



comp11 : {A B C : classoid} -> (f : setoidmap11 B C) -> (g : setoidmap11 A B) -> setoidmap11 A C
comp11 {A} {B} {C} f g =  record { op =   (\x -> ap11 f (ap11 g x)) 
                                ; ext = λ x y p → setoidmap11.ext f (ap11 g x) (ap11 g y) 
                                                                    (setoidmap11.ext g x y p)
                               }

comp01 : {A : setoid} -> {B C : classoid} -> (f : setoidmap11 B C) -> (g : setoidmap1 A B) -> setoidmap1 A C
comp01 {A} {B} {C} f g =  record { op =   (\x -> ap11 f (ap1 g x)) 
                                ; ext = λ x y p → setoidmap11.ext f (ap1 g x) (ap1 g y) 
                                                                    (setoidmap1.ext g x y p)
                               }


