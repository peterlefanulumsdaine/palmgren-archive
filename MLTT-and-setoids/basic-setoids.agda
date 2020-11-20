
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- {-# OPTIONS --no-eta-equality #-}

-- Agda version 2.5.2

module basic-setoids where

open import basic-types



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


extensionality1 : {A : setoid} -> {B : classoid} -> (f : setoidmap1 A B) -> (x y : || A ||) ->
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

