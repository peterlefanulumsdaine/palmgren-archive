-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt0 where

open import basic-types
open import basic-setoids
open import dependent-setoids
open import subsetoids
open import iterative-sets
open import iterative-sets-pt2
open import iterative-sets-pt3

-- V-model parts 1 - 9

-- A setoid model for extensional Martin-Löf type theory
-- using Aczel's set-theoretic universe V as a universe
-- of setoid.

-- The classoid of contexts is V with its standard bisimulation
-- equality.

Ctx : classoid
Ctx = VV

ctx : Set1
ctx = V

-- Every set a in V gives rise to a canonical setoid  κ a.
-- See previous files.
-- The context maps are extensional functions between
-- such canonical setoids.

ctx-maps : (a b : ctx) -> setoid
ctx-maps a b = (κ a => κ b)

ctx-trp :  {a b : ctx} -> (p : a ≐ b) -> || ctx-maps a b ||
ctx-trp {a} {b} p = κ-trp p

-- see properties of κ-trp

-- type of substitutions
-- made in to a record to improve derivation of implicit arguments

record subst (a b : ctx ) : Set where
  constructor sb
  field
    cmap : || ctx-maps a b ||

Subst : (a b : ctx) -> setoid
Subst a b = record {object = subst a b
                   ;  _∼_ = \f -> \g -> < ctx-maps a b > subst.cmap f ~ subst.cmap g
                   ; eqrel = pair (λ f -> <> (\ x → refl (κ b) _))
                                  (pair (λ f g p -> <> (\ x → sym {κ b} ((>< p) x)))
                                        (λ f g h p q -> <> (\ x → tra {κ b} ((>< p) x) ((>< q) x))))
                   }

-- application of substitution.

aps : {a b : ctx} -> (f : subst a b) -> (x : || κ a ||) -> || κ b ||
aps f x = (ap (subst.cmap f) x)

aps-ext : {a b : ctx} -> (f : subst a b) -> (x y : || κ a ||)
              -> < κ a > x ~ y -> < κ b > aps f x ~ aps f y
aps-ext {a} {b} f x y p = extensionality (subst.cmap f) x y p

-- identity substitution and a short form

idsubst : {Γ : ctx} -> subst Γ Γ
idsubst {Γ} = subst.sb (idmap {κ Γ})

ids : {Γ : ctx} -> subst Γ Γ
ids {Γ} = idsubst {Γ}

-- composition of substitutions

infix 5 _⌢_  -- ⌢

_⌢_ : {Θ Δ Γ : ctx} -> (f : subst Δ Γ) -> (g : subst Θ Δ) -> (subst Θ Γ)
f ⌢ g = subst.sb (subst.cmap f ° subst.cmap g)



subst-cong : {Θ Δ Γ : ctx} -> (f f' : subst Δ Γ) -> (g  g' : subst Θ Δ)
      -> < Subst Δ Γ > f ~ f'
      -> < Subst Θ Δ > g ~ g'
      -> < Subst Θ Γ > (f ⌢ g) ~ (f' ⌢ g')
subst-cong {Θ} {Δ} {Γ} f f' g g' p q =
    <> (<> (λ x →
   let eq1 : < κ Γ > setoidmap.op (subst.cmap f ° subst.cmap g) x ~
                     setoidmap.op (subst.cmap f ° subst.cmap g' ) x
       eq1 = extensionality (subst.cmap f) _ _ ((>< (>< q) x))
       eq2 : < κ Γ > setoidmap.op (subst.cmap f ° subst.cmap g' ) x ~
                    setoidmap.op (subst.cmap (f') ° subst.cmap (g')) x
       eq2 = >< (>< p) ( aps g' x)
       eq : < κ Γ > setoidmap.op (subst.cmap f ° subst.cmap g) x ~
                    setoidmap.op (subst.cmap (f') ° subst.cmap (g')) x
       eq = tra eq1 eq2
   in eq))




-- classoid of raw terms are (also) setoidmaps01 into VV
-- (made into a record to improve derivation of implicit arguments)

record raw  (Γ : ctx) : Set1 where
   constructor mkraw
   field
     rawterm : |||  setoidmaps1 (κ Γ) VV |||

apr : {Γ : ctx} -> (a : raw Γ) -> (x : || κ Γ ||) -> V
apr {Γ} a x = (raw.rawterm a) • x


Raw : (Γ : ctx) -> classoid
Raw Γ = record {object = raw Γ
               ;  _∼_ = \a -> \b -> << setoidmaps1 (κ Γ) VV >> (raw.rawterm a) ~ (raw.rawterm b)
               ; eqrel = record { rf' = λ x → <<>> (λ t → <<>> (refV _))
                                ; sy' = λ x y p → <<>> (λ t → <<>> (symV (>><< (>><< p t))))
                                ; tr' =  λ x y z p q → <<>> (λ t → <<>> (traV ((>><< (>><< p t))) ((>><< (>><< q t)))))
                                }
               }



-- classoids of types over context are setoidmaps01 into VV
-- (made into a record to improve derivation of implicit arguments)


{--
record ty (Γ : ctx) : Set1 where
  constructor tyy
  field
    type : ||| setoidmaps1 (κ Γ) VV  |||
--}

{-- New version trying to making it synonymous (thanks to Guillaum Brunerie) :
--}


ty : (Γ : ctx) -> Set1
ty Γ = raw Γ

module ty {Γ : ctx} where
  tyy : |||  setoidmaps1 (κ Γ) VV ||| → raw Γ
  tyy = mkraw

  type : raw Γ → |||  setoidmaps1 (κ Γ) VV |||
  type = raw.rawterm

open ty public

{-- end of new version

--}

-- application of types

apt : {Γ : ctx} -> (A : ty Γ) -> (x : || κ Γ ||) -> V
apt {Γ} A x = (ty.type A) • x



Ty : (Γ : ctx) -> classoid
Ty Γ =  record {object = ty Γ
               ;  _∼_ = \A -> \B -> << setoidmaps1 (κ Γ) VV >> (ty.type A) ~ (ty.type B)
               ; eqrel = record { rf' = λ x → <<>> (λ t → <<>> (refV _))
                                ; sy' = λ x y p → <<>> (λ t → <<>> (symV (>><< (>><< p t))))
                                ; tr' = λ x y z p q → <<>> (λ t → <<>> (traV ((>><< (>><< p t))) ((>><< (>><< q t)))))
                                }
               }




-- well typed terms among raw terms

record tm (Γ : ctx) (A : ty Γ) : Set1 where
  field
    trm : raw Γ
    corr : (x : || κ Γ ||) ->  (apr trm x) ∈ (apt A x)

-- Definition of interpretation of the type-theoretic judgements
--  Γ context
--  Γ ==> A type
--  Γ ==> A == B
--  Γ ==> a :: A
--  Γ ==> a == b :: A

-- (make all these into records just as subst to improve inference of hidden variables?)

--  Γ context
--  is just  Γ : ctx

--   Γ ==> A type
--  is just  A : ty Γ

--  Γ ==> A == B

infix 10  _==>_==_

record _==>_==_ (Γ : ctx) (A B : ty Γ) : Set where
 constructor mk-eqty
 field
   judge-eqty : exteq1 (ty.type A) (ty.type B) --  ought to be Ty equality



ape : {Γ : ctx} -> {A B : ty Γ} ->  (p : Γ ==> A == B) -> (u : || κ Γ ||) -> << VV >> (apt A u) ~ (apt B u)
ape {Γ} {A} {B} p u =  _==>_==_.judge-eqty p u



--  Γ ==> a :: A

infix 10 _==>_::_

record _==>_::_ (Γ : ctx) (a : raw Γ) (A : ty Γ) : Set where
 constructor mk-elt
 field
   judge-elt : (x : || κ Γ ||) ->  (apr a x) ∈ (apt A x)

apel :  {Γ : ctx} -> {a : raw Γ} -> {A : ty Γ}
        -> (p : Γ ==> a :: A) ->  (u : || κ Γ ||)
        ->  (apr a u) ∈ (apt A u)
apel p u =  _==>_::_.judge-elt p u

--  Γ ==> a == b :: A

infix 10  _==>_==_::_

_==>_==_::_ : (Γ : ctx) -> (a b : raw Γ) -> (A : ty Γ) -> Set
Γ ==> a == b :: A = and ((x : || κ Γ ||) -> (apr a x) ≐ (apr b x)) -- should be raw equality, but size issues
                        (and (Γ ==> a :: A) (Γ ==> b :: A))


Raw-lm  : {Γ : ctx} -> {a b : raw Γ}
       -> (<< Raw Γ >> a ~ b)
       -> ((x : || κ Γ ||) -> (apr a x) ≐ (apr b x))
Raw-lm {Γ} {a} {b} p x = >><< (>><< (>><< p) x)

Raw-lm2  : {Γ : ctx} -> {a b : raw Γ}
       -> ((x : || κ Γ ||) -> (apr a x) ≐ (apr b x))
       -> (<< Raw Γ >> a ~ b)
Raw-lm2 {Γ} {a} {b} p = <<>> (<<>> (λ x → <<>> (p x)))


-- Verification of general rules for the type and element equality


tyrefl :  {Γ : ctx}
--
         -> (A : ty Γ)
-- ------------------------
         -> Γ ==> A == A
--
tyrefl A = mk-eqty (λ x → refl' _ _)



tysym :  {Γ : ctx} -> {A B : ty Γ}
--
         -> Γ ==> A == B
--   --------------------------
         -> Γ ==> B == A
--
tysym {A} {B} p = mk-eqty (λ x → sym'  (ape p x))



tytra :  {Γ : ctx} -> {A B C : ty Γ}
--
         -> Γ ==> A == B  -> Γ ==> B == C
--  -------------------------------------
                -> Γ ==> A == C
--
tytra {A} {B} {C} p q = mk-eqty (λ x → tra' (ape p x) (ape q x))




tmrefl :  {Γ : ctx} -> {A : ty Γ}-> {a : raw Γ}
--
         -> Γ ==> a :: A
--    ------------------------
         -> Γ ==> a == a :: A
--
tmrefl p = pair (λ x → refV _) (pair p p)



tmsym :  {Γ : ctx} -> (A : ty Γ) -> (a b : raw Γ)
--
         -> Γ ==> a == b :: A
--    ------------------------
         -> Γ ==> b == a :: A
--
tmsym A a b p = pair (λ x → symV (prj1 p x)) (pair (prj2 (prj2 p)) (prj1 (prj2 p)))

tmtra :  {Γ : ctx} -> (A : ty Γ) -> (a b c : raw Γ)
--
         -> Γ ==> a == b :: A   -> Γ ==> b == c :: A
--  --------------------------------------------------
         -> Γ ==> a == c :: A
--
tmtra A a b c p q = pair (λ x → traV (prj1 p x) (prj1 q x)) (pair (prj1 (prj2 p)) (prj2 (prj2 q)))





-- The crucial type equality is verified

elttyeq :  {Γ : ctx} ->  {a : raw Γ}  -> {A B : ty Γ}
--
      -> Γ ==> a :: A     -> Γ ==> A == B
--  --------------------------------------------
              -> Γ ==> a :: B
--
elttyeq {Γ} {a} {A} {B} p q =
    mk-elt (λ x → (e+ (>><< (ape q x)) (pj1 (apel p x))) , traV (pj2 (apel p x)) (e+prop (>><< (ape q x)) (pj1 (apel p x))) )



-- some auxiliary lemmas

pj1elttyeq :  {Γ : ctx} ->  {a : raw Γ}  -> {A B : ty Γ}
--
      -> Γ ==> a :: A     -> Γ ==> A == B
      -> (x : || κ Γ ||)
      ->  || κ (apt B x) ||
pj1elttyeq {Γ} {a} {A} {B} p q x = e+ (>><< (ape q x)) (pj1 (apel p x))



elttyeq-lm :  {Γ : ctx} ->  {a : raw Γ}  -> {A B : ty Γ}
      -> (p : Γ ==> a :: A)     -> (q : Γ ==> A == B)
      -> (x : || κ Γ ||)
      ->  (apr a x) ≐ (apt B x) ‣  (pj1elttyeq p q x) -- (pj1  (apel (elttyeq p q) x))
elttyeq-lm {Γ} {a} {A} {B} p q x = memV-right-ext-lm2 (apr a x) (apt A x) (apt B x) (apel p x) (>><< (ape q x))


elttyeq-lm2 :  {Γ : ctx} ->  {a : raw Γ}  -> {A B : ty Γ}
      -> (p : Γ ==> a :: A)     -> (q : Γ ==> A == B)
      -> (x : || κ Γ ||)
      ->  (apr a x) ≐ (apt B x) ‣ (e+ (>><< (ape q x)) (pj1 (apel p x)))

elttyeq-lm2 {Γ} {a} {A} {B} p q x = memV-right-ext-lm2 _ _ _ (apel p x) (>><< (ape q x))




-- The other cruical type equality rule is verified

elteqtyeq :  {Γ : ctx} ->  (a b : raw Γ)  -> (A B : ty Γ)
--
      -> Γ ==>  a == b :: A    -> Γ ==> A == B
--  ---------------------------------------------
              -> Γ ==>  a == b :: B
--
elteqtyeq a b A B p q = pair (prj1 p)
                              (pair (elttyeq (prj1 (prj2 p)) q)
                                    (elttyeq (prj2 (prj2 p)) q))




-- Notation for substitution in to terms


sub : {Δ Γ : ctx}  -> raw Γ ->  subst Δ Γ -> raw Δ
sub a f = mkraw (comp1 (raw.rawterm a) (subst.cmap f))



infix 12 _[_]

_[_] : {Δ Γ : ctx}  -> raw Γ ->  subst Δ Γ -> raw Δ
a [ f ] = sub a f

sub-apply : {Δ Γ : ctx}
     -> (a : raw Γ) ->  (f : subst Δ Γ) -> (x : || κ Δ ||)
     -> apr (a [ f ]) x ≐ apr a (aps f x)
sub-apply a f x = refV _

-- Notation for substitution in to types


Sub : {Δ Γ : ctx}  -> ty Γ -> subst Δ Γ -> ty Δ
Sub A f =  tyy (comp1 (ty.type A) (subst.cmap f))


infix 12 _[[_]]

_[[_]] : {Δ Γ : ctx}  -> ty Γ -> subst Δ Γ -> ty Δ
A [[ f ]] = Sub A f

-- (Really want to use _[_] for this as well.)

Sub-apply : {Δ Γ : ctx}
     -> (A : ty Γ) ->  (f : subst Δ Γ) -> (x : || κ Δ ||)
     -> apt (A [[ f ]]) x ≐ apt A (aps f x)
Sub-apply a f x = refV _



-- Functorial properties of substitutions for raw terms

sub-id-prop : {Γ : ctx}
       -> (a : raw Γ)
-- ------------------------------------
       ->   << Raw Γ >> a [ ids ] ~ a
--
sub-id-prop {Γ} a = <<>> (<<>> ((λ x → refl' VV _)))

sub-comp-prop : {Θ Δ Γ : ctx}
       -> (a : raw Γ)
       ->  (f : subst Δ Γ) -> (g : subst Θ Δ)
-- ---------------------------------------------------
       -> << Raw Θ >>  a [ f ⌢ g ]  ~ (a [ f ] [ g ])
--
sub-comp-prop a f g = <<>> (<<>> ( λ x → refl' VV _))

-- substitutions from a context equalities and their properties


-- use   ϕ \varphi for this  - to change **

subst-trp : {Γ Δ : ctx} ->  (p : << Ctx >> Γ ~ Δ) -> subst Γ Δ
subst-trp {Γ} {Δ} p = subst.sb (ctx-trp {Γ} {Δ} (>><< p))



sub-trp-prop : {Γ : ctx}  -> (a : raw Γ)
       ->  (p : << Ctx >> Γ ~ Γ)
-- --------------------------------------------
       -> << Raw Γ >> a [ subst-trp p ]  ~ a
--
sub-trp-prop {Γ} a p =
  <<>> (<<>> (λ x → (let lm : << VV >> apr a (ap (ctx-trp (>><< p)) x) ~ (apr a  x)
                         lm = extensionality1 (raw.rawterm a) (ap (ctx-trp (>><< p)) x) x (κ-trp-id (>><< p) x)
                      in lm)))




-- Functorial properties of substitutions for types


Sub-id-prop : {Γ : ctx}
           -> (A : ty Γ)
-- -----------------------------------
      ->  << Ty Γ >> A [[ ids ]] ~ A
--
Sub-id-prop {Γ} A = <<>> (<<>> (λ x → refl' VV (apt A  x)))

Sub-id-prop-sym : {Γ : ctx}
           -> (A : ty Γ)
-- -----------------------------------
      ->  << Ty Γ >> A [[ ids ]] ~ A
--
Sub-id-prop-sym {Γ} A = sym' (Sub-id-prop {Γ} A)

Sub-comp-prop : {Θ Δ Γ : ctx}
       -> (A : ty Γ)  ->  (f : subst Δ Γ) -> (g : subst Θ Δ)
-- -----------------------------------------------------------
      -> << Ty Θ >>  A [[ f ⌢ g ]]  ~ (A [[ f ]] [[ g ]])
--
Sub-comp-prop {Θ} {Δ} {Γ} A f g = <<>> (<<>> (λ x → refl' VV (apt (Sub {Θ} {Δ} (Sub {Δ} {Γ} A f) g) x)))


Sub-comp-prop-sym : {Θ Δ Γ : ctx}
       -> (A : ty Γ)
       ->  (f : subst Δ Γ) -> (g : subst Θ Δ)
-- -----------------------------------------------------------
    -> << Ty Θ >>   (A [[ f ]] [[ g ]]) ~ (A [[ f ⌢ g ]])
Sub-comp-prop-sym {Θ} {Δ} {Γ} A f g = sym' (Sub-comp-prop {Θ} {Δ} {Γ} A f g )



-- substitutions from a context equalities and their properties

Sub-trp-prop : {Γ : ctx}  -> (A : ty Γ) ->  (p : << Ctx >> Γ ~ Γ) ->
       << Ty Γ >> A [[ subst-trp p ]]  ~ A
Sub-trp-prop A p   = <<>> (<<>> (λ x →
                         let lm : << VV >> (apt A (ap (ctx-trp (>><< p)) x)) ~ (apt A  x)
                             lm = extensionality1 (ty.type A) (ap (ctx-trp (>><< p)) x) x (κ-trp-id (>><< p) x)
                             main :  << VV >> (apt (Sub A (subst-trp p))  x) ~ (apt A  x)
                             main = lm
                         in main))




-- Application of substitutions to judgements


tyeq-subst :  {Δ Γ : ctx} -> {A B : ty Γ} -> (f : subst Δ Γ)
--
                  -> Γ ==> A == B
--      --------------------------------------------------
         -> Δ ==> A [[ f ]] ==  B [[ f ]]
--
tyeq-subst f p = mk-eqty (λ x → (ape p (aps f x)))



elt-subst :  {Δ Γ : ctx} -> {a : raw Γ} -> {A : ty Γ} -> (f : subst Δ Γ)
--
         -> Γ ==> a :: A
--   --------------------------------------------------------
         -> Δ ==> a [ f ] ::  A [[ f ]]
--
elt-subst f p = mk-elt (λ x → apel p (aps f x))



elteq-subst :  {Δ Γ : ctx} -> {a b : raw Γ} -> {A : ty Γ} -> (f : subst Δ Γ)
--
         -> Γ ==> a == b :: A
--   --------------------------------------------------------------------------
         -> Δ ==> a [ f ] == b [ f ] :: A [[ f ]]
--

elteq-subst f p = pair (\x -> prj1 p (aps f x))
                                 (pair (elt-subst f (prj1 (prj2 p)))
                                       (elt-subst f (prj2 (prj2 p))))




-- equality judgements from raw equalities

tyeq-from-eq : {Γ : ctx} -> (A B : ty Γ)
     ->  << Ty Γ >> A  ~ B
--   -------------------------
     -> Γ ==> A == B
tyeq-from-eq A B p =  mk-eqty (λ x →  >><<  (>><< p) x)



elteq-from-eq : {Γ : ctx} -> (A : ty Γ) ->  (a b : raw Γ)
     -> Γ ==> a :: A   -> Γ ==> b :: A   ->  << Raw Γ >> a ~ b
--   -------------------------
     -> Γ ==> a == b :: A
elteq-from-eq A a b p q r =  pair (λ x → >><< (>><< (>><< r) x))
                                  (pair p q)

-- and the reverse rules

eq-from-tyeq : {Γ : ctx} -> (A B : ty Γ)
       -> Γ ==> A == B
--   -------------------------
     ->  << Ty Γ >> A  ~ B
eq-from-tyeq {Γ} A B p = <<>> (<<>> (λ x → ape p x))


eq-from-elteq : {Γ : ctx} -> (A : ty Γ) ->  (a b : raw Γ)
      -> Γ ==> a == b :: A
--   -------------------------
     ->  << Raw Γ >> a ~ b
eq-from-elteq {Γ} A a b r = <<>> (<<>> (λ x → <<>> (prj1 r x)))


tyeq-subst2 :  {Δ Γ : ctx} -> (A : ty Γ) -> (f g : subst Δ Γ)
--
                  -> < Subst Δ Γ > f ~ g
--      --------------------------------------------------
         -> Δ ==> A [[ f ]] ==  A [[ g ]]
--
tyeq-subst2 A f g p = mk-eqty (\x -> (extensionality1 (ty.type A) (aps f x) (aps g x) ( (>< (>< p)) x)))



elteq-subst2 :  {Δ Γ : ctx} -> {a  : raw Γ} -> {A : ty Γ} -> (f  g : subst Δ Γ)
--
           -> Γ ==> a :: A
           -> < Subst Δ Γ > f ~ g
--   --------------------------------------------------------------------------
         -> Δ ==> a [ f ] == a [ g ] :: A [[ f ]]
--
elteq-subst2 {Δ} {Γ} {a} {A} f g p q = pair (λ x → >><< ( extensionality1 (raw.rawterm a) (aps f x) (aps g x)  ( (>< (>< q)) x)))
                                            (pair (elt-subst f  p)
                                                  (elttyeq (elt-subst g  p) (tysym (tyeq-subst2 A f g q))))



tysubst-id : {Γ : ctx}
    -> (A  : ty Γ)
--   -------------------------
     -> Γ ==> (A [[ ids ]]) == A
--
tysubst-id A = tyeq-from-eq (A [[ ids ]]) A (Sub-id-prop A)

tysubst-id-sym : {Γ : ctx}
    -> (A  : ty Γ)
--   -------------------------
     -> Γ ==> A == (A [[ ids ]])
--
tysubst-id-sym A = tysym (tysubst-id A)


tysubst-com : {Θ Δ Γ : ctx}
    -> (A : ty Γ)    -> (f : subst Δ Γ)  -> (g : subst Θ Δ)
--   -------------------------
     -> Θ ==> (A [[ f ⌢ g ]]) == (A [[ f ]] [[ g ]])
--
tysubst-com  A f g =  tyeq-from-eq (A [[ f ⌢ g ]]) (A [[ f ]] [[ g ]])
                           (Sub-comp-prop A f g)




eltsubst-id : {Γ : ctx}
    -> (A  : ty Γ)  ->  (a : raw Γ)  -> Γ ==> a :: A
--   ---------------------------
     -> Γ ==> (a [ ids ]) == a :: A
--
eltsubst-id {Γ} A a p = elteq-from-eq A (a [ ids ]) a (elttyeq (elt-subst ids p) (tysubst-id A)) p (sub-id-prop a)




eltsubst-com : {Θ Δ Γ : ctx}
    -> (A : ty Γ)
    -> (f : subst Δ Γ)  -> (g : subst Θ Δ)
    -> (a : raw Γ)
    -> Γ ==> a :: A
--   -------------------------
     -> Θ ==> (a [ f ⌢ g ]) == (a [ f ] [ g ]) :: (A [[ f ⌢ g ]])
--
eltsubst-com {Θ} {Δ} {Γ} A f g a p = elteq-from-eq (A [[ f ⌢ g ]]) (a [ f ⌢ g ]) ((a [ f ]) [ g ])
                                      (elt-subst (f ⌢ g) p) (elttyeq (elt-subst g (elt-subst f p)) (tysym (tysubst-com A f g))) (sub-comp-prop a f g)



-- a form of subject reduction

subj-red : {Γ : ctx} -> {A : ty Γ} ->  (a b : raw Γ)
     -> Γ ==> a :: A    ->  << Raw Γ >> a ~ b
--   -------------------------
     -> Γ ==> b :: A
subj-red {Γ} {A} a b p q =  mk-elt (λ x →    memV-left-ext (apr b x) (apr a x) (apt A x) (symV (>><< (>><< (>><< q) x))) (apel p x) )


-- useful for proving

elteq-from-eq2 : {Γ : ctx} -> (A : ty Γ) ->  (a b : raw Γ)
     -> Γ ==> a :: A    ->  << Raw Γ >> a ~ b
--   -------------------------
     -> Γ ==> a == b :: A
elteq-from-eq2 {Γ} A a b p q  = elteq-from-eq {Γ} A a b p (subj-red {Γ} {A} a b p q) q







-- useful coercing lemma

A-Aid :  {Γ : ctx} ->  {a : raw Γ}  -> {A  : ty Γ}
--
              -> Γ ==> a :: A
--  --------------------------------------------
              -> Γ ==> a :: A [[ ids ]]
A-Aid {Γ} {a} {A} p = elttyeq p (tysubst-id-sym A)
