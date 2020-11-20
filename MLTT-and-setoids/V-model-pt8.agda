-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt8 where

open import basic-types
open import basic-setoids       -- 525 lines
open import dependent-setoids   -- 559 lines
open import subsetoids          -- 341 lines
open import iterative-sets      -- 869 lines
open import iterative-sets-pt2  -- 326 lines
open import iterative-sets-pt3  -- 439 lines
open import V-model-pt0
open import V-model-pt1         -- 685 lines
open import V-model-pt2         -- 511 lines
open import V-model-pt3         -- 522 lines
open import V-model-pt4         -- 283 lines
open import V-model-pt5         -- 225 lines
open import V-model-pt6         -- 853 lines
open import V-model-pt7         -- 853 lines


-- Extensional identity types


ID-op : {Γ : ctx}
     -> (A : ty Γ) -> (a b : raw Γ) -> (x : || κ Γ ||) -> V
ID-op {Γ} A a b x = sup ((apr a x) ≐ (apr b x)) (\u -> apr a x)

ID-lm : {Γ : ctx}
     -> (A : ty Γ) -> (a b : raw Γ)
     -> (x y : || κ Γ ||)
     -> (< κ Γ > x ~ y)
     -> ID-op A a b x ⊆ ID-op A a b y
ID-lm {Γ} A a b x y q =
                                          (λ z p → let p1 : # (ID-op A a b x)
                                                       p1 = pj1 p
                                                       eq : (apr a x) ≐ (apr b x)
                                                       eq = p1
                                                       eq2 : (apr a y) ≐ (apr b y)
                                                       eq2 = traV (symV (>><< (extensionality1 (raw.rawterm a) x y q)))
                                                                        (traV eq (>><< (extensionality1 (raw.rawterm b) x y q)))
                                                       p2 : z ≐ ID-op A a b x ‣ pj1 p
                                                       p2 = pj2 p
                                                       lm :  z ∈ ID-op A a b y
                                                       lm = eq2 , traV p2 (>><< (extensionality1 (raw.rawterm a) x y q))
                                                   in lm
                                          )

ID-untyped : {Γ : ctx}
     -> (A : ty Γ) -> (a b : raw Γ)
     -> ty Γ
ID-untyped {Γ} A a b = tyy (record { op = ID-op {Γ} A a b
                           ; ext = λ x y q → <<>> (extensional-eqV (ID-op A a b x) (ID-op A a b y)
                                                     (ID-lm {Γ} A a b x y q)
                                                     (ID-lm {Γ} A a b y x (sym {κ Γ} q)))

                           })




-- formation rule for identity type

ID : {Γ : ctx}
     -> (A : ty Γ)
     -> (a : raw Γ)
     -> (p : Γ ==> a :: A)
     -> (b : raw Γ)
     -> (q : Γ ==> b :: A)
     -> ty Γ
ID {Γ} A a p b q = tyy (record { op = ID-op {Γ} A a b
                           ; ext = λ x y q → <<>> (extensional-eqV (ID-op A a b x) (ID-op A a b y)
                                                    (ID-lm {Γ} A a b x y q)
                                                    (ID-lm {Γ} A a b y x (sym {κ Γ} q)))

                           })



rr-op : {Γ : ctx}
     -> (a : raw Γ)
     -> (x : || κ Γ ||) -> V
rr-op {Γ} a x =  apr a x

rr :  {Γ : ctx}
     -> (a : raw Γ)
     -> raw Γ
rr {Γ} a = mkraw (record { op = rr-op {Γ} a
                         ; ext = λ x y p →  (extensionality1 (raw.rawterm a) x y p) })




-- introduction rule - reflexivity

ID-i : {Γ : ctx}
     -> (A : ty Γ)
     -> (a : raw Γ)   -> (p : Γ ==> a :: A)
-- -----------------------
     -> Γ ==> (rr {Γ} a) :: (ID A a p a p)
--
ID-i {Γ} A a p  = mk-elt (λ x → (refV (apr a x)) , (refV (apr (rr a) x)))



-- reflection rule
ID-e : {Γ : ctx}
     -> (A : ty Γ)
     -> (a b t : raw Γ)
     -> (p : Γ ==> a :: A)
     -> (q : Γ ==> b :: A)
     -> (Γ ==> t :: (ID A a p b q))
-- ---------------------------------
     -> Γ ==> a == b :: A
--
ID-e {Γ} A a b t p q r = pair (λ x → pj1 (apel r x)) (pair p q)

-- uniqueness of identity proofs
ID-uip : {Γ : ctx}
     -> (A : ty Γ)
     -> (a b t : raw Γ)
     -> (p : Γ ==> a :: A)
     -> (r : Γ ==> a :: A)
     -> (Γ ==> t :: (ID A a p a r))
-- ---------------------------------------------
     -> Γ ==> t == (rr {Γ} a) :: (ID A a p a r)
--
ID-uip {Γ} A a b t p r q = pair (λ x → pj2 (apel q x)) (pair q (ID-i {Γ} A a p))






-- substitution rule for ID

ID-sub :  {Δ Γ : ctx}
     -> (h : subst Δ Γ)
     -> (A : ty Γ)
     -> (a : raw Γ)
     -> (pa : Γ ==> a :: A)
     -> (b : raw Γ)
     -> (pb : Γ ==> b :: A)
     -> << Ty Δ >> (ID A a pa b pb) [[ h ]] ~ (ID (A [[ h ]]) (a [ h ]) (elt-subst h pa) (b [ h ]) (elt-subst h pb))
ID-sub {Δ} {Γ} h A a pa b pb = <<>> (<<>> (λ x → <<>>  (refV _)))



ID-sub-gen' :  {Δ Γ : ctx}
     -> (h : subst Δ Γ)
     -> (A : ty Γ)
     -> (a : raw Γ)
     -> (pa : Γ ==> a :: A)
     -> (b : raw Γ)
     -> (pb : Γ ==> b :: A)
     -> (q : Δ ==> a [ h ] :: A [[ h ]])
     -> (r : Δ ==> b [ h ] :: A [[ h ]])
     -> << Ty Δ >> (ID A a pa b pb) [[ h ]] ~ (ID (A [[ h ]]) (a [ h ]) q (b [ h ]) r)
ID-sub-gen' {Δ} {Γ} h A a pa b pb q r =  <<>> (<<>> (λ x → <<>>  (refV _)))

ID-sub-gen :  {Δ Γ : ctx}
     -> (h : subst Δ Γ)
     -> (A : ty Γ)
     -> (a : raw Γ)
     -> (pa : Γ ==> a :: A)
     -> (b : raw Γ)
     -> (pb : Γ ==> b :: A)
     -> (q : Δ ==> a [ h ] :: A [[ h ]])
     -> (r : Δ ==> b [ h ] :: A [[ h ]])
     -> Δ ==>  (ID A a pa b pb) [[ h ]] == (ID (A [[ h ]]) (a [ h ]) q (b [ h ]) r)
ID-sub-gen {Δ} {Γ} h A a pa b pb q r = mk-eqty (λ x → <<>> (refV _))


ID-cong' :  {Γ : ctx}
     -> (A A' : ty Γ)
     -> (a b a' b' : raw Γ)
     -> (<< Ty Γ >> A ~ A')
     -> (<< Raw Γ >> a ~ a')
     -> (<< Raw Γ >> b ~ b')
     -> (pa : Γ ==> a :: A)
     -> (pa' : Γ ==> a' :: A')
     -> (pb : Γ ==> b :: A)
     -> (pb' : Γ ==> b' :: A')
     -> << Ty Γ >> ID A a pa b pb ~  ID A' a' pa' b' pb'
ID-cong' {Γ} A A' a b a' b' p q1 q2 pa pa' pb pb'
    = <<>> (<<>> (λ x → <<>>
      (pair (λ r → traV (symV (>><< (>><< (>><< q1) x))) (traV r (>><< (>><< (>><< q2) x))) , (>><< (>><< (>><< q1) x)))
            (λ r →  traV (>><< (>><< (>><< q1) x)) (traV r (symV (>><< (>><< (>><< q2) x)))) , (>><< (>><< (>><< q1) x))))))



ID-cong :  {Γ : ctx}
     -> (A A' : ty Γ)
     -> (a b a' b' : raw Γ)
     -> (pa : Γ ==> a :: A)
     -> (pa' : Γ ==> a' :: A')
     -> (pb : Γ ==> b :: A)
     -> (pb' : Γ ==> b' :: A')
     -> (q : Γ ==>  A == A')
     -> (Γ ==> a ==  a' :: A')
     -> (Γ ==> b ==  b' :: A')
     -> Γ ==> ID A a pa b pb == ID A' a' pa' b' pb'
ID-cong {Γ} A A' a b a' b' pa pa' pb pb' q r1 r2 =
        tyeq-from-eq (ID A a pa b pb) (ID A' a' pa' b' pb')
                     (ID-cong' {Γ} A A' a b a' b' (<<>> (<<>> (ape q)))
                                                 (<<>> (<<>> (λ x → <<>> (prj1 r1 x))))
                                                 (<<>> (<<>> (λ x → <<>> (prj1 r2 x))))
                                                 pa pa' pb pb' )


rr-sub' :  {Δ Γ : ctx}
     -> (h : subst Δ Γ)
     -> (a : raw Γ)
     -> << Raw Δ >> (rr a) [ h ] ~ rr (a [ h ])
rr-sub' {Δ} {Γ} h a = Raw-lm2 (λ x → refV _)

rr-sub :  {Δ Γ : ctx}
     -> (h : subst Δ Γ)
     -> (A : ty Γ)
     -> (a : raw Γ)
     -> (p : Γ ==> a :: A)
     -> Δ ==> (rr a) [ h ] == rr (a [ h ]) ::  (ID A a p a p) [[ h ]]
rr-sub {Δ} {Γ} h A a p = pair (λ x → refV _)
                               (pair (elt-subst h (ID-i A a p))
                                      (elttyeq (ID-i (A [[ h ]]) (a [ h ]) (elt-subst h p))
                                         (tysym (ID-sub-gen {Δ} {Γ} h A a p a p (elt-subst h p) (elt-subst h p))) ))


rr-cong' :  {Γ : ctx}
     ->  (a  b : raw Γ)
     -> (<< Raw Γ >> a ~ b)
     -> << Raw Γ >> rr a ~ rr b
rr-cong' {Γ} a b p  = p


rr-cong :  {Γ : ctx}
     -> (A : ty Γ)
     -> (a  b : raw Γ)
     -> (p : Γ ==> a :: A)
     -> (Γ ==> a == b :: A)
     -> Γ ==> (rr a) == (rr b) ::  (ID A a p a p)
rr-cong {Γ} A a b p q  = pair (prj1 q) (pair (ID-i A a p) (elttyeq (ID-i A b (prj2 (prj2 q)))
                          (tysym (ID-cong {Γ} A A a a b b p (prj2 (prj2 q)) p (prj2 (prj2 q)) (tyrefl A) q q))))

