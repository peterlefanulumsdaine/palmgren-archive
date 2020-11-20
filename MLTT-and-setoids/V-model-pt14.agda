-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt14 where

open import basic-types
open import basic-setoids       -- 525 lines
open import dependent-setoids   -- 559 lines
open import subsetoids          -- 341 lines
open import iterative-sets      -- 869 lines
open import iterative-sets-pt2  -- 326 lines
open import iterative-sets-pt3  -- 439 lines
open import iterative-sets-pt4
open import iterative-sets-pt5
open import iterative-sets-pt6
open import V-model-pt0
open import V-model-pt1         -- 776 lines
open import V-model-pt2         -- 511 lines
open import V-model-pt3         -- 522 lines
open import V-model-pt4         -- 283 lines
open import V-model-pt5         -- 225 lines
open import V-model-pt6         -- 842 lines
open import V-model-pt7         --  66 lines
open import V-model-pt8         -- 134 lines
open import V-model-pt9         -- 441 lines
open import V-model-pt10
open import V-model-pt13

-- universe operator

-- experimental version of the universe axiom
-- if successful replace:  V-model-pt11.agda

U-n : (Γ : ctx)  -> (I : ty Γ) -> (F : ty (Γ ▷ I)) -> ty Γ
U-n Γ I F = {!!}

T-n : {Γ : ctx}  -> (I : ty Γ) -> (F : ty (Γ ▷ I)) -> (A : raw Γ)
     -> (Γ ==> A :: U-n Γ I F)
-- --------------------------
     -> ty Γ
T-n {Γ} I F A p = {!!}

T-n-Russell-eq :  {Γ : ctx}  -> (I : ty Γ) -> (F : ty (Γ ▷ I)) -> (A : raw Γ)
     -> (p : Γ ==> A :: U-n Γ I F)
-- -------------------------------
     ->  Γ ==> T-n I F A p == A
--
T-n-Russell-eq {Γ} I F A p = {!!}


U-n-ix : {Γ : ctx}  -> (I : ty Γ) -> (F : ty (Γ ▷ I))
-- ------------------------------
     -> (Γ ==> I :: U-n Γ I F)
--
U-n-ix {Γ} i F = {!!}

U-n-fm : {Γ : ctx}  -> (I : ty Γ) -> (F : ty (Γ ▷ I))
--
     -> (i : raw Γ)
     -> (p : Γ ==> i :: I)
-- -------------------------------------
     -> (Γ ==> F [ els p ] :: U-n Γ I F)
U-n-fm {Γ} i F = {!!}


-- constant type


U-f  :  (Γ : ctx)  -> ty Γ
U-f  Γ = Const uV  Γ

T-f : {Γ : ctx}  -> (A : raw Γ)
     -> (Γ ==> A :: U-f Γ)
-- --------------------------
     -> ty Γ
T-f {Γ} A p = A  -- tyy (raw.rawterm A)

T-f-Russell-eq :  {Γ : ctx}  -> (A : raw Γ)
     -> (p : Γ ==> A :: U-f Γ)
-- -------------------------------
     ->  Γ ==> T-f A p == A
--
T-f-Russell-eq {Γ} A p = tyrefl A

U-f-sub :  (Δ Γ : ctx)  -> (f : subst Δ Γ)
     ->  Δ ==> (U-f Γ) [[ f ]] == U-f Δ
U-f-sub Δ Γ f = mk-eqty (λ x → <<>> (refV _))


natU : (Γ : ctx) -> raw Γ
natU Γ = mkraw (record { op = λ x → natV
                       ; ext = λ x y p → refl' _ _
                       })


U-f-nat : (Γ : ctx)
-- -----------------------------------
    -> Γ ==> natU Γ :: U-f Γ
--
U-f-nat Γ = mk-elt (λ x → nat-sV , (symV emb-nat))

T-f-nat : (Γ : ctx)
-- ------------------------------------------------------
      -> Γ ==> T-f (natU Γ) (U-f-nat Γ) == Nat Γ
--
T-f-nat Γ = mk-eqty (λ x → <<>> (traV (easy-eqV _ _ _ (λ y → symV (nat-sV-V y))) emb-nat))


U-f-Russell-nat : (Γ : ctx)
-- -----------------------------------
    -> Γ ==> Nat Γ :: U-f Γ
--
U-f-Russell-nat Γ = mk-elt (λ x → natV-in-uV)


{--
natV-in-uV : natV ∈ uV
natV-in-uV = nat-sV , symV emb-nat

--}


-- sigma-sV


U-f-Russell-sigma-lm : {Γ : ctx}
    ->  (A : ty Γ)
    ->  (p : Γ ==> A :: U-f Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U-f Γ [[ ↓ A ]])
    ->  (x :  || κ Γ ||)
    ->  apr (Σ-f A B) x ∈ uV
U-f-Russell-sigma-lm {Γ} A p B q x =
  let lm : (apt (Σ-f A B) x) ≐ sigmaV (apt A x) (mk-Par-op-Fx A B x)
      lm = Σ-f-exp1 {Γ} A B x
      lm2 : sigmaV (apt A x) (mk-Par-op-Fx A B x) ∈ uV
      lm2 = sigmaV-reflection (apt A x) (mk-Par-op-Fx A B x)
                  (apel p x) (λ y → apel q (x , y))
      main : apr (Σ-f A B) x ∈ uV
      main = memV-left-ext (apr (Σ-f A B) x)  _ uV  lm lm2
  in main

U-f-Russell-sigma : {Γ : ctx}
    ->  (A : ty Γ)
    ->  (p : Γ ==> A :: U-f Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U-f Γ [[ ↓ A ]])
    ->  Γ ==> Σ-f A B :: U-f Γ
U-f-Russell-sigma {Γ} A p B q
    = mk-elt (U-f-Russell-sigma-lm {Γ} A p B q)

{--

sigmaV-reflection : (a : V) -> (g :  setoidmap1 (κ a) VV)
    -> (a ∈ uV)
    -> ((x : || κ a ||) -> ap1 g x ∈ uV)
    -> sigmaV a g ∈ uV

Σ-f-exp1 :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       ->  (apt (Σ-f A B)  u) ≐ sigmaV (apt A u) (mk-Par-op-Fx A B u)
Σ-f-exp1 A B u = refV _

--}

U-f-Russell-pi-lm : {Γ : ctx}
    ->  (A : ty Γ)
    ->  (p : Γ ==> A :: U-f Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U-f Γ [[ ↓ A ]])
    ->  (x :  || κ Γ ||)
    ->  apr (Π-f A B) x ∈ uV
U-f-Russell-pi-lm {Γ} A p B q x =
  let lm : (apt (Π-f A B) x) ≐ piV (apt A x) (mk-Par-op-Fx A B x)
      lm = Π-f-exp1 {Γ} A B x
      lm2 : piV (apt A x) (mk-Par-op-Fx A B x) ∈ uV
      lm2 = piV-reflection (apt A x) (mk-Par-op-Fx A B x)
                  (apel p x) (λ y → apel q (x , y))
      main : apr (Π-f A B) x ∈ uV
      main = memV-left-ext (apr (Π-f A B) x)  _ uV  lm lm2
  in main

U-f-Russell-pi : {Γ : ctx}
    ->  (A : ty Γ)
    ->  (p : Γ ==> A :: U-f Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U-f Γ [[ ↓ A ]])
    ->  Γ ==> Π-f A B :: U-f Γ
U-f-Russell-pi {Γ} A p B q  = mk-elt (U-f-Russell-pi-lm {Γ} A p B q)



U-f-Russell-ID-lm : {Γ : ctx}
     -> (A : ty Γ)
     -> (p : Γ ==> A :: U-f Γ)
     -> (a : raw Γ)
     -> (qa : Γ ==> a :: A)
     -> (b : raw Γ)
     -> (qb : Γ ==> b :: A)
     -> (x : || κ Γ ||)
     -> apr (ID A a qa b qb) x ∈ uV
U-f-Russell-ID-lm {Γ} A p a qa b qb x =
  let p2 = pj2 (apel p x)
      qa2 : apr a x ≐ apt A x ‣ pj1 (apel qa x)
      qa2 = pj2 (apel qa x)
      qb2 : apr b x ≐ apt A x ‣ pj1 (apel qb x)
      qb2 = pj2 (apel qb x)
      lm : apr (ID A a qa b qb) x ≐ sup ((apr a x) ≐ (apr b x)) (\u -> apr a x)
      lm = refV _
      lm2 :  sup ((apr a x) ≐ (apr b x)) (\u -> apr a x)
              ≐ idV (apt A x) (pj1 (apel qa x)) (pj1 (apel qb x))
      lm2 = pair (λ r → traV (symV qa2) (traV r qb2) , qa2)
                 (λ r → traV qa2 (traV r (symV qb2)) , qa2)
      main : apr (ID A a qa b qb) x ∈ uV
      main = memV-left-ext (apr (ID A a qa b qb) x) (idV (apt A x) (pj1 (apel qa x)) (pj1 (apel qb x))) uV
               (traV lm lm2)
               (idV-reflection (apt A x) (pj1 (apel qa x)) (pj1 (apel qb x)) (apel p x))
  in main


U-f-Russell-ID : {Γ : ctx}
     -> (A : ty Γ)
     -> (p : Γ ==> A :: U-f Γ)
     -> (a : raw Γ)
     -> (qa : Γ ==> a :: A)
     -> (b : raw Γ)
     -> (qb : Γ ==> b :: A)
     -> Γ ==> ID A a qa b qb :: U-f Γ
U-f-Russell-ID {Γ} A p a qa b qb = mk-elt (U-f-Russell-ID-lm {Γ} A p a qa b qb)

U-f-Russell-N0 : {Γ : ctx}
      -> Γ ==> N0 Γ :: U-f Γ
U-f-Russell-N0 {Γ} = mk-elt (λ x →  zeroV-reflection)

U-f-Russell-Sum-lm : {Γ : ctx}
    ->  (A B : ty Γ)
    ->  (p : Γ ==> A :: U-f Γ)
    ->  (q : Γ ==> B :: U-f Γ)
    ->  (x :  || κ Γ ||)
    ->  apr (Sum A B) x ∈ uV
U-f-Russell-Sum-lm {Γ} A B p q x =
  let  lm : (apt (Sum A B) x) ≐ sumV (apt A x) (apt B x)
       lm = refV _
       lm2 : sumV (apt A x) (apt B x) ∈ uV
       lm2 = sumV-reflection (apt A x) (apt B x) (apel p x) (apel q x)
       main : apr (Sum A B) x ∈ uV
       main = memV-left-ext (apr (Sum A B) x)  _ uV  lm lm2
  in main

U-f-Russell-Sum : {Γ : ctx}
    ->  (A B : ty Γ)
    ->  (p : Γ ==> A :: U-f Γ)
    ->  (q : Γ ==> B :: U-f Γ)
    ->  Γ ==> Sum A B :: U-f Γ
U-f-Russell-Sum {Γ} A B p q
    = mk-elt (U-f-Russell-Sum-lm {Γ} A B p q)
