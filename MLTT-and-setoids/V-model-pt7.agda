-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt7 where

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

-- general congruence for Pi-formation



ext-eq' : {Γ : ctx}
--
      -> (A  A' : ty Γ)
      -> (Γ ==> A == A')
-- --------------------------
     -> << Ctx >> (Γ ▷ A) ~ (Γ ▷ A')
ext-eq' {Γ} A A' p = <<>> (ext-eq {Γ} A A' p) --  <<>> (ext-eq' {Γ} A A' p)




ext-eq-lm' : {Γ : ctx}
      -> (A  A' : ty Γ)
      -> (p : Γ ==> A == A')
      -> (x : || κ Γ ||)
      -> (y : || κ (apt A x)||)
      -> < κ (Γ ▷ A') > aps (subst-trp (ext-eq' A A' p)) (x , y) ~ (x , (ap (κ-Fam ±± ape p x) y))
ext-eq-lm' {Γ} A A' p x y = refl _ _


mk-Par-cong :  {Γ : ctx}
            -> (A  A' : ty Γ)
            -> (p : Γ ==> A == A')
            -> (B : ty (Γ ▷ A))
            -> (B' : ty (Γ ▷ A'))
            -> (Γ ▷ A ==> B == (B' [[  subst-trp (ext-eq' A A' p) ]]))
            -> (x : || κ Γ ||)
            ->  << Par VV κ-Fam >>  ap1 (mk-Par A B) x ~ ap1 (mk-Par  A' B') x
mk-Par-cong {Γ} A A' p B B' q x = <<>>
  (
          (ape p x) ,
          (λ y →
                 let
                     q1 = ape q (x , y)
                     eq2 = (ext-eq' A A' p)
                     eq :  < κ (Γ ▷ A') >
                              aps (subst-trp eq2) (x , y) ~  (x , ap (κ-Fam ±± ape p x) y)
                     eq =  ext-eq-lm {Γ} A A' p x y --  <> (ext-eq-lm {Γ} A A' p x y)


                     lm :  apt (B' [[ subst-trp (ext-eq' A A' p) ]]) (x , y) ≐
                           Fxx (ap1 (mk-Par A' B') x) • ap (κ-Fam ±± ape p x) y
                     lm = >><< (extensionality1 (ty.type B') _ _ eq)
                     main : << VV >> Fxx (ap1 (mk-Par A B) x) • y ~
                                 (Fxx (ap1 (mk-Par A' B') x) • ap (κ-Fam ±± ape p x) y)
                     main = <<>> (traV (>><< q1) lm)
                 in main)
   )




Π-f-cong : {Γ : ctx}
--
      -> (A  A' : ty Γ)
      -> (p : Γ ==> A == A')
      -> (B : ty (Γ ▷ A))
      -> (B' : ty (Γ ▷ A'))
      -> (Γ ▷ A ==> B == (B' [[  subst-trp (ext-eq' A A' p) ]]))
-- ---------------------
      -> Γ ==> Π-f A B == Π-f A' B'
Π-f-cong {Γ} A A' p B B' q  = mk-eqty (λ x → let lm = mk-Par-cong  {Γ} A A' p B B' q x
                                              in extensionality11 piVV (ap1 (mk-Par A B) x) (ap1 (mk-Par  A' B') x) lm)

