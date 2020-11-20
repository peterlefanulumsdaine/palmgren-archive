-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt12 where

open import basic-types
open import basic-setoids       -- 525 lines
open import dependent-setoids   -- 559 lines
open import subsetoids          -- 341 lines
open import iterative-sets      -- 869 lines
open import iterative-sets-pt2  -- 326 lines
open import iterative-sets-pt3  -- 439 lines
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
-- total:                         6859 lines

-- quotient types


Quot : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> ty Γ
Quot {Γ} A R = {!!}

quot : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> raw Γ
quot {Γ} A R a p = {!!}

Quot-i : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> Γ ==> quot {Γ} A R a p :: Quot {Γ} A R
Quot-i {Γ} A R a p = {!!}

{--
els2-lm : {Γ : ctx}
    -> {A : ty Γ}
    -> {a  : raw Γ}
    -> (p : Γ ==> a :: A)
    -> <
--}

els2-lm :  {Γ : ctx}
    -> {A : ty Γ}
    -> {a  : raw Γ}
    -> (p : Γ ==> a :: A)
    -> Γ ==> A == (A [[ ↓ A ]]) [[ els p ]]
els2-lm {Γ} {A} {a} p = {!!}

els2 : {Γ : ctx}
    -> {A : ty Γ}
    -> {a a' : raw Γ}
    -> (p : Γ ==> a :: A)
    -> (p' : Γ ==> a' :: A)
    -> subst Γ  (Γ ▷ A ▷ (A [[ ↓ A ]]))
els2 {Γ} {A} {a} {a'} p p' = ext  (A [[ ↓ A ]]) (els p) a' (elttyeq p' (els2-lm p))

{--

elttyeq :  {Γ : ctx} ->  {a : raw Γ}  -> {A B : ty Γ}
--
      -> Γ ==> a :: A     -> Γ ==> A == B
--  --------------------------------------------
              -> Γ ==> a :: B

ext : {Δ Γ : ctx} -> (A : ty Γ)
      ->  (f : subst Δ Γ) -> (a : raw Δ)
      -> Δ ==> a :: A [[ f ]]
      -> subst Δ (Γ ▷ A)
ext {Δ} {Γ} A f a p = sb (record { op = ext-op A f a p
                                       ; ext = ext-ext A f a p })
--}

omicron : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> (a a' : raw Γ)
   -> (p : Γ ==> a :: A)
   -> (p' : Γ ==> a' :: A)
   -> (r : raw Γ)
   -> (q : Γ ==> r ::  R [[ els2 p p' ]])
   -> raw Γ
omicron {Γ} A R a a' p p' r q = {!!}

Quot-ID-exd : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> (a a' : raw Γ)
   -> (p : Γ ==> a :: A)
   -> (p' : Γ ==> a' :: A)
   -> (r : raw Γ)
   -> (q : Γ ==> r :: R [[ els2 p p' ]])
   -> Γ ==> omicron {Γ} A R a a' p p' r q
        :: ID (Quot {Γ} A R) (quot {Γ} A R a p) (Quot-i {Γ} A R a p)
                             (quot {Γ} A R a' p') (Quot-i {Γ} A R a' p')
Quot-ID-exd {Γ} A R a a' p p' r q = {!!}

quot-subst : {Γ : ctx}
       -> (A : ty Γ)
       -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
       -> subst (Γ ▷ A) (Γ ▷ Quot A R)
quot-subst {Γ} A R = {!!}


QE-op : {Γ : ctx}
       -> (A : ty Γ)
       -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
       -> (P : ty (Γ ▷ (Quot {Γ} A R)))
       -> (d : raw (Γ ▷ A))
       -> (p : Γ ▷ A ==> d :: P [[ quot-subst A R ]])
       -> (e : raw (Γ ▷ A ▷ (A [[ ↓ A ]]) ▷ R))
       -- need transport here
       -> (q : Γ ▷ A ▷ (A [[ ↓ A ]]) ▷ R ==>
                 e :: ID (P [[ quot-subst A R ]] [[ ↓ (A [[ ↓ A ]]) ]] [[ ↓ R ]] )
                        ( d  [ ↓ (A [[ ↓ A ]]) ] [ ↓ R ] ) {!!} {!!} {!!})
       -> (c : raw Γ)
       -> (r : Γ ==> c :: (Quot {Γ} A R))
       -> raw Γ
QE-op = {!!}

Quot-e  : {Γ : ctx}
       -> (A : ty Γ)
       -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
       -> (P : ty (Γ ▷ (Quot {Γ} A R)))
       -> (d : raw (Γ ▷ A))
       -> (p : Γ ▷ A ==> d :: P [[ {!!} ]])
       -> (e : raw (Γ ▷ A ▷ (A [[ ↓ A ]]) ▷ R))
       -> (q : Γ ▷ A ▷ (A [[ ↓ A ]]) ▷ R ==> e :: ID {!!} {!!} {!!} {!!} {!!})
       -> (c : raw Γ)
       -> (r : Γ ==> c :: (Quot {Γ} A R))
       -> Γ ==> QE-op {Γ} A R P d p e q c r :: P [[ els r ]]
Quot-e = {!!}
