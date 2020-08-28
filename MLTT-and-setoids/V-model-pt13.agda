-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt13 where

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
-- total:                         6859 lines

--  binary sum types


 
-- sumV : (a b : V) -> V
-- sumV a b = sup (# a + # b) (bV-sumV a b)

lfV-op : (a b : V) -> || κ a || -> || κ (sumV a b) ||
lfV-op a b x = inl x

lfV-ext : (a b : V) -> (x y : || κ a ||)
        ->  < κ a > x ~ y -> < κ (sumV a b) > lfV-op a b x ~ lfV-op a b y
lfV-ext a b x y p = <> (pairV-ext (refV _) (>< p))  

lfV : (a b : V) -> || (κ a) => (κ (sumV a b)) ||
lfV a b = record { op = lfV-op a b
                 ; ext = lfV-ext a b }



rgV-op : (a b : V) -> || κ b || -> || κ (sumV a b) ||
rgV-op a b y = inr y


rgV-ext : (a b : V) -> (x y : || κ b ||)
        ->  < κ b > x ~ y -> < κ (sumV a b) > rgV-op a b x ~ rgV-op a b y
rgV-ext a b x y p =  <> (pairV-ext (refV _) (>< p))

rgV : (a b : V) -> || (κ b) => (κ (sumV a b)) ||
rgV a b = record { op = rgV-op a b
                 ; ext = rgV-ext a b }



ty-trp-op : {Γ : ctx}
   -> (A : ty Γ)
   -> {x y : || κ Γ ||}
   -> < κ Γ > x ~ y
   -> # (apt A x)
   -> # (apt A y)
ty-trp-op {Γ} A {x} {y} p a = κ-trp-op (>><< (extensionality1 (ty.type A) x y p)) a   

ty-trp-prop : {Γ : ctx}
   -> (A : ty Γ)
   -> {x y : || κ Γ ||}
   -> (p : < κ Γ > x ~ y)
   -> (a : # (apt A x))
   -> (apt A x) ‣ a ≐   (apt A y) ‣ (ty-trp-op A p a)
ty-trp-prop {Γ} A {x} {y} p a =
   let  lm : apt A x ≐ apt A y
        lm = (>><< (extensionality1 (ty.type A) x y p))
   in e+prop lm a 



Sum-op : {Γ : ctx}
   -> (A : ty Γ)
   -> (B : ty Γ)
   -> (x : || κ Γ ||)
   -> V
Sum-op {Γ} A B x = sumV (apt A x) (apt B x)

Sum-ext-half1 : {Γ : ctx}
   -> (A : ty Γ)
   -> (B : ty Γ)
   -> (x y : || κ Γ ||)
   -> < κ Γ > x ~ y 
   -> Sum-op A B x ≤ Sum-op A B y
Sum-ext-half1 {Γ} A B x y p (inl a) =
  let lm :  (apt A x) ‣ a ≐   (apt A y) ‣ (ty-trp-op A p a)
      lm = ty-trp-prop A p a
  in inl (ty-trp-op A p a) , pairV-ext (refV _) lm -- lm
Sum-ext-half1 {Γ} A B x y p (inr b) =
  let lm = (apt B x) ‣ b ≐   (apt B y) ‣ (ty-trp-op B p b)
      lm = ty-trp-prop B p b
  in inr (ty-trp-op B p b) ,  pairV-ext (refV _) lm -- lm



Sum-ext-half2 : {Γ : ctx}
   -> (A : ty Γ)
   -> (B : ty Γ)
   -> (x y : || κ Γ ||)
   -> < κ Γ > x ~ y 
   -> Sum-op A B x ≥ Sum-op A B y
Sum-ext-half2 {Γ} A B x y p u = 
    let lm = Sum-ext-half1 {Γ} A B y x (sym p) u
    in pj1 lm , symV (pj2 lm)



Sum-ext : {Γ : ctx}
   -> (A : ty Γ)
   -> (B : ty Γ)
   -> (x y : || κ Γ ||)
   -> < κ Γ > x ~ y 
   -> Sum-op A B x ≐ Sum-op A B y
Sum-ext {Γ} A B x y p = pair (Sum-ext-half1 {Γ} A B x y p) (Sum-ext-half2 {Γ} A B x y p)

Sum : {Γ : ctx}
   -> (A : ty Γ)
   -> (B : ty Γ)
   -> ty Γ
Sum {Γ} A B = mkraw (record { op = Sum-op {Γ} A B 
                            ; ext = λ x y p → <<>> (Sum-ext {Γ} A B x y p) 
                            })


Sum-cong : {Γ : ctx}
   -> (A A' : ty Γ)
   -> (B B' : ty Γ)
   -> Γ ==> A == A'
   -> Γ ==> B == B'
   -> Γ ==> Sum A B == Sum A' B'
Sum-cong {Γ} A A' B B' p q = mk-eqty (λ x → <<>> (sumV-ext (apt A x) (apt B x) (apt A' x) (apt B' x) 
                                                   (>><< (ape p x)) (>><< (ape q x))))

-- sumV-ext : (a b a' b' : V) -> a ≐ a' -> b ≐ b' -> sumV a b ≐ sumV a' b'

Sum-sub : {Δ Γ : ctx}
   -> (f : subst Δ Γ)
   -> (A : ty Γ)
   -> (B : ty Γ)
   -> Δ ==> (Sum A B) [[ f ]] == Sum (A [[ f ]]) (B [[ f ]]) 
Sum-sub {Δ} {Γ} f A B  = mk-eqty (λ x → <<>> (refV _))


-- move .. (used a lot)  --  same as Raw-lm

aprex : {Γ : ctx}
   -> (a a' : raw Γ)
   ->  << Raw Γ >> a ~ a'
   -> (x  : || κ Γ ||)
   -> apr a x ≐ apr a' x
aprex {Γ} a a' p x = >><< (>><< (>><< p) x)
 

lf-op : {Γ : ctx}
   -> (A B : ty Γ)
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> || κ Γ ||
   -> V
lf-op {Γ} A B a p x =
  (sumV (apt A x) (apt B x)) ‣ (inl ( pj1 (apel p x)))



lf-ext : {Γ : ctx}
   -> (A B : ty Γ)
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> (x y : || κ Γ ||)
   -> < κ Γ > x ~ y
   -> lf-op A B a p x ≐ lf-op A B a p y
lf-ext {Γ} A B a p x y q =
    let px = pj2 (apel p x)
        py = pj2 (apel p y)
        lm : (apt A x) ‣ (pj1 (apel p x)) ≐ (apt A y) ‣ (pj1 (apel p y))
        lm = traV (symV px) (traV (>><< (extensionality1 (raw.rawterm a) _ _ q)) py)
    in pairV-ext (refV _) lm 




lf : {Γ : ctx}
   -> (A B : ty Γ)
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> raw Γ
lf {Γ} A B a p = mkraw (record { op = lf-op {Γ} A B a p
                               ; ext = λ x y q → <<>> (lf-ext {Γ} A B a p x y q)})  


lf-pf : {Γ : ctx}
   -> (A B : ty Γ)
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> Γ ==> lf A B a p :: Sum A B
lf-pf {Γ} A B a p = mk-elt (λ x → (inl ( pj1 (apel p x))) , refV _)


lf-cong' : {Γ : ctx}
   -> (A B A' B' : ty Γ)
   -> (a a' : raw Γ)
   -> (p : Γ ==> a :: A)
   -> (p' : Γ ==> a' :: A')
   -> (q : Γ ==> A == A')
   -> (r : Γ ==> B == B')
   -> << Raw Γ >>  a ~ a'
   -> << Raw Γ >> (lf {Γ} A B a p) ~ (lf {Γ} A' B' a' p')
lf-cong' {Γ} A B A' B' a a' p p' q r t = 
      <<>> (<<>> (λ x → <<>> (inl-ext-gen (apt A x) (apt B x) (apt A' x) (apt B' x) 
                              (pj1 (apel p x)) (pj1 (apel p' x)) 
                              (traV (symV (pj2 (apel p x))) 
                                (traV  (aprex a a' t x) 
                                      (pj2 (apel p' x)))))))


lf-cong : {Γ : ctx}
   -> (A B A' B' : ty Γ)
   -> (a a' : raw Γ)
   -> (p : Γ ==> a :: A)
   -> (p' : Γ ==> a' :: A')
   -> (q : Γ ==> A == A')
   -> (r : Γ ==> B == B')
   -> (Γ ==> a == a' :: A)
   -> Γ ==> lf {Γ} A B a p == lf {Γ} A' B' a' p' :: Sum A B 
lf-cong {Γ} A B A' B' a a' p p' q r t = 
                     pair (Raw-lm (lf-cong' {Γ} A B A' B' a a' p p' q r (Raw-lm2 (prj1 t) ))) 
                          (pair (lf-pf A B a p) 
                                (subj-red _ _ (lf-pf A B a p) (lf-cong' {Γ} A B A' B' a a' p p' q r (Raw-lm2 (prj1 t) ))))



lf-sub-lm : {Δ Γ : ctx}
   -> (f : subst Δ Γ)
   -> (A B : ty Γ)
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> (p' : Δ ==> a [ f ] :: A [[ f ]])
   -> (x  : || κ Δ ||)
   -> lf-op {Γ} A B a p (aps f x) ≐  lf-op {Δ} (A [[ f ]]) (B [[ f ]]) (a [ f ]) p' x
lf-sub-lm {Δ} {Γ} f A B a p p' x = 
  let lm1 : apr a (aps f x) ≐ apt A (aps f x) ‣ pj1 (apel p (aps f x))
      lm1 = pj2 (apel p (aps f x))
      lm2 : apr (a [ f ]) x ≐ apt (A [[ f ]]) x ‣ pj1 (apel p' x)
      lm2 = pj2 (apel p' x)
      lm4 : apt A (aps f x) ‣ pj1 (apel p (aps f x))
            ≐ apt (A [[ f ]]) x ‣ pj1 (apel p' x)
      lm4 = traV (symV lm1) lm2
      lm : (sumV (apt A (aps f x)) (apt B (aps f x))) ‣ (inl ( pj1 (apel p (aps f x))))
           ≐ (sumV (apt (A [[ f ]]) x) (apt (B [[ f ]]) x)) ‣ (inl ( pj1 (apel p' x)))
      lm = inl-ext-gen (apt A (aps f x)) (apt B (aps f x)) (apt (A [[ f ]]) x) (apt (B [[ f ]]) x) _ _ lm4
  in lm 




lf-sub' : {Δ Γ : ctx}
   -> (f : subst Δ Γ)
   -> (A B : ty Γ)
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> (p' : Δ ==> a [ f ] :: A [[ f ]])
   -> << Raw Δ >> (lf A B a p) [ f ] ~ lf (A [[ f ]])  (B [[ f ]]) (a [ f ]) p'
lf-sub' {Δ} {Γ} f A B a p p' = <<>> (<<>> (λ x → <<>> (lf-sub-lm {Δ} {Γ} f A B a p p' x)))

lf-sub : {Δ Γ : ctx}
   -> (h : subst Δ Γ)
   -> (A B : ty Γ)
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> (p' : Δ ==> a [ h ] :: A [[ h ]])
   ->  Δ ==> (lf A B a p) [ h ] == lf (A [[ h ]])  (B [[ h ]]) (a [ h ]) p' :: (Sum A B) [[ h ]]
lf-sub {Δ} {Γ} h A B a p p' = pair (Raw-lm (lf-sub' {Δ} {Γ} h A B a p p')) 
                                    (pair (elt-subst h (lf-pf A B a p))
                                          (subj-red _ _ (elt-subst h (lf-pf A B a p)) (lf-sub' {Δ} {Γ} h A B a p p')))


rg-op : {Γ : ctx}
   -> (A B : ty Γ)
   -> (b : raw Γ)
   -> (p : Γ ==> b :: B)
   -> || κ Γ ||
   -> V
rg-op {Γ} A B b p x =  (sumV (apt A x) (apt B x)) ‣ (inr ( pj1 (apel p x)))


rg-ext : {Γ : ctx}
   -> (A B : ty Γ)
   -> (b : raw Γ)
   -> (p : Γ ==> b :: B)
   -> (x y : || κ Γ ||)
   -> < κ Γ > x ~ y
   -> rg-op A B b p x ≐ rg-op A B b p y
rg-ext {Γ} A B b p x y  q = 
    let px = pj2 (apel p x)
        py = pj2 (apel p y)
        lm : (apt B x) ‣ (pj1 (apel p x)) ≐ (apt B y) ‣ (pj1 (apel p y))
        lm = traV (symV px) (traV (>><< (extensionality1 (raw.rawterm b) _ _ q)) py)
    in pairV-ext (refV _) lm 

rg : {Γ : ctx}
   -> (A B : ty Γ)
   -> (b : raw Γ)
   -> (p : Γ ==> b :: B)
   -> raw Γ
rg {Γ} A B b p = mkraw (record { op = rg-op {Γ} A B b p
                               ; ext =  λ x y q → <<>> (rg-ext {Γ} A B b p x y q) })  

rg-pf : {Γ : ctx}
   -> (A B : ty Γ)
   -> (b : raw Γ)
   -> (p : Γ ==> b :: B)
   -> Γ ==> rg A B b p :: Sum A B
rg-pf {Γ} A B b p = mk-elt (λ x → (inr ( pj1 (apel p x))) , refV _)


rg-cong' : {Γ : ctx}
   -> (A B A' B' : ty Γ)
   -> (b b' : raw Γ)
   -> (p : Γ ==> b :: B)
   -> (p' : Γ ==> b' :: B')
   -> (q : Γ ==> A == A')
   -> (r : Γ ==> B == B')
   -> << Raw Γ >>  b ~ b'
   -> << Raw Γ >> (rg {Γ} A B b p) ~ (rg {Γ} A' B' b' p')
rg-cong' {Γ} A B A' B' b b' p p' q r t =   
     <<>> (<<>> (λ x → <<>> (inr-ext-gen (apt A x) (apt B x) (apt A' x) (apt B' x) 
                              (pj1 (apel p x)) (pj1 (apel p' x)) 
                              (traV (symV (pj2 (apel p x))) 
                                (traV  (aprex b b' t x) 
                                      (pj2 (apel p' x)))))))

rg-cong : {Γ : ctx}
   -> (A B A' B' : ty Γ)
   -> (b b' : raw Γ)
   -> (p : Γ ==> b :: B)
   -> (p' : Γ ==> b' :: B')
   -> (q : Γ ==> A == A')
   -> (r : Γ ==> B == B')
   -> (Γ ==> b == b' :: B)
   -> Γ ==> rg {Γ} A B b p == rg {Γ} A' B' b' p' :: Sum A B 
rg-cong {Γ} A B A' B' b b' p p' q r t = 
                 pair (Raw-lm (rg-cong' {Γ} A B A' B' b b' p p' q r (Raw-lm2 (prj1 t) ))) 
                          (pair (rg-pf A B b p) 
                                (subj-red _ _ (rg-pf A B b p) (rg-cong' {Γ} A B A' B' b b' p p' q r (Raw-lm2 (prj1 t) ))))


rg-sub-lm : {Δ Γ : ctx}
   -> (f : subst Δ Γ)
   -> (A B : ty Γ)
   -> (b : raw Γ)
   -> (p : Γ ==> b :: B)
   -> (p' : Δ ==> b [ f ] :: B [[ f ]])
   -> (x  : || κ Δ ||)
   -> rg-op {Γ} A B b p (aps f x) ≐  rg-op {Δ} (A [[ f ]]) (B [[ f ]]) (b [ f ]) p' x
rg-sub-lm {Δ} {Γ} f A B b p p' x = 
  let lm1 : apr b (aps f x) ≐ apt B (aps f x) ‣ pj1 (apel p (aps f x))
      lm1 = pj2 (apel p (aps f x))
      lm2 : apr (b [ f ]) x ≐ apt (B [[ f ]]) x ‣ pj1 (apel p' x)
      lm2 = pj2 (apel p' x)
      lm4 : apt B (aps f x) ‣ pj1 (apel p (aps f x))
            ≐ apt (B [[ f ]]) x ‣ pj1 (apel p' x)
      lm4 = traV (symV lm1) lm2
      lm : (sumV (apt A (aps f x)) (apt B (aps f x))) ‣ (inr ( pj1 (apel p (aps f x))))
           ≐ (sumV (apt (A [[ f ]]) x) (apt (B [[ f ]]) x)) ‣ (inr ( pj1 (apel p' x)))
      lm = inr-ext-gen (apt A (aps f x)) (apt B (aps f x)) (apt (A [[ f ]]) x) (apt (B [[ f ]]) x) _ _ lm4
  in lm 

rg-sub' : {Δ Γ : ctx}
   -> (f : subst Δ Γ)
   -> (A B : ty Γ)
   -> (b : raw Γ)
   -> (p : Γ ==> b :: B)
   -> (p' : Δ ==> b [ f ] :: B [[ f ]])
   -> << Raw Δ >> (rg A B b p) [ f ] ~ rg (A [[ f ]])  (B [[ f ]]) (b [ f ]) p'
rg-sub' {Δ} {Γ} f A B b p p' = <<>> (<<>> (λ x → <<>> (rg-sub-lm {Δ} {Γ} f A B b p p' x)))


rg-sub : {Δ Γ : ctx}
   -> (h : subst Δ Γ)
   -> (A B : ty Γ)
   -> (b : raw Γ)
   -> (p : Γ ==> b :: B)
   -> (p' : Δ ==> b [ h ] :: B [[ h ]])
   ->  Δ ==> (rg A B b p) [ h ] == rg (A [[ h ]])  (B [[ h ]]) (b [ h ]) p' :: (Sum A B) [[ h ]]
rg-sub {Δ} {Γ} h A B b p p' = pair (Raw-lm (rg-sub' {Δ} {Γ} h A B b p p')) 
                                    (pair (elt-subst h (rg-pf A B b p))
                                          (subj-red _ _ (elt-subst h (rg-pf A B b p)) (rg-sub' {Δ} {Γ} h A B b p p')))




Sum-sub-lf : {Γ : ctx} 
        -> (A B : ty Γ)
        ->  subst (Γ ▷ A) (Γ ▷ (Sum A B))
Sum-sub-lf {Γ} A B = 
  let lm = lf-pf  (A [[ ↓ A ]]) (B [[ ↓ A ]]) (vv A) (asm A)
      lm2 :  Γ ▷ A ==> (Sum A B [[ ↓ A ]]) == Sum (A [[ ↓ A ]]) (B [[ ↓ A ]])
      lm2 = Sum-sub  (↓ A) A B
  in ext (Sum A B) (↓ A) (lf (A [[ ↓ A ]]) (B [[ ↓ A ]]) (vv A) (asm A) ) 
                         (elttyeq lm (tysym lm2))



Sum-sub-rg : {Γ : ctx} 
        -> (A B : ty Γ)
        ->  subst (Γ ▷ B) (Γ ▷ (Sum A B))
Sum-sub-rg {Γ} A B  = 
  let lm = rg-pf  (A [[ ↓ B ]]) (B [[ ↓ B ]]) (vv B) (asm B)
      lm2 :  Γ ▷ B ==> (Sum A B [[ ↓ B ]]) == Sum (A [[ ↓ B ]]) (B [[ ↓ B ]])
      lm2 = Sum-sub  (↓ B) A B
  in ext (Sum A B) (↓ B) (rg (A [[ ↓ B ]]) (B [[ ↓ B ]]) (vv B) (asm B))
                         (elttyeq lm (tysym lm2))



Sum-rec-op-aux : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (x : || κ Γ ||)
       -> (u : || κ (apt (Sum A B) x) ||)
       -> V
Sum-rec-op-aux {Γ} A B C d p e q x (inl u) = (apt C (x , inl u)) ‣ (pj1 (apel p (x , u)))
Sum-rec-op-aux {Γ} A B C d p e q x (inr v) = (apt C (x , inr v)) ‣ (pj1 (apel q (x , v)))



Sum-rec-op-aux-lm : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (x : || κ Γ ||)
       -> (u : || κ (apt (Sum A B) x) ||)
       -> Sum-rec-op-aux {Γ} A B C d p e q x u ∈ apt C (x , u)
Sum-rec-op-aux-lm {Γ} A B C d p e q x (inl u) =  pj1 (apel p (x , u)) , refV _
Sum-rec-op-aux-lm {Γ} A B C d p e q x (inr v) =  pj1 (apel q (x , v)) , refV _



Sum-rec-op : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (c : raw Γ)
       -> (r : Γ ==> c :: Sum A B)
       -> || κ Γ ||
       -> V
Sum-rec-op {Γ} A B C d p e q c r x = Sum-rec-op-aux {Γ} A B C d p e q x (pj1 (apel r x))




Sum-rec-ext-lm : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (x y : || κ Γ ||)
       ->  < κ Γ > x ~ y
       -> (u : || κ (apt (Sum A B) x) ||)
       -> (v : || κ (apt (Sum A B) y) ||)
       -> (apt (Sum A B) x) ‣ u ≐ (apt (Sum A B) y) ‣ v
       ->  Sum-rec-op-aux {Γ} A B C d p e q x u ≐
           Sum-rec-op-aux {Γ} A B C d p e q y v
Sum-rec-ext-lm {Γ} A B C d p e q x y pf (inl a) (inl a') qf = 
       let lm1 =  pj2 (apel p (x , a))
           lm2 =  pj2 (apel p (y , a'))
           lm3 :  < κ (Γ ▷ A) > (x , a) ~ (y , a')
           lm3 = <> (pairV-ext (>< pf) (inl-inj-gen (apt A x) (apt B x) (apt A y) (apt B y) a a' qf) ) 
           lm4 : apr d (x , a) ≐  apr d (y , a') 
           lm4 = >><< (extensionality1 (raw.rawterm d) (x , a)   (y , a') lm3)
           main : apt C (x , inl a) ‣ pj1 (apel p (x , a)) ≐
                  apt C (y , inl a') ‣ pj1 (apel p (y , a'))
           main = traV (symV lm1) (traV lm4 lm2)
       in main    
Sum-rec-ext-lm {Γ} A B C d p e q x y pf (inl a) (inr b) qf = 
      exfalso _  (inl-inr-dis (apt A x) (apt B x) (apt A y) (apt B y) a b qf) 
Sum-rec-ext-lm {Γ} A B C d p e q x y pf (inr b) (inl a) qf = 
      exfalso _  (inr-inl-dis (apt A x) (apt B x) (apt A y) (apt B y) a b qf) 
Sum-rec-ext-lm {Γ} A B C d p e q x y pf (inr b) (inr b') qf =
       let lm1 =  pj2 (apel q (x , b))
           lm2 =  pj2 (apel q (y , b'))
           lm3 :  < κ (Γ ▷ B) > (x , b) ~ (y , b')
           lm3 = <> (pairV-ext (>< pf) (inr-inj-gen (apt A x) (apt B x) (apt A y) (apt B y) b b' qf) ) 
           lm4 : apr e (x , b) ≐  apr e (y , b') 
           lm4 = >><< (extensionality1 (raw.rawterm e) (x , b) (y , b') lm3)
           main : apt C (x , inr b) ‣ pj1 (apel q (x , b)) ≐
                  apt C (y , inr b') ‣ pj1 (apel q (y , b'))
           main = traV (symV lm1) (traV lm4 lm2)
       in main    



Sum-rec-ext : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (c : raw Γ)
       -> (r : Γ ==> c :: Sum A B)
       -> (x y : || κ Γ ||)
       ->  < κ Γ > x ~ y
       ->  Sum-rec-op A B C d p e q c r x ≐  Sum-rec-op A B C d p e q c r y
Sum-rec-ext {Γ} A B C d p e q c r x y pf = 
  let ec : apr c x ≐ apr c y
      ec = >><< (extensionality1 (raw.rawterm c) x y pf)
      eq : (apt (Sum A B) x) ‣ (pj1 (apel r x)) ≐ (apt (Sum A B) y) ‣ (pj1 (apel r y))
      eq = traV (symV (pj2 (apel r x))) (traV ec (pj2 (apel r y)))
      main : Sum-rec-op-aux {Γ} A B C d p e q x (pj1 (apel r x)) ≐
             Sum-rec-op-aux {Γ} A B C d p e q y (pj1 (apel r y))
      main = Sum-rec-ext-lm {Γ} A B C d p e q x y pf (pj1 (apel r x)) (pj1 (apel r y)) eq
  in main

Sum-rec : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (c : raw Γ)
       -> (r : Γ ==> c :: Sum A B)
       -> raw Γ
Sum-rec {Γ} A B C d p e q c r =  mkraw (record { op = Sum-rec-op {Γ} A B C d p e q c r 
                                               ; ext = λ x y pf → <<>> (Sum-rec-ext {Γ} A B C d p e q c r x y pf) })




 
Sum-rec-cong-lm2 : {Γ : ctx}   
       -> (A B A' B' : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (C' : ty (Γ ▷ (Sum A' B')))
       -> (d : raw (Γ ▷ A))
       -> (d' : raw (Γ ▷ A'))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (p' : (Γ ▷ A') ==> d' :: C' [[ Sum-sub-lf A' B' ]])
       -> (e : raw (Γ ▷ B))
       -> (e' : raw (Γ ▷ B'))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (q' : (Γ ▷ B') ==> e' :: C' [[ Sum-sub-rg A' B' ]])
       -> (Aq : Γ ==> A == A')
       -> (Bq : Γ ==> B == B')
       -> (Γ ▷ (Sum A B)  ==> C == C' [[  subst-trp (ext-eq' {Γ} (Sum A B) (Sum A' B') (Sum-cong A A' B B' Aq Bq)) ]])
       -> << Raw (Γ ▷ A) >> d ~ (d' [ subst-trp (ext-eq' {Γ} A A' Aq) ])
       -> << Raw (Γ ▷ B) >> e ~ (e' [ subst-trp (ext-eq' {Γ} B B' Bq) ])
       -> (x  : || κ Γ ||)
       -> (u : || κ (apt (Sum A B) x) ||)
       -> (v : || κ (apt (Sum A' B') x) ||)
       -> (apt (Sum A B) x) ‣ u ≐ (apt (Sum A' B') x) ‣ v
       -> Sum-rec-op-aux {Γ} A B C d p e q x u ≐ Sum-rec-op-aux {Γ} A' B' C' d' p' e' q' x v
Sum-rec-cong-lm2 {Γ} A B A' B' C C' d d' p p' e e' q q' Aq Bq Cq dq eq x (inl a) (inl a') pf =
     let lm = pj2 (apel p (x , a))
         lm' = pj2 (apel p' (x , a'))
         lm3 = aprex _ _ dq (x , a)
         lm4 = inl-inj-gen (apt A x) (apt B x) (apt A' x) (apt B' x) a a' pf      
         lm7 :  apt A' x ‣ (ap (κ-Fam ±± ape Aq x) a) ≐ apt A x ‣ a
         lm7 = symV (e+prop (>><< (ape Aq x)) a)
         lm6 :  < κ (Γ ▷ A') >
              ap (subst.cmap (subst-trp (ext-eq' A A' Aq))) (x , a) ~ (x , a')
         lm6 = tra (ext-eq-lm A A' Aq x a) (<> (pairV-ext (refV _) (traV lm7 lm4)))
         lm5 : apr (d' [ subst-trp (ext-eq' A A' Aq) ]) (x , a) ≐  apr d' (x , a')
         lm5 = >><< (extensionality1 (raw.rawterm d') 
                     (ap (subst.cmap (subst-trp (ext-eq' A A' Aq))) (x , a)) (x , a') lm6)
         lm2 : apr d (x , a) ≐  apr d' (x , a')
         lm2 = traV lm3 lm5
         main : apt C (x , inl a) ‣ pj1 (apel p (x , a)) ≐
                apt C' (x , inl a') ‣ pj1 (apel p' (x , a'))
         main = traV (symV lm) (traV lm2 lm')
     in main
Sum-rec-cong-lm2 {Γ} A B A' B' C C' d d' p p' e e' q q' Aq Bq Cq dq eq x (inl a) (inr b)  pf = exfalso _  (inl-inr-dis (apt A x) (apt B x) (apt A' x) (apt B' x) a b pf) 
Sum-rec-cong-lm2 {Γ} A B A' B' C C' d d' p p' e e' q q' Aq Bq Cq dq eq x (inr b) (inl a)  pf = exfalso _  (inr-inl-dis (apt A x) (apt B x) (apt A' x) (apt B' x) a b pf)
Sum-rec-cong-lm2 {Γ} A B A' B' C C' d d' p p' e e' q q' Aq Bq Cq dq eq x (inr b) (inr b')  pf = 
     let lm = pj2 (apel q (x , b))
         lm' = pj2 (apel q' (x , b'))
         lm3 = aprex _ _ eq (x , b)
         lm4 = inr-inj-gen (apt A x) (apt B x) (apt A' x) (apt B' x) b b' pf      
         lm7 :  apt B' x ‣ (ap (κ-Fam ±± ape Bq x) b) ≐ apt B x ‣ b
         lm7 = symV (e+prop (>><< (ape Bq x)) b)
         lm6 :  < κ (Γ ▷ B') >
              ap (subst.cmap (subst-trp (ext-eq' B B' Bq))) (x , b) ~ (x , b')
         lm6 = tra (ext-eq-lm B B' Bq x b) (<> (pairV-ext (refV _) (traV lm7 lm4)))
         lm5 : apr (e' [ subst-trp (ext-eq' B B' Bq) ]) (x , b) ≐  apr e' (x , b')
         lm5 = >><< (extensionality1 (raw.rawterm e') 
                     (ap (subst.cmap (subst-trp (ext-eq' B B' Bq))) (x , b)) (x , b') lm6)
         lm2 : apr e (x , b) ≐  apr e' (x , b')
         lm2 = traV lm3 lm5
         main : apt C (x , inr b) ‣ pj1 (apel q (x , b)) ≐
                apt C' (x , inr b') ‣ pj1 (apel q' (x , b'))
         main = traV (symV lm) (traV lm2 lm')
     in main

Sum-rec-cong-lm : {Γ : ctx}   
       -> (A B A' B' : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (C' : ty (Γ ▷ (Sum A' B')))
       -> (d : raw (Γ ▷ A))
       -> (d' : raw (Γ ▷ A'))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (p' : (Γ ▷ A') ==> d' :: C' [[ Sum-sub-lf A' B' ]])
       -> (e : raw (Γ ▷ B))
       -> (e' : raw (Γ ▷ B'))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (q' : (Γ ▷ B') ==> e' :: C' [[ Sum-sub-rg A' B' ]])
       -> (c : raw Γ)
       -> (c' : raw Γ)
       -> (r : Γ ==> c :: Sum A B)
       -> (r' : Γ ==> c' :: Sum A' B')
       -> (Aq : Γ ==> A == A')
       -> (Bq : Γ ==> B == B')
       -> (Γ ▷ (Sum A B)  ==> C == C' [[  subst-trp (ext-eq' {Γ} (Sum A B) (Sum A' B') (Sum-cong A A' B B' Aq Bq)) ]])
       -> << Raw (Γ ▷ A) >> d ~ (d' [ subst-trp (ext-eq' {Γ} A A' Aq) ])
       -> << Raw (Γ ▷ B) >> e ~ (e' [ subst-trp (ext-eq' {Γ} B B' Bq) ])
       -> << Raw Γ >> c ~ c'
       -> (x  : || κ Γ ||)
       ->  Sum-rec-op {Γ} A B C d p e q c r x ≐ Sum-rec-op {Γ} A' B' C' d' p' e' q' c' r' x
Sum-rec-cong-lm {Γ} A B A' B' C C' d d' p p' e e' q q' c c' r r' Aq Bq Cq dq eq cq x =
   let pf : (apt (Sum A B) x) ‣ (pj1 (apel r x)) ≐ (apt (Sum A' B') x) ‣ (pj1 (apel r' x))
       pf = traV (symV (pj2 (apel r x))) (traV (aprex c c' cq x) (pj2 (apel r' x)))
       lm : Sum-rec-op-aux {Γ} A B C d p e q x (pj1 (apel r x)) ≐ Sum-rec-op-aux {Γ} A' B' C' d' p' e' q' x (pj1 (apel r' x))
       lm = Sum-rec-cong-lm2 {Γ} A B A' B' C C' d d' p p' e e' q q' Aq Bq Cq dq eq x (pj1 (apel r x)) (pj1 (apel r' x)) pf
   in lm


 
Sum-rec-cong' : {Γ : ctx}   
       -> (A B A' B' : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (C' : ty (Γ ▷ (Sum A' B')))
       -> (d : raw (Γ ▷ A))
       -> (d' : raw (Γ ▷ A'))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (p' : (Γ ▷ A') ==> d' :: C' [[ Sum-sub-lf A' B' ]])
       -> (e : raw (Γ ▷ B))
       -> (e' : raw (Γ ▷ B'))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (q' : (Γ ▷ B') ==> e' :: C' [[ Sum-sub-rg A' B' ]])
       -> (c : raw Γ)
       -> (c' : raw Γ)
       -> (r : Γ ==> c :: Sum A B)
       -> (r' : Γ ==> c' :: Sum A' B')
       -> (Aq : Γ ==> A == A')
       -> (Bq : Γ ==> B == B')
       -> (Γ ▷ (Sum A B)  ==> C == C' [[  subst-trp (ext-eq' {Γ} (Sum A B) (Sum A' B') (Sum-cong A A' B B' Aq Bq)) ]])
       -> << Raw (Γ ▷ A) >> d ~ (d' [ subst-trp (ext-eq' {Γ} A A' Aq) ])
       -> << Raw (Γ ▷ B) >> e ~ (e' [ subst-trp (ext-eq' {Γ} B B' Bq) ])
       -> << Raw Γ >> c ~ c'
       -> << Raw Γ >>  Sum-rec {Γ} A B C d p e q c r ~  Sum-rec {Γ} A' B' C' d' p' e' q' c' r'
Sum-rec-cong' {Γ} A B A' B' C C' d d' p p' e e' q q' c c' r r' Aq Bq Cq dq eq cq =
    <<>> (<<>> (λ x → <<>> (Sum-rec-cong-lm {Γ} A B A' B' C C' d d' p p' e e' q q' c c' r r' Aq Bq Cq dq eq cq x)))





Sum-rec-sub-lm2 : {Δ Γ : ctx}
       -> (f : subst Δ Γ)   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (c : raw Γ)
       -> (r : Γ ==> c :: Sum A B)
       -> (p' : Δ ▷ _[[_]] {Δ} {Γ} A f ==>
                   _[_] {Δ ▷ _[[_]] {Δ} {Γ} A f} {Γ ▷ A} d (↑ {Δ} {Γ} A f) ::
                  _[[_]] {Δ ▷ _[[_]] {Δ} {Γ} A f}
                 {Δ ▷ Sum {Δ} (_[[_]] {Δ} {Γ} A f) (_[[_]] {Δ} {Γ} B f)}
                   (_[[_]] {Δ ▷ _[[_]] {Δ} {Γ} (Sum {Γ} A B) f} {Γ ▷ Sum {Γ} A B} C
                   (↑ {Δ} {Γ} (Sum {Γ} A B) f))
                  (Sum-sub-lf {Δ} (_[[_]] {Δ} {Γ} A f) (_[[_]] {Δ} {Γ} B f)))
       -> (q' : Δ ▷ _[[_]] {Δ} {Γ} B f ==>
                 _[_] {Δ ▷ _[[_]] {Δ} {Γ} B f} {Γ ▷ B} e (↑ {Δ} {Γ} B f) ::
                  _[[_]] {Δ ▷ _[[_]] {Δ} {Γ} B f}
              {Δ ▷ Sum {Δ} (_[[_]] {Δ} {Γ} A f) (_[[_]] {Δ} {Γ} B f)}
                (_[[_]] {Δ ▷ _[[_]] {Δ} {Γ} (Sum {Γ} A B) f} {Γ ▷ Sum {Γ} A B} C
                      (↑ {Δ} {Γ} (Sum {Γ} A B) f))
                (Sum-sub-rg {Δ} (_[[_]] {Δ} {Γ} A f) (_[[_]] {Δ} {Γ} B f)))
       -> (r' : Δ ==> c [ f ] :: Sum (A [[ f ]]) (B [[ f ]]))
       -> (x  : || κ Δ ||)
       -> (u : # (apt (Sum A B) (aps f x)))
       -> (v : # (apt (Sum (A [[ f ]]) (B [[ f ]])) x))
       -> (apt (Sum A B) (aps f x) ‣  u  ≐  apt (Sum (A [[ f ]]) (B [[ f ]])) x ‣ v)
       ->  Sum-rec-op-aux {Γ} A B C d p e q (aps f x) u ≐
           Sum-rec-op-aux {Δ} (A [[ f ]]) (B [[ f ]]) (C [[ ↑ (Sum A B) f ]])
                     (d [ ↑ A f ]) p' (e [ ↑ B f ]) q'  x v
Sum-rec-sub-lm2 {Δ} {Γ} f A B C d p e q c r p' q' r' x (inl u) (inl v) t =    
       let lm1 =  pj2 (apel p (aps f x , u))
           lm2 =  pj2 (apel p' (x , v))  
           lmt : (apt A (aps f x)) ‣ u ≐  (apt (A [[ f ]]) x) ‣ v
           lmt = inl-inj-gen (apt A (aps f x)) (apt B (aps f x)) (apt (A [[ f ]]) x) (apt (B [[ f ]]) x) u v t  
           lm3 :  < κ (Γ ▷ A) > aps f x , u ~ (aps f x , v)
           lm3 = <> (pairV-ext (refV _) lmt)
           lm3b : apr d (aps f x , u) ≐ apr d (aps f x , v)
           lm3b = >><< (extensionality1 (raw.rawterm d) (aps f x , u) (aps f x , v) lm3)
           lm3c : apr d (aps f x , v) ≐ apr (d [ ↑ A f ]) (x , v)
           lm3c = symV (traV (sub-apply d (↑ A f) (x , v)) 
                   (>><< (extensionality1 (raw.rawterm d) (aps (↑ A f) (x , v)) (aps f x , v) (qq-eq A f x v))))
           lm4 : apr d (aps f x , u) ≐ apr (d [ ↑ A f ]) (x , v)
           lm4 = traV lm3b lm3c
           main : apt C (aps f x , inl u) ‣ pj1 (apel p (aps f x , u)) ≐
                  apt (C [[ ↑ (Sum A B) f ]]) (x , inl v) ‣ pj1 (apel p' (x , v))
           main = traV (symV lm1) (traV lm4 lm2)
       in main 


Sum-rec-sub-lm2 {Δ} {Γ} f A B C d p e q c r p' q' r' x (inl u) (inr v) t = 
     exfalso _  (inl-inr-dis (apt A (aps f x)) (apt B (aps f x)) (apt (A [[ f ]]) x) (apt (B [[ f ]]) x) u v t) 
Sum-rec-sub-lm2 {Δ} {Γ} f A B C d p e q c r p' q' r' x (inr u) (inl v) t =   
     exfalso _  (inr-inl-dis (apt A (aps f x)) (apt B (aps f x)) (apt (A [[ f ]]) x) (apt (B [[ f ]]) x) v u t) 
Sum-rec-sub-lm2 {Δ} {Γ} f A B C d p e q c r p' q' r' x (inr u) (inr v) t =  
       let lm1 =  pj2 (apel q (aps f x , u))
           lm2 =  pj2 (apel q' (x , v))  
           lmt : (apt B (aps f x)) ‣ u ≐  (apt (B [[ f ]]) x) ‣ v
           lmt = inr-inj-gen (apt A (aps f x)) (apt B (aps f x)) (apt (A [[ f ]]) x) (apt (B [[ f ]]) x) u v t  
           lm3 :  < κ (Γ ▷ B) > aps f x , u ~ (aps f x , v)
           lm3 = <> (pairV-ext (refV _) lmt)
           lm3b : apr e (aps f x , u) ≐ apr e (aps f x , v)
           lm3b = >><< (extensionality1 (raw.rawterm e) (aps f x , u) (aps f x , v) lm3)
           lm3c : apr e (aps f x , v) ≐ apr (e [ ↑ B f ]) (x , v)
           lm3c =  symV (traV (sub-apply e (↑ B f) (x , v)) 
                   (>><< (extensionality1 (raw.rawterm e) (aps (↑ B f) (x , v)) (aps f x , v) (qq-eq B f x v))))
           lm4 : apr e (aps f x , u) ≐ apr (e [ ↑ B f ]) (x , v)
           lm4 = traV lm3b lm3c  
           main :  apt C (aps f x , inr u) ‣ pj1 (apel q (aps f x , u)) ≐
                   apt (C [[ ↑ (Sum A B) f ]]) (x , inr v) ‣ pj1 (apel q' (x , v))

           main = traV (symV lm1) (traV lm4 lm2)   
       in main 
   
Sum-rec-sub-lm : {Δ Γ : ctx}
       -> (f : subst Δ Γ)   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (c : raw Γ)
       -> (r : Γ ==> c :: Sum A B)
       -> (p' : Δ ▷ (A [[ f ]]) ==>  d [ ↑ A f ] ::
                  _[[_]] {Δ ▷ _[[_]] {Δ} {Γ} A f}
                 {Δ ▷ Sum {Δ} (_[[_]] {Δ} {Γ} A f) (_[[_]] {Δ} {Γ} B f)}
                   (_[[_]] {Δ ▷ _[[_]] {Δ} {Γ} (Sum {Γ} A B) f} {Γ ▷ Sum {Γ} A B} C
                   (↑ {Δ} {Γ} (Sum {Γ} A B) f))
                  (Sum-sub-lf {Δ} (_[[_]] {Δ} {Γ} A f) (_[[_]] {Δ} {Γ} B f)))
       -> (q' : Δ ▷ (B [[ f ]]) ==> e [ ↑ B f ] ::
                  _[[_]] {Δ ▷ _[[_]] {Δ} {Γ} B f}
              {Δ ▷ Sum {Δ} (_[[_]] {Δ} {Γ} A f) (_[[_]] {Δ} {Γ} B f)}
                (_[[_]] {Δ ▷ _[[_]] {Δ} {Γ} (Sum {Γ} A B) f} {Γ ▷ Sum {Γ} A B} C
                      (↑ {Δ} {Γ} (Sum {Γ} A B) f))
                (Sum-sub-rg {Δ} (_[[_]] {Δ} {Γ} A f) (_[[_]] {Δ} {Γ} B f)))
       -> (r' : Δ ==> c [ f ] :: Sum (A [[ f ]]) (B [[ f ]]))
       -> (x  : || κ Δ ||)
       ->  
           raw.rawterm (Sum-rec A B C d p e q c r [ f ]) • x ≐
           (raw.rawterm
           (Sum-rec (A [[ f ]]) (B [[ f ]]) (C [[ ↑ (Sum A B) f ]])
            (d [ ↑ A f ]) p' (e [ ↑ B f ]) q' (c [ f ]) r')
           • x)
Sum-rec-sub-lm {Δ} {Γ} f A B C d p e q c r p' q' r' x = 
   let lm1 = (pj2 (apel r (aps f x)))
       lm2 = (pj2 (apel r' x))
       lm3 : apr (c [ f ]) x ≐ apr c (aps f x) 
       lm3 = refV _
       lk1 = (pj1 (apel r (aps f x)))
       lk2 = (pj1 (apel r' x))
       eq : apt (Sum A B) (aps f x) ‣ pj1 (apel r (aps f x)) ≐ apt (Sum (A [[ f ]]) (B [[ f ]])) x ‣ pj1 (apel r' x)
       eq = traV (symV lm1) lm2
       main :   Sum-rec-op-aux {Γ} A B C d p e q (aps f x) (pj1 (apel r (aps f x))) ≐
                Sum-rec-op-aux {Δ} (A [[ f ]]) (B [[ f ]]) (C [[ ↑ (Sum A B) f ]])
                     (d [ ↑ A f ]) p' (e [ ↑ B f ]) q'  x (pj1 (apel r' x))
       main = Sum-rec-sub-lm2 {Δ} {Γ} f A B C d p e q c r p' q' r' x lk1 lk2 eq
    in main 


Sum-rec-sub' : {Δ Γ : ctx}
       -> (f : subst Δ Γ)   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (c : raw Γ)
       -> (r : Γ ==> c :: Sum A B)
       -> (p' : Δ ▷ (A [[ f ]]) ==>  d [ ↑ A f ] ::
                  _[[_]] {Δ ▷ _[[_]] {Δ} {Γ} A f}
                 {Δ ▷ Sum {Δ} (_[[_]] {Δ} {Γ} A f) (_[[_]] {Δ} {Γ} B f)}
                   (_[[_]] {Δ ▷ _[[_]] {Δ} {Γ} (Sum {Γ} A B) f} {Γ ▷ Sum {Γ} A B} C
                   (↑ {Δ} {Γ} (Sum {Γ} A B) f))
                  (Sum-sub-lf {Δ} (_[[_]] {Δ} {Γ} A f) (_[[_]] {Δ} {Γ} B f)))
       -> (q' : Δ ▷ (B [[ f ]]) ==> e [ ↑ B f ] ::
                  _[[_]] {Δ ▷ _[[_]] {Δ} {Γ} B f}
              {Δ ▷ Sum {Δ} (_[[_]] {Δ} {Γ} A f) (_[[_]] {Δ} {Γ} B f)}
                (_[[_]] {Δ ▷ _[[_]] {Δ} {Γ} (Sum {Γ} A B) f} {Γ ▷ Sum {Γ} A B} C
                      (↑ {Δ} {Γ} (Sum {Γ} A B) f))
                (Sum-sub-rg {Δ} (_[[_]] {Δ} {Γ} A f) (_[[_]] {Δ} {Γ} B f)))
       -> (r' : Δ ==> c [ f ] :: Sum (A [[ f ]]) (B [[ f ]]))
       -> << Raw Δ >> ((Sum-rec {Γ} A B C d p e q c r) [ f ])
                      ~  (Sum-rec {Δ} (A [[ f ]]) (B [[ f ]]) (C [[ ↑ {Δ} {Γ} (Sum A B) f ]]) 
                                    (d [ ↑  A f ]) p' (e [ ↑ B f ]) q' (c [ f ]) r')
Sum-rec-sub' {Δ} {Γ} f A B C d p e q c r p' q' r' = 
    let main :  << Raw Δ >> ((Sum-rec {Γ} A B C d p e q c r) [ f ])
                      ~ (Sum-rec {Δ} (A [[ f ]]) (B [[ f ]]) (C [[ ↑ {Δ} {Γ} (Sum A B) f ]]) 
                                    (d [ ↑  A f ]) p' (e [ ↑ B f ]) q' (c [ f ]) r')
        main = <<>> (<<>> (λ x → <<>> (Sum-rec-sub-lm {Δ} {Γ} f A B C d p e q c r p' q' r' x )))
    in main


Sum-e : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (c : raw Γ)
       -> (r : Γ ==> c :: Sum A B)
       -> Γ ==> Sum-rec A B C d p e q c r :: C [[ els r ]]
Sum-e {Γ} A B C d p e q c r = mk-elt (λ x → Sum-rec-op-aux-lm {Γ} A B C d p e q x (pj1 (apel r x)))


Sum-c1-lm : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (a : raw Γ)
       -> (r : Γ ==> a :: A)
       -> (r' : Γ ==> (lf {Γ} A B a r) :: Sum A B)
       -> (x  : || κ Γ ||)
       -> apr (Sum-rec A B C d p e q (lf A B a r) r') x ≐  apr (d [ els r ]) x
Sum-c1-lm {Γ} A B C d p e q a r r' x = 
  let lm1 = pj2 (apel r x)
      lm2 :  apr (lf A B a r) x ≐ apt (Sum A B) x ‣ pj1 (apel r' x)
      lm2 = pj2 (apel r' x)
      lm3 :  apr (lf A B a r) x ≐ (sumV (apt A x) (apt B x)) ‣ (inl ( pj1 (apel r x)))
      lm3 = refV _
      lm4  = pj2 (apel p (x , pj1 (apel r x)))
      lm5 = traV (symV lm3) lm2
      main' : Sum-rec-op-aux {Γ} A B C d p e q x (inl ( pj1 (apel r x))) ≐ apr (d [ els r ]) x
      main' = symV lm4
      lm6 :  Sum-rec-op-aux {Γ} A B C d p e q x (inl ( pj1 (apel r x))) ≐
             Sum-rec-op-aux {Γ} A B C d p e q x (pj1 (apel r' x))
      lm6 =  Sum-rec-ext-lm {Γ} A B C d p e q x x (<> (refV _)) (inl ( pj1 (apel r x))) (pj1 (apel r' x)) 
                    lm2 
      main : Sum-rec-op-aux {Γ} A B C d p e q x (pj1 (apel r' x)) ≐ apr (d [ els r ]) x
      main = traV (symV lm6) main' 
  in main

Sum-c1-lm2 : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (a : raw Γ)
       -> (r : Γ ==> a :: A)
       -> (r' : Γ ==> (lf {Γ} A B a r) :: Sum A B)
       -> (x   : || κ Γ ||)
       -> (κ (Γ ▷ Sum A B) setoid.∼
            ap (subst.cmap (Sum-sub-lf A B)) (ap (subst.cmap (els r)) x))
           (ap (subst.cmap (els r')) x)
Sum-c1-lm2 {Γ} A B C a r r' x = 
   let lm1 = pj2 (apel r' x)
       lm2 = pj2 (apel r x)
       lm3 :  apt A (aps (↓ A) (ap (subst.cmap (els r)) x)) ‣
                 pj1 (apel r x)
              ≐ apt A x ‣ pj1 (apel r x)
       lm3 = refV _
   in pairV-ext (refV _) (traV (pairV-ext (refV _) lm3 ) lm1)



Sum-c1 : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (a : raw Γ)
       -> (r : Γ ==> a :: A)
       -> (r' : Γ ==> (lf {Γ} A B a r) :: Sum A B)
       -> Γ ==> Sum-rec A B C d p e q (lf {Γ} A B a r) r' == d [ els r ] :: C [[ els r' ]]
Sum-c1 {Γ} A B C d p e q a r r' = 
    let lm2 : Γ  ==> d [ els r ] :: C [[ Sum-sub-lf A B ]] [[ els r ]]
        lm2 = elt-subst (els r) p
        lm3 : Γ  ==>  C [[ Sum-sub-lf A B ]] [[ els r ]] ==  C [[ els r' ]]
        lm3 = mk-eqty (λ x → extensionality1 (ty.type C) _ _ (<> (Sum-c1-lm2 {Γ} A B C a r r' x)))
        lm : Γ ==> d [ els r ] :: C [[ els r' ]]
        lm = elttyeq lm2 lm3
    in  pair (Sum-c1-lm {Γ} A B C d p e q a r r')
             (pair (Sum-e {Γ} A B C d p e q  (lf A B a r) r') 
                   lm)
 

Sum-c2-lm : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (b : raw Γ)
       -> (r : Γ ==> b :: B)
       -> (r' : Γ ==> (rg {Γ} A B b r) :: Sum A B)
       -> (x  : || κ Γ ||)
       -> apr (Sum-rec A B C d p e q (rg A B b r) r') x ≐ apr (e [ els r ]) x
Sum-c2-lm {Γ} A B C d p e q b r r' x = 
  let lm1 = pj2 (apel r x)
      lm2 :  apr (rg A B b r) x ≐ apt (Sum A B) x ‣ pj1 (apel r' x)
      lm2 = pj2 (apel r' x)
      lm3 :  apr (rg A B b r) x ≐ (sumV (apt A x) (apt B x)) ‣ (inr ( pj1 (apel r x)))
      lm3 = refV _
      lm4  = pj2 (apel q (x , pj1 (apel r x)))
      lm5 = traV (symV lm3) lm2
      main' : Sum-rec-op-aux {Γ} A B C d p e q x (inr ( pj1 (apel r x))) ≐ apr (e [ els r ]) x
      main' = symV lm4
      lm6 :  Sum-rec-op-aux {Γ} A B C d p e q x (inr ( pj1 (apel r x))) ≐
             Sum-rec-op-aux {Γ} A B C d p e q x (pj1 (apel r' x))
      lm6 =  Sum-rec-ext-lm {Γ} A B C d p e q x x (<> (refV _)) (inr ( pj1 (apel r x))) (pj1 (apel r' x)) 
                    lm2
      main : Sum-rec-op-aux {Γ} A B C d p e q x (pj1 (apel r' x)) ≐ apr (e [ els r ]) x
      main = traV (symV lm6) main'
  in main

Sum-c2-lm2 : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (b : raw Γ)
       -> (r : Γ ==> b :: B)
       -> (r' : Γ ==> (rg {Γ} A B b r) :: Sum A B)
       -> (x   : || κ Γ ||)
       -> (κ (Γ ▷ Sum A B) setoid.∼
            ap (subst.cmap (Sum-sub-rg A B)) (ap (subst.cmap (els r)) x))
           (ap (subst.cmap (els r')) x)
Sum-c2-lm2 {Γ} A B C b r r' x = 
   let lm1 = pj2 (apel r' x)
       lm2 = pj2 (apel r x)
       lm3 :  apt B (aps (↓ B) (ap (subst.cmap (els r)) x)) ‣
                 pj1 (apel r x)
              ≐ apt B x ‣ pj1 (apel r x)
       lm3 = refV _
   in pairV-ext (refV _) (traV (pairV-ext (refV _) lm3 ) lm1)

Sum-c2 : {Γ : ctx}   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (b : raw Γ)
       -> (r : Γ ==> b :: B)
       -> (r' : Γ ==> (rg {Γ} A B b r) :: Sum A B)
       -> Γ ==> Sum-rec A B C d p e q (rg {Γ} A B b r) r' == e [ els r ] :: C [[ els r'  ]]
Sum-c2 {Γ} A B C d p e q b r r' = 
  let   lm2 : Γ  ==> e [ els r ] :: C [[ Sum-sub-rg A B ]] [[ els r ]]
        lm2 = elt-subst (els r) q
        lm3 : Γ  ==>  C [[ Sum-sub-rg A B ]] [[ els r ]] ==  C [[ els r' ]]
        lm3 = mk-eqty (λ x → extensionality1 (ty.type C) _ _ (<> (Sum-c2-lm2 {Γ} A B C b r r' x)))
        lm : Γ ==> e [ els r ] :: C [[ els r' ]]
        lm =  elttyeq lm2 lm3
  in
                pair (Sum-c2-lm {Γ} A B C d p e q b r r') 
                     (pair (Sum-e {Γ} A B C d p e q  (rg A B b r) r') 
                           lm)


Sum-rec-cong : {Γ : ctx}   
       -> (A B A' B' : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (C' : ty (Γ ▷ (Sum A' B')))
       -> (d : raw (Γ ▷ A))
       -> (d' : raw (Γ ▷ A'))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (p' : (Γ ▷ A') ==> d' :: C' [[ Sum-sub-lf A' B' ]])
       -> (e : raw (Γ ▷ B))
       -> (e' : raw (Γ ▷ B'))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (q' : (Γ ▷ B') ==> e' :: C' [[ Sum-sub-rg A' B' ]])
       -> (c : raw Γ)
       -> (c' : raw Γ)
       -> (r : Γ ==> c :: Sum A B)
       -> (r' : Γ ==> c' :: Sum A' B')
       -> (Aq : Γ ==> A == A')
       -> (Bq : Γ ==> B == B')
       -> (Γ ▷ (Sum A B)  ==> C == C' [[  subst-trp (ext-eq' {Γ} (Sum A B) (Sum A' B') (Sum-cong A A' B B' Aq Bq)) ]])
       -> ((Γ ▷ A) ==> d == (d' [ subst-trp (ext-eq' {Γ} A A' Aq) ]) :: C [[ Sum-sub-lf A B ]]) 
       -> ((Γ ▷ B) ==> e == (e' [ subst-trp (ext-eq' {Γ} B B' Bq) ]) :: C [[ Sum-sub-rg A B ]]) 
       -> (Γ ==> c == c' :: Sum A B) 
       -> Γ ==>  Sum-rec {Γ} A B C d p e q c r == Sum-rec {Γ} A' B' C' d' p' e' q' c' r' :: C [[ els r ]]
Sum-rec-cong {Γ} A B A' B' C C' d d' p p' e e' q q' c c' r r' Aq Bq Cq dq eq cq = 
     let dq' : << Raw (Γ ▷ A) >> d ~ (d' [ subst-trp (ext-eq' {Γ} A A' Aq) ])
         dq' = Raw-lm2 (prj1 dq)
         eq' : << Raw (Γ ▷ B) >> e ~ (e' [ subst-trp (ext-eq' {Γ} B B' Bq) ])
         eq' = Raw-lm2 (prj1 eq)
         cq' : << Raw Γ >> c ~ c'
         cq' = Raw-lm2 (prj1 cq)
         lm = Sum-rec-cong' {Γ} A B A' B' C C' d d' p p' e e' q q' c c' r r' Aq Bq Cq dq' eq' cq'
     in
          pair (Raw-lm lm) 
               (pair (Sum-e A B C d p e q c r) (subj-red _ _ (Sum-e A B C d p e q c r) lm))


Sum-rec-sub : {Δ Γ : ctx}
       -> (h : subst Δ Γ)   
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (c : raw Γ)
       -> (r : Γ ==> c :: Sum A B)
       -> (p' : Δ ▷ (A [[ h ]]) ==>  d [ ↑ A h ] ::
                  _[[_]] {Δ ▷ _[[_]] {Δ} {Γ} A h}
                 {Δ ▷ Sum {Δ} (_[[_]] {Δ} {Γ} A h) (_[[_]] {Δ} {Γ} B h)}
                   (_[[_]] {Δ ▷ _[[_]] {Δ} {Γ} (Sum {Γ} A B) h} {Γ ▷ Sum {Γ} A B} C
                   (↑ {Δ} {Γ} (Sum {Γ} A B) h))
                  (Sum-sub-lf {Δ} (_[[_]] {Δ} {Γ} A h) (_[[_]] {Δ} {Γ} B h)))
       -> (q' : Δ ▷ (B [[ h ]]) ==> e [ ↑ B h ] ::
                  _[[_]] {Δ ▷ _[[_]] {Δ} {Γ} B h}
              {Δ ▷ Sum {Δ} (_[[_]] {Δ} {Γ} A h) (_[[_]] {Δ} {Γ} B h)}
                (_[[_]] {Δ ▷ _[[_]] {Δ} {Γ} (Sum {Γ} A B) h} {Γ ▷ Sum {Γ} A B} C
                      (↑ {Δ} {Γ} (Sum {Γ} A B) h))
                (Sum-sub-rg {Δ} (_[[_]] {Δ} {Γ} A h) (_[[_]] {Δ} {Γ} B h)))
       -> (r' : Δ ==> c [ h ] :: Sum (A [[ h ]]) (B [[ h ]]))
       ->  Δ ==> ((Sum-rec {Γ} A B C d p e q c r) [ h ])
                     ==  (Sum-rec {Δ} (A [[ h ]]) (B [[ h ]]) (C [[ ↑ {Δ} {Γ} (Sum A B) h ]]) 
                                    (d [ ↑  A h ]) p' (e [ ↑ B h ]) q' (c [ h ]) r') 
                       ::  C [[ els r ]] [[ h ]]
Sum-rec-sub {Δ} {Γ} h A B C d p e q c r p' q' r' =
  let lm = Sum-rec-sub' {Δ} {Γ} h A B C d p e q c r p' q' r'

  in  pair (Raw-lm lm) 
           (pair (elt-subst h (Sum-e A B C d p e q c r)) 
                 (subj-red _ _ (elt-subst h (Sum-e A B C d p e q c r))
                               lm))

{--
-- Raw-lm2  : {Γ : ctx} -> {a b : raw Γ}
--       -> ((x : || κ Γ ||) -> (apr a x) ≐ (apr b x))
--       -> (<< Raw Γ >> a ~ b)
pair (Raw-lm (rg-sub' {Δ} {Γ} h A B b p p')) 
                                    (pair (elt-subst h (rg-pf A B b p))
                                          (subj-red _ _ (elt-subst h (rg-pf A B b p)) (rg-sub' {Δ} {Γ} h A B b p p')))
--}
