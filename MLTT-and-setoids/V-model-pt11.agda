-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt11 where

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
open import iterative-sets-pt8
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


-- Universes à la Russell with parameters
-- 
--       



-- constant type


U-f  :   (I : Set) -> (F : I -> Set) 
        -> (Γ : ctx)  -> ty Γ
U-f I F Γ = Const (uV I F)  Γ

T-f :  (I : Set) -> (F : I -> Set) 
     -> {Γ : ctx}  -> (A : raw Γ)
     -> (Γ ==> A :: U-f I F Γ)
-- --------------------------
     -> ty Γ
T-f I F {Γ} A p = A  -- tyy (raw.rawterm A)

T-f-Russell-eq : (I : Set) -> (F : I -> Set) 
     -> {Γ : ctx}  -> (A : raw Γ)
     -> (p : Γ ==> A :: U-f I F Γ)
-- -------------------------------
     ->  Γ ==> T-f I F A p == A
--
T-f-Russell-eq I F {Γ} A p = tyrefl A

U-f-sub : (I : Set) -> (F : I -> Set) 
     ->  (Δ Γ : ctx)  -> (f : subst Δ Γ)
     ->  Δ ==> (U-f I F Γ) [[ f ]] == U-f I F Δ
U-f-sub I F Δ Γ f = mk-eqty (λ x → <<>> (refV _))


natU : (Γ : ctx) -> raw Γ
natU Γ = mkraw (record { op = λ x → natV 
                       ; ext = λ x y p → refl' _ _  
                       })



U-f-nat :  (I : Set) -> (F : I -> Set) 
           -> (Γ : ctx) 
-- -----------------------------------
    -> Γ ==> natU Γ :: U-f I F Γ
--
U-f-nat I F Γ = mk-elt (λ x → nat-sV I F , (symV (emb-nat I F)))




T-f-nat :  (I : Set) -> (F : I -> Set) 
              -> (Γ : ctx)
-- ------------------------------------------------------
      -> Γ ==> T-f I F (natU Γ) (U-f-nat I F Γ) == Nat Γ
--
T-f-nat I F Γ = mk-eqty (λ x → <<>> (traV (easy-eqV _ _ _ (λ y → symV (nat-sV-V I F y))) (emb-nat I F))) 


U-f-Russell-nat :  (I : Set) -> (F : I -> Set) 
              -> (Γ : ctx) 
-- -----------------------------------
    -> Γ ==> Nat Γ :: U-f I F Γ
--
U-f-Russell-nat I F Γ = mk-elt (λ x → natV-in-uV I F)  





-- sigma-sV


U-f-Russell-sigma-lm : (I : Set) -> (F : I -> Set) 
    -> {Γ : ctx} 
    ->  (A : ty Γ) 
    ->  (p : Γ ==> A :: U-f I F Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U-f I F Γ [[ ↓ A ]])
    ->  (x :  || κ Γ ||)
    ->  apr (Σ-f A B) x ∈ uV I F
U-f-Russell-sigma-lm I F {Γ} A p B q x = 
  let lm : (apt (Σ-f A B) x) ≐ sigmaV (apt A x) (mk-Par-op-Fx A B x)
      lm = Σ-f-exp1 {Γ} A B x
      lm2 : sigmaV (apt A x) (mk-Par-op-Fx A B x) ∈ uV I F
      lm2 = sigmaV-reflection I F (apt A x) (mk-Par-op-Fx A B x) 
                  (apel p x) (λ y → apel q (x , y))
      main : apr (Σ-f A B) x ∈ uV I F
      main = memV-left-ext (apr (Σ-f A B) x)  _ (uV I F)  lm lm2
  in main



U-f-Russell-sigma :  (I : Set) -> (F : I -> Set) 
    -> {Γ : ctx} 
    ->  (A : ty Γ) 
    ->  (p : Γ ==> A :: U-f I F Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U-f I F Γ [[ ↓ A ]])
    ->  Γ ==> Σ-f A B :: U-f I F Γ
U-f-Russell-sigma I F {Γ} A p B q  
    = mk-elt (U-f-Russell-sigma-lm I F {Γ} A p B q)



U-f-Russell-pi-lm : (I : Set) -> (F : I -> Set) 
    -> {Γ : ctx} 
    ->  (A : ty Γ) 
    ->  (p : Γ ==> A :: U-f I F Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U-f I F Γ [[ ↓ A ]])
    ->  (x :  || κ Γ ||)
    ->  apr (Π-f A B) x ∈ uV I F
U-f-Russell-pi-lm I F {Γ} A p B q x = 
  let lm : (apt (Π-f A B) x) ≐ piV (apt A x) (mk-Par-op-Fx A B x)
      lm = Π-f-exp1 {Γ} A B x
      lm2 : piV (apt A x) (mk-Par-op-Fx A B x) ∈ uV I F
      lm2 = piV-reflection I F (apt A x) (mk-Par-op-Fx A B x) 
                  (apel p x) (λ y → apel q (x , y))
      main : apr (Π-f A B) x ∈ uV I F
      main = memV-left-ext (apr (Π-f A B) x)  _ (uV I F)  lm lm2
  in main



U-f-Russell-pi : (I : Set) -> (F : I -> Set) 
    -> {Γ : ctx} 
    ->  (A : ty Γ) 
    ->  (p : Γ ==> A :: U-f I F Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U-f I F Γ [[ ↓ A ]])
    ->  Γ ==> Π-f A B :: U-f I F Γ
U-f-Russell-pi I F {Γ} A p B q  = mk-elt (U-f-Russell-pi-lm I F {Γ} A p B q)



U-f-Russell-ID-lm :  (I : Set) -> (F : I -> Set) 
     -> {Γ : ctx}
     -> (A : ty Γ)
     -> (p : Γ ==> A :: U-f I F Γ)
     -> (a : raw Γ)
     -> (qa : Γ ==> a :: A)
     -> (b : raw Γ)
     -> (qb : Γ ==> b :: A)
     -> (x : || κ Γ ||)
     -> apr (ID A a qa b qb) x ∈ uV I F
U-f-Russell-ID-lm I F {Γ} A p a qa b qb x =
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
      main : apr (ID A a qa b qb) x ∈ uV I F
      main = memV-left-ext (apr (ID A a qa b qb) x) (idV (apt A x) (pj1 (apel qa x)) (pj1 (apel qb x))) (uV I F)
               (traV lm lm2)
               (idV-reflection I F (apt A x) (pj1 (apel qa x)) (pj1 (apel qb x)) (apel p x))
  in main



U-f-Russell-ID :  (I : Set) -> (F : I -> Set) 
     -> {Γ : ctx}
     -> (A : ty Γ)
     -> (p : Γ ==> A :: U-f I F Γ)
     -> (a : raw Γ)
     -> (qa : Γ ==> a :: A)
     -> (b : raw Γ)
     -> (qb : Γ ==> b :: A)    
     -> Γ ==> ID A a qa b qb :: U-f I F Γ
U-f-Russell-ID I F {Γ} A p a qa b qb = mk-elt (U-f-Russell-ID-lm I F{Γ} A p a qa b qb)



U-f-Russell-N0 :  (I : Set) -> (F : I -> Set) 
      -> {Γ : ctx}
      -> Γ ==> N0 Γ :: U-f I F Γ
U-f-Russell-N0 I F {Γ} = mk-elt (λ x →  (zeroV-reflection I F))




U-f-Russell-Sum-lm :  (I : Set) -> (F : I -> Set) 
    -> {Γ : ctx} 
    ->  (A B : ty Γ) 
    ->  (p : Γ ==> A :: U-f I F Γ)
    ->  (q : Γ ==> B :: U-f I F Γ)
    ->  (x :  || κ Γ ||)
    ->  apr (Sum A B) x ∈ uV I F
U-f-Russell-Sum-lm I F {Γ} A B p q x = 
  let  lm : (apt (Sum A B) x) ≐ sumV (apt A x) (apt B x)
       lm =  refV _
       lm2 : sumV (apt A x) (apt B x) ∈ uV I F
       lm2 = sumV-reflection I F (apt A x) (apt B x) (apel p x) (apel q x)
       main : apr (Sum A B) x ∈ uV I F
       main = memV-left-ext (apr (Sum A B) x)  _ (uV I F)  lm lm2
  in main

U-f-Russell-Sum :  (I : Set) -> (F : I -> Set) 
    ->  {Γ : ctx} 
    ->  (A B : ty Γ) 
    ->  (p : Γ ==> A :: U-f I F Γ)
    ->  (q : Γ ==> B :: U-f I F Γ)
    ->  Γ ==> Sum A B :: U-f I F Γ
U-f-Russell-Sum I F {Γ} A B p q  
    = mk-elt (U-f-Russell-Sum-lm I F {Γ} A B p q)

-- instantiate the parameters I and F

I0 : Set
I0 = N₀
F0 : I0 -> Set
F0 = \x -> N₀

U-0 : (Γ : ctx)  -> ty Γ
U-0 Γ = U-f I0 F0 Γ

T-0 : {Γ : ctx}  -> (A : raw Γ)
     -> (Γ ==> A :: U-0 Γ)
-- --------------------------
     -> ty Γ
T-0 A p = A 


-- U-f I F Γ = Const (uV I F)  Γ
--  apr (U-0 Γ) x = uV I0 F0
-- uV : (I : Set) -> (F : I -> Set) -> V
-- uV I F = sup (sV I F) (emb I F)
-- sV I F = W (Uo I F) (To {I} {F})

-- sV I0 F0 = W (Uo I0 F0) (To {I0} {F0})
-- sV I1 F1 = W (Uo I1 F1) (To {I1} {F1})

-- uV I0 F0 = sup (sV I0 F0) (emb I0 F0)
-- uV I1 F1 = sup (sV I1 F1) (emb I1 F1)

-- emb :   (I : Set) -> (F : I -> Set) -> sV I F -> V 
-- emb I F (sup A f) = sup (To {I} {F} A) (\x -> emb I F (f x))








-- U-f I F Γ = Const (uV I F)  Γ
--  apr (U-0 Γ) x = uV I0 F0
-- uV : (I : Set) -> (F : I -> Set) -> V
-- uV I F = sup (sV I F) (emb I F)
-- sV I F = W (Uo I F) (To {I} {F})

-- sV I0 F0 = W (Uo I0 F0) (To {I0} {F0})
-- sV I1 F1 = W (Uo I1 F1) (To {I1} {F1})

-- uV I0 F0 = sup (sV I0 F0) (emb I0 F0)
-- uV I1 F1 = sup (sV I1 F1) (emb I1 F1)

-- emb :   (I : Set) -> (F : I -> Set) -> sV I F -> V 
-- emb I F (sup A f) = sup (To {I} {F} A) (\x -> emb I F (f x))


-- I0 : Set
-- I0 = N₀
-- F0 : I0 -> Set
-- F0 = \x -> N₀

I1 : Set
I1 = Uo I0 F0 -- # (uV I0 F0)
F1 : I1 -> Set
F1 = To {I0} {F0}  -- \x -> # ((uV I0 F0) ‣ x)


U-1 : (Γ : ctx)  -> ty Γ
U-1 Γ = U-f I1 F1 Γ

T-1 : {Γ : ctx}  -> (A : raw Γ)
     -> (Γ ==> A :: U-1 Γ)
-- --------------------------
     -> ty Γ
T-1 A p = A 



emb-W-W : (I : Set) -> (F : I -> Set) 
         -> (J : Set) -> (G : J -> Set)
         -> (h : I -> J) -> (g : (i : I) -> G (h i) -> F i )
         -> W I F -> W J G
emb-W-W I F J G h g (sup a f) = 
      sup (h a) (\x -> emb-W-W I F J G h g (f (g a x)))


-- (sV I0 F0)

-- (W I1 (λ x → F1 x))

-- looking for z


za :  Uo I1 F1
za = w ix lft

-- (sV I0 F0) =  (To za)

zf : To za → W (Uo I1 F1) To
zf v = emb-W-W I1 F1 (Uo I1 F1) (To {I1} {F1}) (λ x → lft x) (λ i x → x) v

zV : sV I1 F1
zV = sup za zf

zf-lm : (v : (sV I0 F0)) ->  emb I0 F0 v ≐  emb I1 F1 (zf v)
zf-lm (sup a f) = easy-eqV _ _ _ (λ x → zf-lm (f x))

emb-zV-le : sup (sV I0 F0) (emb I0 F0) ≤ emb I1 F1 zV
emb-zV-le v = v , (let lm : emb I0 F0 v ≐  emb I1 F1 (zf v)
                       lm = zf-lm v
                   in lm)

emb-zV-ge : sup (sV I0 F0) (emb I0 F0) ≥ emb I1 F1 zV
emb-zV-ge v = v , zf-lm v

emb-zV : sup (sV I0 F0) (emb I0 F0) ≐ emb I1 F1 zV
emb-zV = pair emb-zV-le emb-zV-ge

Cu-1a-lm2 : uV I0 F0 ∈ uV I1 F1
Cu-1a-lm2 = zV , emb-zV

Cu-1a : (Γ : ctx)  
     -> (Γ ==> U-0 Γ :: U-1 Γ)
Cu-1a Γ = mk-elt (λ x → Cu-1a-lm2)



transitive-uV : (I : Set) -> (F : I -> Set) -> (u : V) -> u ∈ uV I F -> u ⊆ uV I F
transitive-uV I F u (sup a f , p2) x q = 
    let lm : u ≐ emb I F (sup a f)
        lm = p2
        lm2 : x ∈ sup (To a) (λ x₁ → emb I F (f x₁))
        lm2 = memV-right-ext _ _ _ q lm
        lm3 : x ≐ emb I F (f (pj1 lm2))
        lm3 = pj2 lm2
        lm4 = (f (pj1 lm2))
        main : x ∈ uV I F
        main = lm4 , lm3
    in main 
  


Cu-1b-lm2 : uV I0 F0 ⊆ uV I1 F1
Cu-1b-lm2 = transitive-uV I1 F1 (uV I0 F0) Cu-1a-lm2

Cu-1b-lm : {Γ : ctx}  -> (A : raw Γ)
     -> (Γ ==> A :: U-0 Γ)
     -> (x : || κ Γ ||)
     -> apr A x ∈ apt (U-1 Γ) x
Cu-1b-lm {Γ} A p x  = 
    let r : apr A x ∈ apt (U-0 Γ) x
        r = apel p x
        main : apr A x ∈ apt (U-1 Γ) x
        main = Cu-1b-lm2 (apr A x) r
    in main



Cu-1b : {Γ : ctx}  -> (A : raw Γ)
     -> (Γ ==> A :: U-0 Γ)
     -> (Γ ==> A :: U-1 Γ)
Cu-1b {Γ} A p = mk-elt (λ x → Cu-1b-lm {Γ} A p x)


-- Infinite hierarchy of Russell universes


mutual

  I- : (k : N) -> Set
  I- O = I0
  I- (s k) = Uo (I- k) (F- k)

  F- : (k : N) -> I- k -> Set
  F- O = F0
  F- (s k) = To {I- k} {F- k}


U- : (k : N) -> (Γ : ctx)  -> ty Γ
U- k Γ = U-f (I- k) (F- k) Γ

T- : (k : N) -> {Γ : ctx}  -> (A : raw Γ)
     -> (Γ ==> A :: U- k Γ)
-- --------------------------
     -> ty Γ
T- k {Γ} A p = A 



-- Cumulativity


za- :  (k : N) -> Uo (I- k) (F- k)
za- k = w ix lft


zf- : (k : N) -> To (za- k) ->  W (Uo (I- k) (F- k)) To
zf- k v = emb-W-W (I- k) (F- k) (Uo (I- k) (F- k)) (To {I- k} {F- k}) (λ x → lft x) (λ i x → x) v



zV- : (k : N) -> sV (I- k) (F- k)
zV- k = sup (za- k) (zf- k)



zf-lm- : (k : N) -> (v : (sV (I- k) (F- k))) ->  
          emb (I- k) (F- k) v ≐  emb (I- (s k)) (F- (s k)) (zf- (s k) v)
zf-lm- k (sup a f) = easy-eqV _ _ _ (λ x → zf-lm- k (f x))



emb-zV-le- : (k : N) -> sup (sV (I- k) (F- k)) (emb (I- k) (F- k)) ≤ emb (I- (s k)) (F- (s k)) (zV- (s k))
emb-zV-le- k v = v , (let lm : emb (I- k) (F- k) v ≐  emb (I- (s k)) (F- (s k))  (zf- (s k) v)
                          lm = zf-lm- k v
                      in lm)

 
emb-zV-ge- : (k : N) -> sup (sV (I- k) (F- k)) (emb (I- k) (F- k)) ≥ emb  (I- (s k)) (F- (s k)) (zV- (s k))
emb-zV-ge- k v = v , zf-lm- k v


emb-zV- : (k : N) -> sup (sV (I- k) (F- k)) (emb (I- k) (F- k)) ≐  emb  (I- (s k)) (F- (s k)) (zV- (s k))
emb-zV- k = pair (emb-zV-le- k) (emb-zV-ge- k)


Cu-1a-lm2- : (k : N) -> uV (I- k) (F- k) ∈ uV (I- (s k)) (F- (s k))
Cu-1a-lm2- k = (zV- (s k)) , (emb-zV- k)

Cu-1a- : (k : N) -> (Γ : ctx)  
     -> (Γ ==> U- k Γ :: U- (s k) Γ)
Cu-1a- k Γ = mk-elt (λ x → Cu-1a-lm2- k)



Cu-1b-lm2- : (k : N) -> uV (I- k) (F- k) ⊆ uV (I- (s k)) (F- (s k))
Cu-1b-lm2- k = transitive-uV (I- (s k)) (F- (s k)) (uV (I- k) (F- k)) (Cu-1a-lm2- k)


Cu-1b-lm- :  (k : N) -> {Γ : ctx}  -> (A : raw Γ)
     -> (Γ ==> A :: U- k Γ)
     -> (x : || κ Γ ||)
     -> apr A x ∈ apt (U- (s k) Γ) x
Cu-1b-lm- k {Γ} A p x  = 
    let r : apr A x ∈ apt (U- k Γ) x
        r = apel p x
        main : apr A x ∈ apt (U- (s k) Γ) x
        main = Cu-1b-lm2- k (apr A x) r
    in main

Cu-1b- : (k : N) -> {Γ : ctx}  -> (A : raw Γ)
     -> (Γ ==> A :: U- k Γ)
     -> (Γ ==> A :: U- (s k) Γ)
Cu-1b- k {Γ} A p = mk-elt (λ x → Cu-1b-lm- k {Γ} A p x)


-- Closure rules

T-eq- : (k : N) 
     -> {Γ : ctx}  -> (A : raw Γ)
     -> (p : Γ ==> A :: U- k  Γ)
-- -------------------------------
     ->  Γ ==> T- k A p == A
--
T-eq- k {Γ} A p = tyrefl A

U-sub- : (k : N)  
     ->  (Δ Γ : ctx)  -> (f : subst Δ Γ)
     ->  Δ ==> (U- k Γ) [[ f ]] == U- k  Δ
U-sub- k Δ Γ f = mk-eqty (λ x → <<>> (refV _))


U-nat- :  (k : N) -> (Γ : ctx) 
-- -----------------------------------
    -> Γ ==> Nat Γ :: U- k Γ
--
U-nat- k Γ = mk-elt (λ x → natV-in-uV (I- k) (F- k))  



U-sigma-lm- : (k : N) 
    -> {Γ : ctx} 
    ->  (A : ty Γ) 
    ->  (p : Γ ==> A :: U- k Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U- k Γ [[ ↓ A ]])
    ->  (x :  || κ Γ ||)
    ->  apr (Σ-f A B) x ∈ uV (I- k) (F- k)
U-sigma-lm- k {Γ} A p B q x = 
  let lm : (apt (Σ-f A B) x) ≐ sigmaV (apt A x) (mk-Par-op-Fx A B x)
      lm = Σ-f-exp1 {Γ} A B x
      lm2 : sigmaV (apt A x) (mk-Par-op-Fx A B x) ∈ uV (I- k) (F- k)
      lm2 = sigmaV-reflection (I- k) (F- k) (apt A x) (mk-Par-op-Fx A B x) 
                  (apel p x) (λ y → apel q (x , y))
      main : apr (Σ-f A B) x ∈ uV (I- k) (F- k)
      main = memV-left-ext (apr (Σ-f A B) x)  _ (uV (I- k) (F- k))  lm lm2
  in main



U-sigma- : (k : N)  
    -> {Γ : ctx} 
    ->  (A : ty Γ) 
    ->  (p : Γ ==> A :: U- k Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U- k Γ [[ ↓ A ]])
    ->  Γ ==> Σ-f A B :: U- k Γ
U-sigma- k {Γ} A p B q  
    = mk-elt (U-sigma-lm- k {Γ} A p B q)




U-pi-lm- :  (k : N)  
    -> {Γ : ctx} 
    ->  (A : ty Γ) 
    ->  (p : Γ ==> A :: U- k Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U- k Γ [[ ↓ A ]])
    ->  (x :  || κ Γ ||)
    ->  apr (Π-f A B) x ∈ uV (I- k) (F- k)
U-pi-lm- k {Γ} A p B q x = 
  let lm : (apt (Π-f A B) x) ≐ piV (apt A x) (mk-Par-op-Fx A B x)
      lm = Π-f-exp1 {Γ} A B x
      lm2 : piV (apt A x) (mk-Par-op-Fx A B x) ∈ uV (I- k) (F- k)
      lm2 = piV-reflection  (I- k) (F- k) (apt A x) (mk-Par-op-Fx A B x) 
                  (apel p x) (λ y → apel q (x , y))
      main : apr (Π-f A B) x ∈ uV  (I- k) (F- k)
      main = memV-left-ext (apr (Π-f A B) x)  _ (uV (I- k) (F- k))  lm lm2
  in main



U-pi- : (k : N) 
    -> {Γ : ctx} 
    ->  (A : ty Γ) 
    ->  (p : Γ ==> A :: U- k Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U- k Γ [[ ↓ A ]])
    ->  Γ ==> Π-f A B :: U- k Γ
U-pi- k {Γ} A p B q  = mk-elt (U-pi-lm- k {Γ} A p B q)




U-ID-lm- : (k : N) 
     -> {Γ : ctx}
     -> (A : ty Γ)
     -> (p : Γ ==> A :: U- k Γ)
     -> (a : raw Γ)
     -> (qa : Γ ==> a :: A)
     -> (b : raw Γ)
     -> (qb : Γ ==> b :: A)
     -> (x : || κ Γ ||)
     -> apr (ID A a qa b qb) x ∈ uV (I- k) (F- k)
U-ID-lm- k {Γ} A p a qa b qb x =
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
      main : apr (ID A a qa b qb) x ∈ uV (I- k) (F- k)
      main = memV-left-ext (apr (ID A a qa b qb) x) 
               (idV (apt A x) (pj1 (apel qa x)) (pj1 (apel qb x))) (uV (I- k) (F- k))
               (traV lm lm2)
               (idV-reflection (I- k) (F- k) (apt A x) (pj1 (apel qa x)) (pj1 (apel qb x)) (apel p x))
  in main


U-ID- :  (k : N) 
     -> {Γ : ctx}
     -> (A : ty Γ)
     -> (p : Γ ==> A :: U- k Γ)
     -> (a : raw Γ)
     -> (qa : Γ ==> a :: A)
     -> (b : raw Γ)
     -> (qb : Γ ==> b :: A)    
     -> Γ ==> ID A a qa b qb :: U- k Γ
U-ID- k {Γ} A p a qa b qb = mk-elt (U-ID-lm- k {Γ} A p a qa b qb)



U-N0- :  (k : N)
      -> {Γ : ctx}
      -> Γ ==> N0 Γ :: U- k Γ
U-N0- k {Γ} = mk-elt (λ x →  (zeroV-reflection (I- k) (F- k)))


U-Sum-lm- :  (k : N) 
    ->  {Γ : ctx} 
    ->  (A B : ty Γ) 
    ->  (p : Γ ==> A :: U- k Γ)
    ->  (q : Γ ==> B :: U- k Γ)
    ->  (x :  || κ Γ ||)
    ->  apr (Sum A B) x ∈ uV (I- k) (F- k)
U-Sum-lm- k {Γ} A B p q x = 
  let  lm : (apt (Sum A B) x) ≐ sumV (apt A x) (apt B x)
       lm =  refV _
       lm2 : sumV (apt A x) (apt B x) ∈ uV  (I- k) (F- k)
       lm2 = sumV-reflection (I- k) (F- k) (apt A x) (apt B x) (apel p x) (apel q x)
       main : apr (Sum A B) x ∈ uV (I- k) (F- k)
       main = memV-left-ext (apr (Sum A B) x)  _ (uV (I- k) (F- k))  lm lm2
  in main

U-Sum- :  (k : N)
    ->  {Γ : ctx} 
    ->  (A B : ty Γ) 
    ->  (p : Γ ==> A :: U- k Γ)
    ->  (q : Γ ==> B :: U- k Γ)
    ->  Γ ==> Sum A B :: U- k Γ
U-Sum- k {Γ} A B p q  
    = mk-elt (U-Sum-lm- k {Γ} A B p q)

-- reflection of type equalities

U-eq-refl1 :  (k : N)
    ->  {Γ : ctx} 
    ->  (A B : ty Γ) 
    ->  (p : Γ ==> A :: U- k Γ)
    ->  (q : Γ ==> B :: U- k Γ)
    ->  (Γ ==> A == B)
    ->  Γ ==> A == B :: U- k Γ
U-eq-refl1 k {Γ} A B p q r = pair (Raw-lm (eq-from-tyeq A B r)) (pair p q)

U-eq-refl2 :  (k : N)
    ->  {Γ : ctx} 
    ->  (A B : ty Γ) 
    ->  (p : Γ ==> A :: U- k Γ)
    ->  (q : Γ ==> B :: U- k Γ)
    ->  (Γ ==> A == B :: U- k Γ)
    ->  Γ ==> A == B
U-eq-refl2 k {Γ} A B p q r = mk-eqty (λ x → <<>> (prj1 r x))

