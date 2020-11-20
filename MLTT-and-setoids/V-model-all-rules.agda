-- disable the K axiom:


{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-all-rules where

open import basic-types
open import basic-setoids       
open import dependent-setoids   
open import subsetoids          
open import iterative-sets      
open import iterative-sets-pt2  
open import iterative-sets-pt3  
open import iterative-sets-pt4
open import iterative-sets-pt5 
open import iterative-sets-pt6
open import iterative-sets-pt8
open import V-model-pt0
open import V-model-pt1         
open import V-model-pt2         
open import V-model-pt3         
open import V-model-pt4         
open import V-model-pt5         
open import V-model-pt6         
open import V-model-pt7         
open import V-model-pt8         
open import V-model-pt9         
open import V-model-pt10
open import V-model-pt13
open import V-model-pt11
open import V-model-pt15

-- Summary of interpreted rules

E1-tyrefl :  {Γ : ctx} 
--
         -> (A : ty Γ) 
-- ------------------------
         -> Γ ==> A == A
--
E1-tyrefl =  tyrefl

E2-tysym :  {Γ : ctx} -> {A B : ty Γ} 
--
         -> Γ ==> A == B 
--   -------------------------- 
         -> Γ ==> B == A
--
E2-tysym = tysym 


E3-tytra :  {Γ : ctx} -> {A B C : ty Γ} 
--
         -> Γ ==> A == B  -> Γ ==> B == C 
--  -------------------------------------
                -> Γ ==> A == C
--
E3-tytra = tytra 

E4-tmrefl :  {Γ : ctx} -> {A : ty Γ}-> {a : raw Γ}
--
         -> Γ ==> a :: A  
--    ------------------------
         -> Γ ==> a == a :: A
--
E4-tmrefl = tmrefl 

E5-tmsym :  {Γ : ctx} -> (A : ty Γ) -> (a b : raw Γ) 
--
         -> Γ ==> a == b :: A 
--    ------------------------
         -> Γ ==> b == a :: A
--
E5-tmsym = tmsym 


E6-tmtra :  {Γ : ctx} -> (A : ty Γ) -> (a b c : raw Γ) 
--
         -> Γ ==> a == b :: A   -> Γ ==> b == c :: A 
--  --------------------------------------------------
         -> Γ ==> a == c :: A
--
E6-tmtra = tmtra








E10-elttyeq :  {Γ : ctx} ->  {a : raw Γ}  -> {A B : ty Γ} 
--
      -> Γ ==> a :: A     -> Γ ==> A == B 
--  --------------------------------------------
              -> Γ ==> a :: B
--
E10-elttyeq =  elttyeq 

E11-elteqtyeq :  {Γ : ctx} ->  (a b : raw Γ)  -> (A B : ty Γ) 
--
      -> Γ ==>  a == b :: A    -> Γ ==> A == B 
--  ---------------------------------------------
              -> Γ ==>  a == b :: B
--
E11-elteqtyeq = elteqtyeq


E12-subj-red : {Γ : ctx} -> {A : ty Γ} ->  (a b : raw Γ)
--
     -> Γ ==> a :: A    ->  << Raw Γ >> a ~ b
--   -------------------------
     -> Γ ==> b :: A
--
E12-subj-red  = subj-red 


S1-sub-id-prop : {Γ : ctx}  
--
         -> (a : raw Γ) 
--    ---------------------------------
      ->  << Raw Γ >> a [ ids ] ~ a  
-- 
S1-sub-id-prop = sub-id-prop


S2-sub-comp-prop : {Θ Δ Γ : ctx}  
--
       -> (a : raw Γ) 
       -> (f : subst Δ Γ) -> (g : subst Θ Δ) 
-- --------------------------------------------------
      -> << Raw Θ >>  a [ f ⌢ g ]  ~ (a [ f ] [ g ])
--
S2-sub-comp-prop = sub-comp-prop

-- substitution of ctx-trp in to a

S3-subst-trp : {Γ Δ : ctx} 
--
     ->  (p : << Ctx >> Γ ~ Δ) 
-- -------------------------------
     -> subst Γ Δ
S3-subst-trp = subst-trp

S4-sub-trp-prop : {Γ : ctx}  
--
    -> (a : raw Γ)   ->  (p : << Ctx >> Γ ~ Γ) 
-- ---------------------------------------------
    -> << Raw Γ >> a [ subst-trp p ]  ~ a
--
S4-sub-trp-prop = sub-trp-prop


S5-Sub-id-prop : {Γ : ctx}  
--
        -> (A : ty Γ)
-- -----------------------------------
      ->  << Ty Γ >> A [[ ids ]] ~ A   
--
S5-Sub-id-prop  = Sub-id-prop

S6-Sub-comp-prop : {Θ Δ Γ : ctx}  
--
       -> (A : ty Γ) 
       ->  (f : subst Δ Γ) -> (g : subst Θ Δ) ->
-- -------------------------------------------------------
       << Ty Θ >>  A [[ f ⌢ g ]]  ~ (A [[ f ]] [[ g ]])
--
S6-Sub-comp-prop = Sub-comp-prop


S7-tyeq-subst :  {Δ Γ : ctx} -> {A B : ty Γ} -> (f : subst Δ Γ) 
--
                  -> Γ ==> A == B 
--      -------------------------------------------------- 
         -> Δ ==> A [[ f ]] ==  B [[ f ]]
--
S7-tyeq-subst = tyeq-subst

S8-elt-subst :  {Δ Γ : ctx} -> {a : raw Γ} -> {A : ty Γ} -> (f : subst Δ Γ) 
--
          -> Γ ==> a :: A 
--   -------------------------------------------------------- 
         -> Δ ==> a [ f ] ::  A [[ f ]]
--
S8-elt-subst = elt-subst


S9-elteq-subst :  {Δ Γ : ctx} -> {a b : raw Γ} -> {A : ty Γ} 
--
          -> (f : subst Δ Γ)   -> Γ ==> a == b :: A 
--   --------------------------------------------------------------------------
         -> Δ ==> a [ f ] == b [ f ] :: A [[ f ]]
--
S9-elteq-subst = elteq-subst


S10-tyeq-subst2 :  {Δ Γ : ctx}
--
        -> (A : ty Γ)   -> (f g : subst Δ Γ)    -> < Subst Δ Γ > f ~ g
--      -------------------------------------------------- 
         -> Δ ==> A [[ f ]] ==  A [[ g ]]
--
S10-tyeq-subst2 = tyeq-subst2

S9b-elteq-subst2 :  {Δ Γ : ctx} -> {a  : raw Γ} -> {A : ty Γ} -> (f  g : subst Δ Γ) 
--
           -> Γ ==> a :: A
           -> < Subst Δ Γ > f ~ g
--   --------------------------------------------------------------------------
         -> Δ ==> a [ f ] == a [ g ] :: A [[ f ]]
--
S9b-elteq-subst2 = elteq-subst2

S11-tysubst-id : {Γ : ctx}
--
        -> (A  : ty Γ) 
--   -------------------------
     -> Γ ==> (A [[ ids ]]) == A
--
S11-tysubst-id = tysubst-id 

S12-tysubst-com : {Θ Δ Γ : ctx}
--
    -> (A : ty Γ)    -> (f : subst Δ Γ)  -> (g : subst Θ Δ)
--   -------------------------
     -> Θ ==> (A [[ f ⌢ g ]]) == (A [[ f ]] [[ g ]])
--
S12-tysubst-com = tysubst-com



S13-eltsubst-id : {Γ : ctx}
--
    -> (A  : ty Γ)  ->  (a : raw Γ)  -> Γ ==> a :: A
--   ---------------------------
     -> Γ ==> (a [ ids ]) == a :: A
--
S13-eltsubst-id = eltsubst-id


S14-eltsubst-com : {Θ Δ Γ : ctx}
--
    -> (A : ty Γ)
    -> (f : subst Δ Γ)  -> (g : subst Θ Δ)
    -> (a : raw Γ)
    -> Γ ==> a :: A
--   -------------------------
     -> Θ ==> (a [ f ⌢ g ]) == (a [ f ] [ g ]) :: (A [[ f ⌢ g ]])
--
S14-eltsubst-com = eltsubst-com


S15-subst-trp-id :  {Γ : ctx} 
--
       ->  (p : << Ctx >> Γ ~ Γ) 
-- -------------------------------------------
      -> < Subst Γ Γ > subst-trp p ~ ids {Γ}
--
S15-subst-trp-id = subst-trp-id

S16-subst-trp-irr :  {Γ Δ : ctx}
-- 
      ->  (p q : << Ctx >> Γ ~ Δ) 
-- ----------------------------------------------
      -> < Subst Γ Δ > subst-trp p ~ subst-trp q
--
S16-subst-trp-irr  = subst-trp-irr 

S17-subst-trp-fun :  {Γ Δ  Θ : ctx} 
-- 
    ->  (p : << Ctx >> Γ ~ Δ)   ->  (q : << Ctx >> Δ ~ Θ) 
    ->  (r : << Ctx >> Γ ~ Θ)
-- ----------------------------------------------------------------
    -> < Subst Γ Θ > ((subst-trp q) ⌢ (subst-trp p)) ~ subst-trp r
--
S17-subst-trp-fun = subst-trp-fun



C1-↓ : {Γ : ctx} 
-- 
      -> (A : ty Γ) 
-- ---------------------
     -> subst (Γ ▷ A) Γ
--
C1-↓ = ↓

C2-asm : {Γ : ctx}
--
      -> (A : ty Γ) 
--   --------------------------------------------------------
      -> Γ ▷ A ==> vv A :: A [[ ↓ A ]]
--
C2-asm = asm

C3-ext : {Δ Γ : ctx} 
--
      -> (A : ty Γ) 
      -> (f : subst Δ Γ) -> (a : raw Δ) 
      -> Δ ==> a :: A [[ f ]]
-- ------------------------------------
      -> subst Δ (Γ ▷ A)
--
C3-ext = ext

C4-ext-irr : {Δ Γ : ctx} 
--
      -> (A : ty Γ) 
      -> (f : subst Δ Γ) -> (a : raw Δ) 
      -> (p : Δ ==> a :: A [[ f ]])
      -> (q : Δ ==> a :: A [[ f ]])
-- ----------------------------------------
      -> < Subst Δ (Γ ▷ A) >  (ext A f a p) ~  (ext A f a q) 
--
C4-ext-irr = ext-irr

C5-ext-prop1 : {Δ Γ : ctx} 
--
      -> (A : ty Γ) 
      -> (f : subst Δ Γ) -> (a : raw Δ) 
      -> (p : Δ ==> a :: A [[ f ]])
-- ----------------------------------------------------
      -> < Subst Δ Γ >  ((↓ A) ⌢ (ext A f a p)) ~ f
--
C5-ext-prop1 = ext-prop1

C6-ext-prop2 : {Δ Γ : ctx} 
--
      -> (A : ty Γ) 
      ->  (f : subst Δ Γ) -> (a : raw Δ) 
      -> (p : Δ ==> a :: A [[ f ]])
-- ----------------------------------------------------
      -> << Raw Δ >>  (vv A) [ ext A f a p ] ~ a
C6-ext-prop2 = ext-prop2


C7-ext-prop3 : {Γ : ctx} 
--
       -> (A : ty Γ) 
-- -----------------------------------------------------------------------------
     ->   < Subst (Γ ▷ A) (Γ ▷ A) >  (ext A (↓ A) (vv A) (asm A)) ~ ids {Γ ▷ A}
--
C7-ext-prop3 = ext-prop3


C9-ext-prop4 : {Θ Δ Γ : ctx} 
--
      -> (A : ty Γ) 
      -> (f : subst Δ Γ) -> (a : raw Δ) 
      -> (p : Δ ==> a :: A [[ f ]])
      -> (h : subst Θ Δ)
--  --------------------------
      -> < Subst Θ (Γ ▷ A) > ((ext A f a p) ⌢ h) ~
                               (ext A (f ⌢ h) (a [ h ]) (ext-prop4-lm  A f a p h ))
--
C9-ext-prop4 = ext-prop4


C10-ext-prop4-gen : {Θ Δ Γ : ctx} -> (A : ty Γ) 
      -> (f : subst Δ Γ) -> (a : raw Δ) 
      -> (p : Δ ==> a :: A [[ f ]])
      -> (h : subst Θ Δ)
      -> (q : Θ ==> a [ h ] :: A [[ f ⌢ h ]])
--    --------------------------------------------
      -> < Subst Θ (Γ ▷ A) > ((ext A f a p) ⌢ h) ~ (ext A (f ⌢ h) (a [ h ]) q)
--
C10-ext-prop4-gen = ext-prop4-lm2 


C10-ext-eq : {Γ : ctx}
--
      -> (A  A' : ty Γ) 
      -> (Γ ==> A == A')
-- --------------------------
      -> (Γ ▷ A) ≐ (Γ ▷ A')
--
C10-ext-eq = ext-eq



C11-els  :  
       {Γ : ctx} 
--
    -> {A : ty Γ}   
    -> {a : raw Γ}
    -> (Γ ==> a :: A)
-- -------------------------
    -> subst Γ (Γ ▷ A)
--
C11-els = els


C12-↑ :  {Δ Γ : ctx}  
--
    -> (A : ty Γ)    -> (h : subst Δ Γ) 
-- -------------------------------------
     -> subst (Δ ▷ (A [[ h ]])) (Γ ▷ A)
--
C12-↑ = ↑ 


P1-Π-f :  {Γ : ctx} 
--
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
--     ---------------------------------------
       -> ty Γ
-- 
P1-Π-f = Π-f

P2-Π-f-rcong :  {Γ : ctx} 
--
       -> (A : ty Γ)   -> (B B' : ty (Γ ▷ A))
       -> (Γ ▷ A ==> B == B')
--     ---------------------------------------
       -> (Γ  ==>  Π-f A B == Π-f A B')
P2-Π-f-rcong = Π-f-rcong

P3-Π-i  :  {Γ : ctx} 
--
       -> (A : ty Γ)   -> {B : ty (Γ ▷ A)}
       -> {b : raw (Γ ▷ A)}
       -> Γ ▷ A ==> b :: B
--  -----------------------------------------
        -> Γ ==> lambda A B b :: Π-f A B
-- 
P3-Π-i = Π-i


P4-Π-xi  :  {Γ : ctx} 
       -> (A : ty Γ)   -> {B : ty (Γ ▷ A)}
       -> {b : raw (Γ ▷ A)}
       -> {b' : raw (Γ ▷ A)}
       -> (r : Γ ▷ A ==> b == b' :: B)
--  -----------------------------------------
        -> Γ ==> lambda A B b ==  lambda A B b' :: Π-f A B
-- 
P4-Π-xi = Π-xi


P5-Π-e :  {Γ : ctx} 
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (q : Γ ==> a :: A)
--  -----------------------------------------
    ->  Γ ==> app A B c p a q :: B [[ els q ]]
--
P5-Π-e = Π-e 

P6-Π-e-cong :  {Γ : ctx} 
--
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c c' : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (p' : Γ ==> c' :: Π-f {Γ} A B)
    -> (Γ ==> c == c' :: Π-f {Γ} A B)
    -> (a a' : raw Γ)
    -> (q : Γ ==> a :: A)
    -> (q' : Γ ==> a' :: A)
    -> (Γ ==> a == a' :: A)
--  -----------------------------------------
    ->  Γ ==> app A B c p a q == app A B c' p' a' q'  :: B [[ els q ]]
--
P6-Π-e-cong = Π-e-cong 

P7-Π-beta :  {Γ : ctx} 
--
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (b : raw (Γ ▷ A))
       -> (p : Γ ▷ A ==> b :: B)
       -> (a : raw Γ)
       -> (q : Γ ==> a :: A)
--  -----------------------------------------
       ->  Γ ==> app A B (lambda A B b) (Π-i A p) a q  
             ==  b [ els q ] :: B [[ els q ]]
--
P7-Π-beta = Π-beta

P8-Π-beta-gen :  {Γ : ctx} 
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (b : raw (Γ ▷ A))
       -> (p : Γ ▷ A ==> b :: B)
       -> (r : Γ  ==> (lambda A B b) :: Π-f {Γ} A B)
       -> (a : raw Γ)
       -> (q : Γ ==> a :: A)
--  -----------------------------------------
       ->  Γ ==> app A B (lambda A B b) r a q  
             ==  b [ els q ] :: B [[ els q ]]
--
P8-Π-beta-gen = Π-beta-gen




P9-Π-f-sub :  {Δ Γ : ctx} 
--
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))  -> (h : subst Δ Γ) 
--     ---------------------------------------
       -> Δ ==>  (Π-f A B) [[ h ]] ==  Π-f (A [[ h ]]) (B [[ ↑ A h ]]) 
--
P9-Π-f-sub = Π-f-sub 

P10-lambda-sub  :  {Δ Γ : ctx} 
--
       -> (A : ty Γ)   -> {B : ty (Γ ▷ A)}
       -> {b : raw (Γ ▷ A)}
       -> (h : subst Δ Γ)
       -> Γ ▷ A ==> b :: B
--  -----------------------------------------
       -> Δ ==> (lambda A B b) [ h ] ==
                (lambda (A [[ h ]]) (B [[ ↑ A h ]]) (b [ ↑ A h ]))  :: (Π-f A B) [[ h ]]
--
P10-lambda-sub = lambda-sub



P11-Π-eta-left2 :  {Γ : ctx}  
--
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
-- -------------------------------------
    -> (Γ ▷ A) ==> vv A ::  A [[ ↓ A ]]
--
P11-Π-eta-left2 = Π-eta-left2

P12-Π-eta-left3 :  {Γ : ctx}  
--
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
-- --------------------------------------------------------------------------------
    -> (Γ ▷ A) ==> (c [ ↓ A ]) ::   (Π-f {Γ ▷ A} (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]))  
--  
P12-Π-eta-left3 = Π-eta-left3 


P13-Π-eta-eq :  {Γ : ctx}  
--
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
-- ------------------------------------------------------
    -> Γ ==> lambda A B (app (A [[ ↓ A ]]) 
                             (B [[ ↑ A (↓ A) ]])
                             (c [ ↓ A ])
                             (Π-eta-left3 {Γ} A B c p)  
                             (vv A) 
                             (Π-eta-left2 {Γ} A B c p))  
             == c ::  Π-f {Γ} A B
--
P13-Π-eta-eq = Π-eta-eq

-- More general rule where RHS doesn't depend on Π-eta-left{3,2}:

P14-Π-eta-eq-gen :  {Γ : ctx}  
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)

    -> (q1 : (Γ ▷ A) ==> vv A ::  A [[ ↓ A ]])
    -> (q2 : (Γ ▷ A) ==> (c [ ↓ A ]) ::   (Π-f {Γ ▷ A} (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])))     
    -> Γ ==> lambda A B (app (A [[ ↓ A ]]) 
                             (B [[ ↑ A (↓ A) ]])
                             (c [ ↓ A ])
                             q2  
                             (vv A) 
                             q1)  
             == c ::  Π-f {Γ} A B
P14-Π-eta-eq-gen = Π-eta-eq-gen


P15-Π-f-cong : {Γ : ctx}
--
      -> (A  A' : ty Γ) 
      -> (p : Γ ==> A == A')
      -> (B : ty (Γ ▷ A))
      -> (B' : ty (Γ ▷ A'))
      -> (Γ ▷ A ==> B == (B' [[  subst-trp (ext-eq' A A' p) ]]))
-- ---------------------
      -> Γ ==> Π-f A B == Π-f A' B'
--
P15-Π-f-cong = Π-f-cong

-- Perhaps more general rule ?



I1-ID : {Γ : ctx}
--
     -> (A : ty Γ) 
     -> (a : raw Γ)
     -> (p : Γ ==> a :: A)
     -> (b : raw Γ)
     -> (q : Γ ==> b :: A)   
-- ----------------------------- 
     -> ty Γ

I1-ID = ID

I2-ID-i : {Γ : ctx}
--
     -> (A : ty Γ)
     -> (a : raw Γ)
     -> (p : Γ ==> a :: A)
-- --------------------------------------
     -> Γ ==> (rr {Γ} a) :: (ID A a p a p)
--
I2-ID-i = ID-i

I3-ID-e : {Γ : ctx}
-- 
     -> (A : ty Γ)
     -> (a b t : raw Γ)
     -> (p : Γ ==> a :: A)
     -> (q : Γ ==> b :: A)
     -> (Γ ==> t :: (ID A a p b q))
-- -----------------------------------------
     -> Γ ==> a == b :: A
--
I3-ID-e = ID-e

I4-ID-uip : {Γ : ctx}
-- 
     -> (A : ty Γ)
     -> (a b t : raw Γ)
     -> (p : Γ ==> a :: A)
     -> (r : Γ ==> a :: A)
     -> (Γ ==> t :: (ID A a p a r))
-- ------------------------------------------
     -> Γ ==> t == (rr {Γ} a) :: (ID A a p a r)
--
I4-ID-uip = ID-uip


I5-rr-sub :  {Δ Γ : ctx}
--
     -> (h : subst Δ Γ)
     -> (A : ty Γ)
     -> (a : raw Γ)    
     -> (p : Γ ==> a :: A)
-- ---------------------------------------------
     -> Δ ==> (rr a) [ h ] == rr (a [ h ]) ::  (ID A a p a p) [[ h ]]
--
I5-rr-sub = rr-sub



I6-rr-cong :  {Γ : ctx}
--
     -> (A : ty Γ)
     -> (a  b : raw Γ) 
     -> (p : Γ ==> a :: A)
     -> (Γ ==> a == b :: A)
-- --------------------------------
     -> Γ ==> (rr a) == (rr b) ::  (ID A a p a p) 
--
I6-rr-cong = rr-cong

I7-ID-sub :  {Δ Γ : ctx}
--
     -> (h : subst Δ Γ)
     -> (A : ty Γ)
     -> (a : raw Γ) 
     -> (pa : Γ ==> a :: A) 
     -> (b : raw Γ) 
     -> (pb : Γ ==> b :: A) 
-- --------------------------------------------------------------------------
     -> << Ty Δ >> (ID A a pa b pb) [[ h ]] ~
           (ID (A [[ h ]]) (a [ h ]) (elt-subst h pa) (b [ h ]) (elt-subst h pb))
-- 
I7-ID-sub = ID-sub

-- More general rule where RHS doesn't depend on elt-subst:




I8-ID-sub-gen :  {Δ Γ : ctx}
     -> (h : subst Δ Γ)
     -> (A : ty Γ)
     -> (a : raw Γ) 
     -> (pa : Γ ==> a :: A) 
     -> (b : raw Γ) 
     -> (pb : Γ ==> b :: A) 
     -> (q : Δ ==> a [ h ] :: A [[ h ]])
     -> (r : Δ ==> b [ h ] :: A [[ h ]])
     -> Δ ==>  (ID A a pa b pb) [[ h ]] == (ID (A [[ h ]]) (a [ h ]) q (b [ h ]) r)
I8-ID-sub-gen =  ID-sub-gen





I9-ID-cong :  {Γ : ctx}
--
     -> (A A' : ty Γ)
     -> (a b a' b' : raw Γ) 
     -> (pa : Γ ==> a :: A)
     -> (pa' : Γ ==> a' :: A')
     -> (pb : Γ ==> b :: A)
     -> (pb' : Γ ==> b' :: A')
     -> (q : Γ ==>  A == A')
     -> (Γ ==> a ==  a' :: A')
     -> (Γ ==> b ==  b' :: A')
-- ------------------------------------------
     -> Γ ==> ID A a pa b pb == ID A' a' pa' b' pb'
I9-ID-cong = ID-cong



Sg1-Σ-f :  {Γ : ctx} 
--
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
-- -------------------------------------------
       -> ty Γ
--
Sg1-Σ-f = Σ-f

Sg2-Σ-f-cong : {Γ : ctx}
--
      -> (A  A' : ty Γ) 
      -> (p : Γ ==> A == A')
      -> (B : ty (Γ ▷ A))
      -> (B' : ty (Γ ▷ A'))
      -> (Γ ▷ A ==> B == (B' [[  subst-trp (ext-eq' A A' p) ]]))
-- --------------------------------------------------------------
      -> Γ ==> Σ-f A B == Σ-f A' B'
--
Sg2-Σ-f-cong = Σ-f-cong

-- Possibly find a more general rule for the above

Sg3-Σ-i : {Γ : ctx}
--
      -> (A  : ty Γ) 
      -> (B : ty (Γ ▷ A))
      -> (a  : raw Γ) 
      -> (p : Γ ==> a :: A)
      -> (b : raw Γ)
      -> (Γ ==> b :: (B [[ els p ]]))
-- --------------------------------------
      -> Γ ==> pr a b :: Σ-f A B
--
Sg3-Σ-i = Σ-i

Sg4-Σ-e-1 : {Γ : ctx}
--
      -> (A  : ty Γ) 
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
-- -------------------------------------------
      -> Γ ==> pr1 A B c p :: A
--
Sg4-Σ-e-1  = Σ-e-1 

Sg5-Σ-e-2 : {Γ : ctx}
--
      -> (A  : ty Γ) 
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (q : Γ ==> pr1 A B c p :: A)
-- --------------------------------------------
      -> Γ ==> pr2 A B c p :: B [[ els q ]]
--
Sg5-Σ-e-2 = Σ-e-2 

Sg6-Σ-c-1 : {Γ : ctx}
--
      -> (A  : ty Γ) 
      -> (B : ty (Γ ▷ A))
      -> (a  : raw Γ) 
      -> (p : Γ ==> a :: A)
      -> (b : raw Γ)
      -> (Γ ==> b :: (B [[ els p ]]))
      -> (q : Γ ==> pr a b :: Σ-f A B)
-- ----------------------------------------------
      -> Γ ==> pr1 A B (pr a b) q == a :: A
--
Sg6-Σ-c-1 = Σ-c-1

Sg7-Σ-c-2 : {Γ : ctx}
--
      -> (A  : ty Γ) 
      -> (B : ty (Γ ▷ A))
      -> (a  : raw Γ) 
      -> (p : Γ ==> a :: A)
      -> (b : raw Γ)
      -> (Γ ==> b :: (B [[ els p ]]))
      -> (q : Γ ==> pr a b :: Σ-f A B)
-- --------------------------------------------------------------
      ->  Γ ==> pr2 A B (pr a b) q == b  :: (B [[ els p ]])
--
Sg7-Σ-c-2 = Σ-c-2

Sg8-Σ-c-eta : {Γ : ctx}
-- 
      -> (A  : ty Γ) 
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
-- ------------------------------------------------------------------
      ->  Γ ==> c == pr (pr1 A B c p) (pr2 A B c p) :: Σ-f A B
--
Sg8-Σ-c-eta = Σ-c-eta


Sg8-Σ-f-sub :  {Δ Γ : ctx} 
--
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))  -> (h : subst Δ Γ) 
--     ---------------------------------------
       -> Δ ==>  (Σ-f A B) [[ h ]] ==  Σ-f (A [[ h ]]) (B [[ ↑ A h ]]) 
--
Sg8-Σ-f-sub = Σ-f-sub

-- Natural numbers


N1-Nat-i-O : (Γ : ctx) -> 
--  -------------------------------------------
          Γ ==> zero Γ :: Nat Γ
--
N1-Nat-i-O =  Nat-i-O 



N2-Nat-i-s : (Γ : ctx) 
        -> (a : raw Γ)
        -> (Γ ==> a :: Nat Γ)      
--  -------------------------------------------
       ->  Γ ==> succ Γ a :: Nat Γ
--
N2-Nat-i-s = Nat-i-s

N3-Nat-e : {Γ : ctx} 
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> Γ ==> Rec C d p e q c r :: C [[ els r ]]
N3-Nat-e = Nat-e 


N4-Nat-c-O : {Γ : ctx} 
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> Γ ==> Rec C d p e q (zero Γ) (Nat-i-O Γ) == d :: C [[ els (Nat-i-O Γ)]]
N4-Nat-c-O = Nat-c-O

N5-Nat-c-s : {Γ : ctx} 
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (a : raw Γ)
      -> (r : Γ ==> a :: Nat Γ)
      -> Γ ==> Rec C d p e q (succ Γ a) (Nat-i-s Γ a r) 
           == e [  ext C (els r) (Rec C d p e q a r) (Nat-e {Γ} C d p e q a r) ] 
                 :: C [[ els (Nat-i-s Γ a r)]]
N5-Nat-c-s = Nat-c-s 

N6-Rec-cong : {Γ : ctx}
      -> (C C' : ty (Γ ▷ Nat Γ))
      -> (d d' : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (p' : Γ ==> d' :: C' [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (e' : raw ((Γ ▷ Nat Γ) ▷ C'))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (q' : (Γ ▷ Nat Γ) ▷ C'  ==> e' :: C' [[ step-sub Γ ]] [[ ↓ C' ]])
      -> (c c' : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> (r' : Γ ==> c' :: Nat Γ)
      -> (Cq : (Γ ▷ Nat Γ)  ==> C == C')
      -> << Raw Γ >> d ~ d'
      -> << Raw ((Γ ▷ Nat Γ) ▷ C) >> e ~ (e' [ subst-trp (ext-eq' {Γ ▷ Nat Γ} C C' Cq) ])
      -> << Raw Γ >> c ~ c'
      -> << Raw Γ >>  Rec {Γ} C d p e q c r ~ Rec {Γ} C' d' p' e' q' c' r'
N6-Rec-cong  =   Rec-cong' 

N7-Nat-sub :  (Δ Γ : ctx) -> (f : subst Δ Γ)
    -> Δ ==> (Nat Γ) [[ f ]] == (Nat Δ)
N7-Nat-sub = Nat-sub

N8-zero-sub : {Δ Γ : ctx} -> (f : subst Δ Γ)
        -> << Raw Δ >>  (zero Γ [ f ]) ~ (zero Δ)
N8-zero-sub = zero-sub

N9-succ-sub : {Δ Γ : ctx} -> (f : subst Δ Γ) -> (a : raw Γ)
        -> << Raw Δ >>  ((succ Γ a) [ f ]) ~ (succ Δ (a [ f ]))
N9-succ-sub  = succ-sub


N10-Rec-sub : {Δ Γ : ctx}
      -> (f : subst Δ Γ)
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (p' : Δ ==> (d [ f ]) :: C [[  N-sub f  ]] [[ els (Nat-i-O Δ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q  : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (q' : (Δ ▷ Nat Δ ) ▷ (C [[ N-sub f ]])  ==> e [ C-sub f C ] ::  
           C [[  N-sub f  ]] [[ step-sub Δ ]] [[ ↓ ( C [[  N-sub f  ]]) ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> (r' : Δ ==> (c [ f ]) :: (Nat Γ) [[ f ]])
      -> << Raw Δ >> ((Rec {Γ} C d p e q c r) [ f ])
                   ~ (Rec {Δ} (C [[  N-sub f  ]]) 
                              (d [ f ]) p' (e [ C-sub f C ])  q' (c [ f ]) r')
N10-Rec-sub  = Rec-sub' 




Empty1-N0-sub :  (Δ Γ : ctx) -> (f : subst Δ Γ)
    -> Δ ==> (N0 Γ) [[ f ]] == (N0 Δ)
Empty1-N0-sub = N0-sub

Empty2-N0-e : {Γ : ctx} 
      -> (C : ty (Γ ▷ N0 Γ))
      -> (c : raw Γ)
      -> (r : Γ ==> c :: N0 Γ)
      -> Γ ==> R0 C c r :: C [[ els r ]]
Empty2-N0-e = N0-e

Empty3-R0-sub : {Δ Γ : ctx}
      -> (f : subst Δ Γ)
      -> (C : ty (Γ ▷ N0 Γ))
      -> (c : raw Γ)
      -> (r : Γ ==> c :: N0 Γ)
      -> (r' : Δ ==> c [ f ] :: (N0 Γ) [[ f ]])
      -> << Raw Δ >>  ((R0 {Γ} C c r) [[ f ]])  ~  (R0 {Δ} (C [[ ↑ (N0 Γ) f ]]) (c [ f ]) r')
Empty3-R0-sub = R0-sub'

Empty4-R0-cong : {Γ : ctx}
      -> (C C' : ty (Γ ▷ N0 Γ))
      -> (c c' : raw Γ)
      -> (r : Γ ==> c :: N0 Γ)
      -> (r' : Γ ==> c' :: N0 Γ)
      -> (Cq : (Γ ▷ N0 Γ)  ==> C == C')
      -> << Raw Γ >> c ~ c'
      -> << Raw Γ >>  R0 {Γ} C c r ~ R0 {Γ} C' c' r'
Empty4-R0-cong = R0-cong'

-- Disjoint union

Sm1-Sum : {Γ : ctx}
--
   -> (A : ty Γ)    -> (B : ty Γ)
-- -------------------------------
   -> ty Γ
--
Sm1-Sum = Sum

Sm2-Sum-cong : {Γ : ctx}
--
   -> (A A' : ty Γ)
   -> (B B' : ty Γ)
   -> Γ ==> A == A'  -> Γ ==> B == B'
-- -------------------------------
   -> Γ ==> Sum A B == Sum A' B'
--
Sm2-Sum-cong = Sum-cong

Sm3-Sum-sub : {Δ Γ : ctx}
--
   -> (f : subst Δ Γ)
   -> (A : ty Γ)
   -> (B : ty Γ)
-- ----------------------------------------------------------
   -> Δ ==> (Sum A B) [[ f ]] == Sum (A [[ f ]]) (B [[ f ]]) 
--
Sm3-Sum-sub  = Sum-sub


Sm4-lf-pf : {Γ : ctx}
--
   -> (A B : ty Γ)
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
-- ---------------------------------
   -> Γ ==> lf A B a p :: Sum A B
--
Sm4-lf-pf = lf-pf


Sm5-rg-pf : {Γ : ctx}
--
   -> (A B : ty Γ)
   -> (b : raw Γ)
   -> (p : Γ ==> b :: B)
-- ---------------------------------
   -> Γ ==> rg A B b p :: Sum A B
-- 
Sm5-rg-pf = rg-pf


Sm6-lf-cong : {Γ : ctx}
--
   -> (A B A' B' : ty Γ)
   -> (a a' : raw Γ)
   -> (p : Γ ==> a :: A)
   -> (p' : Γ ==> a' :: A')
   -> (q : Γ ==> A == A')
   -> (r : Γ ==> B == B')
   -> (Γ ==> a == a' :: A)
-- --------------------------------------------------------
   -> Γ ==> lf {Γ} A B a p == lf {Γ} A' B' a' p' :: Sum A B 
--
Sm6-lf-cong = lf-cong


Sm7-lf-sub : {Δ Γ : ctx}
   -> (h : subst Δ Γ)
   -> (A B : ty Γ)
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> (p' : Δ ==> a [ h ] :: A [[ h ]])
   ->  Δ ==> (lf A B a p) [ h ] == lf (A [[ h ]])  (B [[ h ]]) (a [ h ]) p' :: (Sum A B) [[ h ]]
Sm7-lf-sub = lf-sub 

Sm8-rg-cong : {Γ : ctx}
--
   -> (A B A' B' : ty Γ)
   -> (b b' : raw Γ)
   -> (p : Γ ==> b :: B)
   -> (p' : Γ ==> b' :: B')
   -> (q : Γ ==> A == A')
   -> (r : Γ ==> B == B')
   -> (Γ ==> b == b' :: B)
-- ---------------------------------------------------------
   -> Γ ==> rg {Γ} A B b p == rg {Γ} A' B' b' p' :: Sum A B 
--
Sm8-rg-cong = rg-cong



Sm9-rg-sub : {Δ Γ : ctx}
   -> (h : subst Δ Γ)
   -> (A B : ty Γ)
   -> (b : raw Γ)
   -> (p : Γ ==> b :: B)
   -> (p' : Δ ==> b [ h ] :: B [[ h ]])
   ->  Δ ==> (rg A B b p) [ h ] == rg (A [[ h ]])  (B [[ h ]]) (b [ h ]) p' :: (Sum A B) [[ h ]]
Sm9-rg-sub = rg-sub



Sm10-Sum-e : {Γ : ctx} 
--  
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (c : raw Γ)
       -> (r : Γ ==> c :: Sum A B)
-- ---------------------------------------------------------
       -> Γ ==> Sum-rec A B C d p e q c r :: C [[ els r ]]
--
Sm10-Sum-e = Sum-e



Sm11-Sum-c1 : {Γ : ctx}   
--
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (a : raw Γ)
       -> (r : Γ ==> a :: A)
       -> (r' : Γ ==> (lf {Γ} A B a r) :: Sum A B)
-- ----------------------------------------------------------------------------------------
       -> Γ ==> Sum-rec A B C d p e q (lf {Γ} A B a r) r' == d [ els r ] :: C [[ els r' ]]
--
Sm11-Sum-c1 = Sum-c1

Sm12-Sum-c2 : {Γ : ctx}   
--
       -> (A B : ty Γ)
       -> (C : ty (Γ ▷ (Sum A B)))
       -> (d : raw (Γ ▷ A))
       -> (p : (Γ ▷ A) ==> d :: C [[ Sum-sub-lf A B ]])
       -> (e : raw (Γ ▷ B))
       -> (q : (Γ ▷ B) ==> e :: C [[ Sum-sub-rg A B ]])
       -> (b : raw Γ)
       -> (r : Γ ==> b :: B)
       -> (r' : Γ ==> (rg {Γ} A B b r) :: Sum A B)
-- ------------------------------------------------------------------------------------------
       -> Γ ==> Sum-rec A B C d p e q (rg {Γ} A B b r) r' == e [ els r ] :: C [[ els r'  ]]
--
Sm12-Sum-c2 =  Sum-c2

Sm13-Sum-rec-cong : {Γ : ctx}   
-- 
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
-- --------------------------------------------------------------------------------------------
       -> Γ ==>  Sum-rec {Γ} A B C d p e q c r == Sum-rec {Γ} A' B' C' d' p' e' q' c' r' :: C [[ els r ]]
Sm13-Sum-rec-cong = Sum-rec-cong



Sm14-Sum-rec-sub : {Δ Γ : ctx}
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
Sm14-Sum-rec-sub = Sum-rec-sub





-- Universe hierarchy à la Russell

U1-T-eq- : (k : N) 
     -> {Γ : ctx}  
     -> (A : raw Γ)
     -> (p : Γ ==> A :: U- k Γ)
-- -------------------------------
     ->  Γ ==> T- k A p == A
--
U1-T-eq- = T-eq- 


U2-U-nat- : (k : N) ->  (Γ : ctx) 
-- -----------------------------------
    -> Γ ==> Nat Γ :: U- k Γ
--
U2-U-nat- = U-nat-
 


U3-U-sigma- :   (k : N) -> {Γ : ctx} 
--
    ->  (A : ty Γ) 
    ->  (p : Γ ==> A :: U- k Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U- k Γ [[ ↓ A ]])
-- --------------------------------------------
    ->  Γ ==> Σ-f A B :: U- k Γ
--
U3-U-sigma-  = U-sigma-



U4-U-pi- : (k : N) -> {Γ : ctx} 
--
    ->  (A : ty Γ) 
    ->  (p : Γ ==> A :: U- k Γ)
    ->  (B : ty (Γ ▷ A))
    ->  (q : (Γ ▷ A) ==> B :: U- k Γ [[ ↓ A ]])
-- --------------------------------------------
    ->  Γ ==> Π-f A B :: U- k Γ
--
U4-U-pi- = U-pi-



U5-U-ID- :  (k : N) -> {Γ : ctx}
--
     -> (A : ty Γ)
     -> (p : Γ ==> A :: U- k Γ)
     -> (a : raw Γ)
     -> (qa : Γ ==> a :: A)
     -> (b : raw Γ)
     -> (qb : Γ ==> b :: A)    
-- ------------------------------------------
     -> Γ ==> ID A a qa b qb :: U- k Γ
--
U5-U-ID- = U-ID-


U6-U-N0- : (k : N) -> {Γ : ctx}
-- ---------------------------
      -> Γ ==> N0 Γ :: U- k Γ
--
U6-U-N0-  = U-N0-



U7-U-Sum- : (k : N) -> {Γ : ctx} 
--
    ->  (A B : ty Γ) 
    ->  (p : Γ ==> A :: U- k Γ)
    ->  (q : Γ ==> B :: U- k Γ)
-- ------------------------------
    ->  Γ ==> Sum A B :: U- k Γ
--
U7-U-Sum- = U-Sum-




U8-U-sub- :  (k : N) ->  (Δ Γ : ctx) 
      -> (f : subst Δ Γ)
-- --------------------------------------
     ->  Δ ==> (U- k Γ) [[ f ]] == U- k Δ
--
U8-U-sub- = U-sub-


U9-Cu-1a  : (k : N) -> (Γ : ctx)  
-- ---------------------------------------
     -> (Γ ==> U- k Γ :: U- (s k) Γ)
--
U9-Cu-1a  =  Cu-1a-

U10-Cu-1b : (k : N) -> {Γ : ctx}  -> (A : raw Γ)
     -> (Γ ==> A :: U- k Γ)
-- ---------------------------------------
     -> (Γ ==> A :: U- (s k) Γ)
--
U10-Cu-1b  =  Cu-1b-


-- Bracket types (Awodey & Bauer 2004)



B1-Br-intro :  {Γ : ctx} 
--
    -> (A : ty Γ) 
    -> (a : raw Γ)
    -> Γ ==> a :: A
-- -------------------------
    -> Γ ==> br a :: Br A
B1-Br-intro  =  Br-intro

B2-Br-e :  {Γ : ctx} 
--
    -> (A B : ty Γ) 
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ A ==> b :: B [[ ↓ A ]])
    -> (p : Γ ▷ A ▷ (A [[ ↓ A ]]) ==> b [ pr-x A  ] ==  b [ pr-y A ] :: B  [[ ↓ A ]] [[ ↓ (A [[ ↓ A ]]) ]])
-- --------------------------------  
    -> Γ ==>  wh A B k b q r p :: B
B2-Br-e = Br-e

B3-Br-beta :  {Γ : ctx} 
--
    -> (A B : ty Γ) 
    -> (a : raw Γ)
    -> (b  : raw (Γ ▷ A))
    -> (t : Γ ==> a :: A)
    -> (q : Γ ==> (br a) :: Br A)
    -> (r : Γ ▷ A ==> b :: B [[ ↓ A ]])
    -> (p : Γ ▷ A ▷ (A [[ ↓ A ]]) ==> b [ pr-x A  ] ==  b [ pr-y A ] :: B  [[ ↓ A ]] [[ ↓ (A [[ ↓ A ]]) ]])
-- --------------------------------  
    -> Γ ==>  (wh A B (br a) b q r p) == (b [ els t ]) :: B
B3-Br-beta = Br-beta

B4-Br-eta :  {Γ : ctx} 
--
    -> (A B : ty Γ) 
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ Br A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ (Br A) ==> b :: B [[ ↓ (Br A) ]])
    -> (t :  Γ ▷ A ==> b [ br-sb A ] :: B [[ ↓ A ]])
-- --------------------------------  
    -> Γ ==>  wh A B k (b [ br-sb A ]) q t (br-sb-lm {Γ} A B b r) == (b [ els q ]) :: B
B4-Br-eta = Br-eta

B5-Br-eqty :  {Γ : ctx} 
--
    -> (A : ty Γ) 
    -> (a b : raw Γ)
    -> Γ ==> a :: Br A
    -> Γ ==> b :: Br A
-- -----------------------
    ->  Γ ==> a == b :: Br A
B5-Br-eqty = Br-eqty

B6-Br-cong : {Γ : ctx} 
--
    -> (A B : ty Γ) 
    -> Γ ==> A == B
-- -------------------
    -> Γ ==> Br A == Br B
B6-Br-cong = Br-cong

B7-Br-e-cong :  {Γ : ctx} 
--
    -> (A B : ty Γ) 
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ A ==> b :: B [[ ↓ A ]])
    -> (p : Γ ▷ A ▷ (A [[ ↓ A ]]) ==> b [ pr-x A  ] ==  b [ pr-y A ] :: B  [[ ↓ A ]] [[ ↓ (A [[ ↓ A ]]) ]])
    -> (A' B' : ty Γ) 
    -> (k'  : raw Γ)
    -> (b' : raw (Γ ▷ A'))
    -> (q' : Γ ==> k' :: Br A')
    -> (r' : Γ ▷ A' ==> b' :: B' [[ ↓ A' ]])
    -> (p' : Γ ▷ A' ▷ (A' [[ ↓ A' ]]) ==> b' [ pr-x A'  ] ==  b' [ pr-y A' ] :: B'  [[ ↓ A' ]] [[ ↓ (A' [[ ↓ A' ]]) ]])
    -> (Aq : Γ ==> A == A')
    -> Γ ==> B == B'
    -> Γ ==> k ==  k' :: Br A
    -> Γ ▷ A ==> b == (b' [ subst-trp (ext-eq' {Γ} A A' Aq) ]) ::  B [[ ↓ A ]]
-- --------------------------------  
    -> Γ ==>  wh A B k b q r p ==  wh A' B' k' b' q' r' p' :: B
B7-Br-e-cong = Br-e-cong


B8-Br-sub : {Δ Γ : ctx} 
--
    -> (A : ty Γ) 
    -> (f : subst Δ Γ) 
-- --------------------------------    
    ->  Δ ==> (Br A) [[ f ]] == (Br (A [[ f ]]))
B8-Br-sub = Br-sub

B9-br-sub : {Δ Γ : ctx} 
--
    -> (A : ty Γ) 
    -> (f : subst Δ Γ) 
    -> (a : raw Γ)
    -> Γ ==> a :: A
-- --------------------------------    
    ->  Δ ==> (br a) [ f ] == (br (a [ f ])) :: (Br A) [[ f ]]
B9-br-sub = br-sub

B10-Br-e-sub :  {Δ Γ : ctx} 
--
    -> (h : subst Δ Γ)
    -> (A B : ty Γ) 
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ A ==> b :: B [[ ↓ A ]])
    -> (p : Γ ▷ A ▷ (A [[ ↓ A ]]) ==> b [ pr-x A  ] ==  b [ pr-y A ] :: B  [[ ↓ A ]] [[ ↓ (A [[ ↓ A ]]) ]])
    -> (q' : Δ ==> k [ h ] :: Br (A [[ h ]]))
    -> (r' : Δ ▷ (A [[ h ]])  ==> (b [[ (↑ A  h) ]]) :: (B [[ h ]]) [[ ↓ (A [[ h ]]) ]])
    -> (p' : Δ ▷ (A [[ h ]]) ▷ ((A [[ h ]]) [[ ↓ (A [[ h ]]) ]]) 
             ==> (b [[ (↑ A h) ]]) [ pr-x (A [[ h ]])  ] ==  (b [[ (↑ A  h) ]]) [ pr-y (A [[ h ]]) ] 
                  :: (B [[ h ]])  [[ ↓ (A [[ h ]]) ]] [[ ↓ ((A [[ h ]]) [[ ↓ (A [[ h ]]) ]]) ]])

-- --------------------------------  
    -> Δ ==>  (wh A B k b q r p) [ h ] == (wh (A [[ h ]]) (B [[ h ]]) (k [ h ]) (b [[ (↑ A h) ]]) q' r' p') :: B [[ h ]]
B10-Br-e-sub = Br-e-sub