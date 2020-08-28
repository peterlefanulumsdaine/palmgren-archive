-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt10 where

open import basic-types
open import basic-setoids       -- 525 lines
open import dependent-setoids   -- 559 lines
open import subsetoids          -- 341 lines
open import iterative-sets      -- 869 lines
open import iterative-sets-pt2  -- 326 lines
open import iterative-sets-pt3  -- 439 lines
open import iterative-sets-pt4  
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
                     -- total     6859 lines

-- empty context

⊤ : ctx
⊤ = oneV

⊤-unique : (x y : || κ ⊤ ||) -> < κ ⊤ > x ~ y
⊤-unique 0₁ 0₁ = <> (easy-eqV _  br-zeroV  br-zeroV (λ z → exfalso _ z))

! : (Γ : ctx) -> subst Γ ⊤
! Γ = sb (record { op = λ x → 0₁ 
                 ; ext = λ x y p → <> (easy-eqV _ br-zeroV br-zeroV (λ z → exfalso _ z))})

!-unique : (Γ : ctx) -> (f : subst Γ ⊤) -> < Subst Γ ⊤ > f ~ ! Γ
!-unique Γ f = <> (<> (\ x -> ⊤-unique (setoidmap.op (subst.cmap f) x) (setoidmap.op (subst.cmap (! Γ)) x)))


!-sub : (Δ Γ : ctx) -> (f : subst  Δ Γ) -> < Subst Δ ⊤ >  ! Γ ⌢ f ~ ! Δ
!-sub Δ Γ f = !-unique Δ (! Γ ⌢ f) 


-- to be moved elsewhere probably



Ext-eq-lm1 :  (Γ : ctx) 
           -> (A : ty Γ)
           ->  (z z' : || κ (Γ ▷ A) ||)
           ->  (< κ (Γ ▷ A) >  z ~ z')
           ->  and (Γ ‣ (pj1 z)  ≐  Γ ‣ (pj1 z')) 
                   (((ty.type A) • (pj1 z)) ‣ (pj2 z)  ≐  ((ty.type A) • (pj1 z')) ‣ (pj2 z'))
Ext-eq-lm1 Γ A z z' p = pairV-inv-1 (>< p) 

Ext-eq-lm2 :   (Γ : ctx) 
           ->  (A : ty Γ)
           ->  (z z' : || κ (Γ ▷ A) ||)
           ->  (Γ ‣ (pj1 z)  ≐  Γ ‣ (pj1 z')) 
           ->  (((ty.type A) • (pj1 z)) ‣ (pj2 z)  ≐  ((ty.type A) • (pj1 z')) ‣ (pj2 z'))
           ->  (< κ (Γ ▷ A) >  z ~ z')
Ext-eq-lm2 a g z z' p q = <> (pairV-ext p q) 





-- Ext : (Γ : ctx) -> (A : ty Γ) -> ctx
-- Ext Γ A = sigmaV Γ (ty.type A)
-- sigmaV : (a : V) -> (g :  setoidmap1 (κ a) VV) -> V
-- sigmaV a g =  sup (Σ (# a) (\y -> # (g • y))) 
--                     (\u -> < a ‣ (pj1 u) , (g • (pj1 u)) ‣ (pj2 u) >)


-- Γ ▷ A = Ext Γ A


-- supN1-lm : (f g : N₁ -> V) -> (f 0₁ ≐ g 0₁) -> (sup N₁ f) ≐ (sup N₁ g)
-- constant type

Const⊤ : V -> ty ⊤
Const⊤ u = tyy (record { op = λ x → u 
                       ; ext = λ x y p → <<>> (refV u) })

Const : V -> (Γ : ctx) -> ty Γ
Const u Γ =  (Const⊤ u) [[ ! Γ ]]
             -- tyy (record { op = λ x → u 
             --            ; ext = λ x y p → refV u })

Const-sub : (u : V) -> {Δ Γ : ctx} -> (f : subst Δ Γ) 
     -> Δ ==> Const u Γ [[ f ]] == Const u Δ
Const-sub u {Δ} {Γ} f = (tysym (tysubst-com (Const⊤ u) ( ! Γ) f))


const⊤ :  V ->  raw ⊤
const⊤ u =   mkraw (record { op = λ x → u 
                            ; ext = λ x y p → <<>> (refV u) })

const :  V -> (Γ : ctx) -> raw Γ
const u Γ =   const⊤ u [ ! Γ ] 


const-sub : (u : V) -> {Δ Γ : ctx} -> (f : subst Δ Γ) 
     -> << Raw Δ >>  (const u Γ [ f ]) ~ (const u Δ)
const-sub u {Δ} {Γ} f = <<>> (<<>> (λ x → <<>> (refV _)))  

{--

sub-comp-prop : {Θ Δ Γ : ctx}  
       -> (a : raw Γ) 
       ->  (f : subst Δ Γ) -> (g : subst Θ Δ) 
-- ---------------------------------------------------
       -> << Raw Θ >>  a [ f ⌢ g ]  ~ (a [ f ] [ g ])

--}

-- Γ ▷ (Const u Γ) == vv (Const u Γ) :: (Const u Γ) [[ ↓ (Const u Γ) ]]
-- Γ ▷ (Const u Γ) == vv (Const u Γ) :: (Const u (Γ ▷ (Const u Γ)))

-- function on a constant type

fun⊤-op : (u v : V) -> || (κ u) => (κ v) || ->  || κ (⊤ ▷ Const⊤ u) || ->  || κ (⊤ ▷ Const⊤ v) ||
fun⊤-op  u v h (x , y) = x , ap h y 

fun⊤-ext : (u v : V) -> (h : || (κ u) => (κ v) ||) -> (z z' :  || κ (⊤ ▷ Const⊤ u) ||) 
    -> (< κ (⊤ ▷ Const⊤ u) > z ~ z')
    -> < κ (⊤ ▷ Const⊤ v) > fun⊤-op u v h z ~ fun⊤-op u v h z'
fun⊤-ext u v h (x , y) (x' , y') p = 
     let lm = Ext-eq-lm1 ⊤ (Const⊤ u) _ _ p
         lm2 : (ty.type (Const⊤ u) • x) ‣ y ≐ (ty.type (Const⊤ u) • x') ‣ y'
         lm2 = prj2 lm
         lm3 : u ‣ y ≐  u ‣ y'
         lm3 = lm2
         lm4 : v ‣ ap h y ≐  v ‣ ap h y'
         lm4 = >< (extensionality h y y' (<> lm3))
         lm5 : (ty.type (Const⊤ v) • x) ‣ ap h y ≐
               (ty.type (Const⊤ v) • x') ‣ ap h y' 
         lm5 = lm4
      
     in  Ext-eq-lm2 ⊤ (Const⊤ v) _ _ (prj1 lm) lm5
  

-- pairV-inv-1 : {x y z u : V} -> < x , y > ≐ < z , u > ->  and (x ≐ z) (y ≐ u)

fun⊤ : (u v : V) -> || (κ u) => (κ v) ||  -> subst (⊤ ▷ (Const⊤ u))  (⊤ ▷ (Const⊤ v))
fun⊤ u v h = sb (record { op = fun⊤-op u v h  
                        ; ext = fun⊤-ext u v h })

pr⊤ : (u : V) -> (Γ : ctx) -> subst (Γ ▷ (Const u Γ))  (⊤ ▷ (Const⊤ u))
pr⊤ u Γ = ↑ (Const⊤ u) (! Γ)
 
-- better names for these :

lm :   (u : V) -> ⊤ ▷ (Const⊤ u) ==> vv (Const⊤ u) :: (Const⊤ u) [[ ↓ (Const⊤ u) ]] 
lm u = asm (Const⊤ u)

lm2 : (u v : V) -> (f : || (κ u) => (κ v) ||) -> 
       ⊤ ▷ (Const⊤ u) ==> vv (Const⊤ v) [ fun⊤ u v f ] :: (Const⊤ v) [[ ↓ (Const⊤ v) ]] [[ fun⊤ u v f ]]
lm2 u v f = elt-subst (fun⊤ u v f) (lm v)

lm3 :  (u v : V) -> (f : || (κ u) => (κ v) ||) ->  (Γ : ctx) ->
    Γ ▷ (Const u Γ) ==> vv (Const⊤ v) [ fun⊤ u v f ] [ pr⊤ u Γ ] 
            :: (Const⊤ v) [[ ↓ (Const⊤ v) ]] [[ fun⊤ u v f ]] [[ pr⊤ u Γ ]]
lm3 u v f Γ = elt-subst (pr⊤ u Γ) (lm2 u v f) 

lm4 : (u v : V) -> (f : || (κ u) => (κ v) ||) ->  (Γ : ctx) ->
      Γ ▷ (Const u Γ) ==> (Const⊤ v) [[ ↓ (Const⊤ v) ]] [[ fun⊤ u v f ]] [[ pr⊤ u Γ ]]
                       == (Const⊤ v [[ ! Γ ]]) [[ ↓ (Const⊤ u [[ ! Γ ]]) ]]
lm4 u v f Γ = mk-eqty (λ x → <<>> (refV _))

lm5 :  (u v : V) -> (f : || (κ u) => (κ v) ||) ->  (Γ : ctx) ->
    Γ ▷ (Const u Γ) ==> vv (Const⊤ v) [ fun⊤ u v f ] [ pr⊤ u Γ ] 
            :: (Const⊤ v [[ ! Γ ]]) [[ ↓ (Const⊤ u [[ ! Γ ]]) ]]
lm5 u v f Γ = elttyeq (lm3 u v f Γ) (lm4 u v f Γ)


{--
↑ :  {Δ Γ : ctx}  -> (A : ty Γ)    -> (h : subst Δ Γ) 
     -> subst (Δ ▷ (A [[ h ]])) (Γ ▷ A)
↑ A h = qq A h
--}

lift : (u v : V)  -> (f : || (κ u) => (κ v) ||) -> (Γ : ctx) 
      -> subst (Γ ▷ ((Const⊤ u) [[ ! Γ ]]))  (Γ ▷ ((Const⊤ v) [[ ! Γ ]]))
lift  u v f Γ = ext ((Const⊤ v) [[ ! Γ ]]) (↓  ((Const⊤ u) [[ ! Γ ]]) ) 
                           (vv (Const⊤ v) [ fun⊤ u v f ] [ pr⊤ u Γ ]) (lm5 u v f Γ)

lift-fun : (u v : V) -> || (κ u) => (κ v) || -> (Γ : ctx) -> subst (Γ ▷ (Const u Γ)) (Γ ▷ (Const v Γ))
lift-fun u v h Γ = lift u v h Γ




-- 



-- Natural numbers

Nat :  (Γ : ctx) -> ty Γ
Nat Γ = Const natV Γ

Nat-sub :  (Δ Γ : ctx) -> (f : subst Δ Γ)
    -> Δ ==> (Nat Γ) [[ f ]] == (Nat Δ)
Nat-sub Δ Γ f = mk-eqty (λ x → <<>> (refV _))

zero :  (Γ : ctx) -> raw Γ
zero Γ = const zeroV Γ

zero-sub : {Δ Γ : ctx} -> (f : subst Δ Γ)
        -> << Raw Δ >>  (zero Γ [ f ]) ~ (zero Δ)
zero-sub {Δ} {Γ} f = const-sub zeroV {Δ} {Γ} f 

succ : (Γ : ctx) -> raw Γ -> raw Γ
succ Γ a = mkraw (record { op = λ x → succV (apr a x) 
                         ; ext = λ x y p → <<>> (succV-ext _ _ (>><< (extensionality1 (raw.rawterm a) x y p))) })

succ-sub : {Δ Γ : ctx} -> (f : subst Δ Γ) -> (a : raw Γ)
        -> << Raw Δ >>  ((succ Γ a) [ f ]) ~ (succ Δ (a [ f ]))
succ-sub {Δ} {Γ} f a = <<>> (<<>> (λ x → <<>> (refV _)))

Nat-i-O : (Γ : ctx) -> 
--  -------------------------------------------
          Γ ==> zero Γ :: Nat Γ
--
Nat-i-O Γ = mk-elt (λ x → zeroV-in-natV)



Nat-i-s : (Γ : ctx) 
        -> (a : raw Γ)
        -> (Γ ==> a :: Nat Γ)      
--  -------------------------------------------
       ->  Γ ==> succ Γ a :: Nat Γ
--
Nat-i-s Γ a p =
   mk-elt (λ x → (s (pj1 (apel p x))) , succV-ext _ _ (pj2 (apel p x)))




-- lift-fun : (u v : V) -> || (κ u) => (κ v) || -> (Γ : ctx) -> subst (Γ ▷ (Const u Γ)) (Γ ▷ (Const v Γ))
-- lift-fun u v h Γ = lift u v h Γ



step-sub : (Γ : ctx) 
        ->  subst (Γ ▷ Nat Γ) (Γ ▷ Nat Γ)
step-sub Γ = lift-fun natV natV succ-fun Γ




mk-step-e  : {Γ : ctx}
      -> (C : ty (Γ ▷ Nat Γ))
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (u : || κ Γ ||)
      -> (m : || κ natV ||) -> (z : || κ (apt C (u , m)) ||) ->  || κ (apt C (u , (s m))) ||
mk-step-e  {Γ} C e q u m z = pj1 (apel q ((u , m) , z))
{--   let 
       eu = apr e ((u , m) , z)
       qu = apel q ((u , m) , z)
       lm : apt ((C [[ step-sub Γ ]]) [[ ↓ C ]]) ((u , m) , z) ≐ apt C (u , s m)
       lm = refV _
       qu' : apr e ((u , m) , z) ∈   apt C (u , s m)
       qu' = qu  --  luck!
       main : || κ (apt C (u , s m)) ||
       main = pj1 qu'
   in main
--}

mk-step-e-xt :  {Γ : ctx}
      -> (C : ty (Γ ▷ Nat Γ))
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (z : || κ Γ ||)
      -> (m  k : || κ natV ||) -> (u :  || κ (apt C (z , m)) ||) -> (v :  || κ (apt C (z , k)) ||)
               -> < κ natV > m ~ k -> (apt C (z , m)) ‣ u ≐ (apt C (z , k)) ‣ v ->
                     (apt C (z , (s m))) ‣ (mk-step-e {Γ} C e q z m u) 
                   ≐ (apt C (z , (s k))) ‣ (mk-step-e {Γ} C e q z k v)
mk-step-e-xt {Γ} C e q z m k u v p r = 
   let lm1 : apr e ((z , m) , u) ∈ apt C (z , (s m))
       lm1 = apel q ((z , m) , u)
       eq1 : apr e ((z , m) , u) ≐
          apt C (z , s m) ‣ pj1 (apel q ((z , m) , u))
       eq1 = pj2 lm1
       lm2 : apr e ((z , k) , v) ∈ apt C (z , (s k))
       lm2 = apel q ((z , k) , v)
       eq2 : apr e ((z , k) , v) ≐
          apt C (z , s k) ‣ pj1 (apel q ((z , k) , v))
       eq2 = pj2 lm2 
       eq3 = extensionality1 (raw.rawterm e) ((z , m) , u) ((z , k) , v)
       eq4 : apr e ((z , m) , u) ≐ apr e ((z , k) , v)
       eq4 = >><< (eq3 (<> (pairV-ext (pairV-ext (refV _) (>< p)) r)))
       main : (apt C (z , (s m))) ‣ (mk-step-e {Γ} C e q z m u) 
                   ≐ (apt C (z , (s k))) ‣ (mk-step-e {Γ} C e q z k v)
       main = traV (symV eq1) (traV eq4 eq2 )
   in main

-- more general version

mk-step-e-xt2 :  {Γ : ctx}
      -> (C : ty (Γ ▷ Nat Γ))
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (z z' : || κ Γ ||)     
      -> (m m' : N) -> (u :  || κ (apt C (z , m)) ||) -> (v :  || κ (apt C (z' , m')) ||)
               -> < κ Γ > z ~ z'  -> < κ natV > m ~ m'
               -> (apt C (z , m)) ‣ u ≐ (apt C (z' , m')) ‣ v ->
                     (apt C (z , (s m))) ‣ (mk-step-e {Γ} C e q z m u) 
                   ≐ (apt C (z' , (s m'))) ‣ (mk-step-e {Γ} C e q z' m' v)
mk-step-e-xt2 {Γ} C e q z z' m m' u v p1 p2 p3 = 
   let lm1 : apr e ((z , m) , u) ∈ apt C (z , (s m))
       lm1 = apel q ((z , m) , u)
       eq1 : apr e ((z , m) , u) ≐
          apt C (z , s m) ‣ pj1 (apel q ((z , m) , u))
       eq1 = pj2 lm1
       lm2 : apr e ((z' , m') , v) ∈ apt C (z' , (s m'))
       lm2 = apel q ((z' , m') , v)
       eq2 : apr e ((z' , m') , v) ≐
          apt C (z' , s m') ‣ pj1 (apel q ((z' , m') , v))
       eq2 = pj2 lm2 
       eq3 = extensionality1 (raw.rawterm e) ((z , m) , u) ((z' , m') , v)
       eq4 : apr e ((z , m) , u) ≐ apr e ((z' , m') , v)
       eq4 = >><< (eq3 (<> (pairV-ext (pairV-ext (>< p1) (>< p2)) p3) )) 
       main : (apt C (z , (s m))) ‣ (mk-step-e {Γ} C e q z m u) 
                   ≐ (apt C (z' , (s m'))) ‣ (mk-step-e {Γ} C e q z' m' v)
       main = traV (symV eq1) (traV eq4 eq2 )
   in main

-- 
{--

natV-rec : 
         (C : setoidmap1 (κ natV) VV)
      -> (d : || κ (ap1 C O) ||)
      -> (e : (m : || κ natV ||) -> (z :  || κ (ap1 C m) ||) ->  || κ (ap1 C (s m)) ||)
      -> (xt :  (m  k : || κ natV ||) -> (u :  || κ (ap1 C m) ||) -> (v :  || κ (ap1 C k) ||)
               -> < κ natV > m ~ k -> (ap1 C m) ‣ u ≐ (ap1 C k) ‣ v ->
                     (ap1 C (s m)) ‣ (e m u) ≐ (ap1 C (s k)) ‣ (e k v))
      -> (m : || κ natV ||)
      -> || κ (ap1 C m) ||
natV-rec C d e xt O = d
natV-rec C d e xt (s m) = e m (natV-rec C d e xt m)

--}

natV-rec-lm-s : 
         (C : setoidmap1 (κ natV) VV)
      -> (d : || κ (ap1 C O) ||)
      -> (e : (m : || κ natV ||) -> (z :  || κ (ap1 C m) ||) ->  || κ (ap1 C (s m)) ||)
      -> (xt :  (m  k : || κ natV ||) -> (u :  || κ (ap1 C m) ||) -> (v :  || κ (ap1 C k) ||)
               -> < κ natV > m ~ k -> (ap1 C m) ‣ u ≐ (ap1 C k) ‣ v ->
                     (ap1 C (s m)) ‣ (e m u) ≐ (ap1 C (s k)) ‣ (e k v))
      -> (m : || κ natV ||)
      -> (ap1 C (s m)) ‣ (natV-rec C d e xt (s m)) ≐   (ap1 C (s m)) ‣ (e m (natV-rec C d e xt m))
natV-rec-lm-s C d e xt m = refV _

-- lmbC

lmbC : {Γ : ctx}
        -> (C : ty (Γ ▷ Nat Γ))
        -> (u : || κ Γ ||)
        -> setoidmap1 (κ natV) VV
lmbC {Γ} C u =
            record { op = λ x →  apt C (u , x) 
                    ; ext = λ x y pf → extensionality1 (ty.type C) (u , x) (u , y) 
                                        (<> (pairV-ext (refV _) (>< pf))) }
       


Rec-op : {Γ : ctx}
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> (u : || κ Γ ||)
      -> V
Rec-op {Γ} C d p e q c r u = 
    let 
        pu = apel p u
        pu1 : # (apt (C [[ els (Nat-i-O Γ) ]]) u)
        pu1 = pj1 pu  
        pu2 = pj2 pu
        cu = apr c u
        ru = apel r u
        ru1 = pj1 ru
        lm : || κ (ap1 (lmbC {Γ} C u) ru1) ||
        lm = natV-rec (lmbC {Γ} C u) pu1 (mk-step-e {Γ} C e q u) (mk-step-e-xt {Γ} C e q u) ru1
        main : V
        main = (ap1  (lmbC {Γ} C u) ru1) ‣ lm 
    in main
-- explicitly:
-- Rec-op {Γ} C d p e q c r u 
-- = (ap1  (lmbC {Γ} C u) (pj1 (apel r u))) ‣ 
--     (natV-rec (lmbC {Γ} C u) (pj1 (apel p u)) (mk-step-e {Γ} C e q u) (mk-step-e-xt {Γ} C e q u) (pj1 (apel r u)))

Rec-op-lm2 : {Γ : ctx}
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> (u : || κ Γ ||)
      ->  Rec-op {Γ} C d p e q c r u ∈ (ap1  (lmbC {Γ} C u) (pj1 (apel r u)))
Rec-op-lm2 {Γ} C d p e q c r u = 
     (natV-rec (lmbC {Γ} C u) (pj1 (apel p u)) 
                          (mk-step-e {Γ} C e q u) 
                           (mk-step-e-xt {Γ} C e q u) (pj1 (apel r u)))    
     , (refV _)


Rec-ext-lm3 : {Γ : ctx}
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> (m k : || κ natV ||)
      -> (pf1 : < κ natV > m ~ k) 
      -> (x y : || κ Γ ||)
      ->  (pf2 : < κ Γ > x ~ y)
      ->  (ap1  (lmbC {Γ} C x) m) ‣ 
                  (natV-rec (lmbC {Γ} C x) (pj1 (apel p x)) (mk-step-e {Γ} C e q x) (mk-step-e-xt {Γ} C e q x) m) 
               ≐
          (ap1  (lmbC {Γ} C y) k) ‣ 
                  (natV-rec (lmbC {Γ} C y) (pj1 (apel p y)) (mk-step-e {Γ} C e q y) (mk-step-e-xt {Γ} C e q y) k)
Rec-ext-lm3 {Γ} C d p e q c r O O         pf1 x y pf2 =
   let deq :  apr d x ≐ apr d y
       deq = >><< (extensionality1 (raw.rawterm d) x y pf2)
       px = pj2 (apel p x)
       py = pj2 (apel p y)
       main :  ap1 (lmbC {Γ} C x) O ‣ pj1 (apel p x) ≐
               ap1 (lmbC {Γ} C y) O ‣ pj1 (apel p y)
       main = traV (symV px) (traV deq py)
   in main   
Rec-ext-lm3 {Γ} C d p e q c r (s m) O     pf1 x y pf2 = exfalso _ (Peano4 (nV m) (>< pf1))
Rec-ext-lm3 {Γ} C d p e q c r O (s k)     pf1 x y pf2 = exfalso _ (Peano4 (nV k) (symV (>< pf1)))
Rec-ext-lm3 {Γ} C d p e q c r (s m) (s k) pf1 x y pf2 =
   let pf1' : < κ natV > m ~ k
       pf1' = <> (succV-inj _ _ (>< pf1))
       ih   : ap1 (lmbC {Γ} C x) m ‣
               natV-rec (lmbC {Γ} C x) (pj1 (apel p x)) (mk-step-e {Γ} C e q x)
                 (mk-step-e-xt {Γ} C e q x) m
                 ≐
              ap1 (lmbC {Γ} C y) k ‣
                natV-rec (lmbC {Γ} C y) (pj1 (apel p y)) (mk-step-e {Γ} C e q y)
                  (mk-step-e-xt {Γ} C e q y) k
       ih = Rec-ext-lm3 {Γ} C d p e q c r m k pf1' x y pf2
       main : ap1 (lmbC {Γ} C x) (s m) ‣
              mk-step-e {Γ} C e q x m
              (natV-rec (lmbC {Γ} C x) (pj1 (apel p x)) (mk-step-e {Γ} C e q x)
              (mk-step-e-xt {Γ} C e q x) m)
               ≐
             ap1 (lmbC {Γ} C y) (s k) ‣
             mk-step-e {Γ} C e q y k
             (natV-rec (lmbC {Γ} C y) (pj1 (apel p y)) (mk-step-e {Γ} C e q y)
             (mk-step-e-xt {Γ} C e q y) k)
       main = mk-step-e-xt2 {Γ} C e q x y m k _ _ pf2 pf1' ih
   in main   



Rec-ext-lm : {Γ : ctx}
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> (x y : || κ Γ ||)
      -> < κ Γ > x ~ y 
      -> Rec-op C d p e q c r x ≐ Rec-op C d p e q c r y
Rec-ext-lm {Γ} C d p e q c r x y pf = 
  let  
       px1 : # (apt (C [[ els (Nat-i-O Γ) ]]) x)
       px1 = pj1 (apel p x)
       py1 : # (apt (C [[ els (Nat-i-O Γ) ]]) y)
       py1 = pj1 (apel p y)
       rx1 : # (apt (Nat Γ) x)
       rx1 = pj1 (apel r x)
       rx2 = pj2 (apel r x)
       ry1 : # (apt (Nat Γ) y)
       ry1 = pj1 (apel r y)
       ry2 = pj2 (apel r y)
       cxcyeq :  apr c x ≐ apr c y
       cxcyeq = >><< (extensionality1 (raw.rawterm c) x y pf)
       rx1ry1eq : < κ natV > pj1 (apel r x) ~ pj1 (apel r y)
       rx1ry1eq = <> (traV (symV rx2) (traV cxcyeq ry2))
       lm : (ap1  (lmbC {Γ} C x) rx1) ‣ 
                  (natV-rec (lmbC {Γ} C x) px1 (mk-step-e {Γ} C e q x) (mk-step-e-xt {Γ} C e q x) rx1) 
               ≐
            (ap1  (lmbC {Γ} C y) ry1) ‣ 
                  (natV-rec (lmbC {Γ} C y) py1 (mk-step-e {Γ} C e q y) (mk-step-e-xt {Γ} C e q y) ry1)
       lm = Rec-ext-lm3 {Γ} C d p e q c r rx1 ry1 rx1ry1eq x y pf
    
       main :  Rec-op C d p e q c r x ≐ Rec-op C d p e q c r y
       main = lm
  in main


Rec-ext : {Γ : ctx}
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> (x y : || κ Γ ||)
      -> < κ Γ > x ~ y 
      -> << VV >> Rec-op C d p e q c r x ~ Rec-op C d p e q c r y
Rec-ext {Γ} C d p e q c r x y pf = <<>> (Rec-ext-lm {Γ} C d p e q c r x y pf)


Rec : {Γ : ctx}
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> raw Γ
Rec {Γ} C d p e q c r = mkraw (record { op = Rec-op {Γ} C d p e q c r  
                                      ; ext = Rec-ext {Γ} C d p e q c r })

N-sub : {Δ Γ : ctx}
      -> (f : subst Δ Γ)
      ->  subst  (Δ ▷ Nat Δ) (Γ ▷ Nat Γ)
N-sub {Δ} {Γ} f = ↑ (Nat Γ) f

C-sub : {Δ Γ : ctx}
      -> (f : subst Δ Γ)
      -> (C : ty (Γ ▷ Nat Γ))
      -> subst ((Δ ▷ Nat Δ) ▷ (C [[ N-sub f ]])) ((Γ ▷ Nat Γ) ▷ C)
C-sub {Δ} {Γ} f C = ↑ C (N-sub f)

-- *** TO DO :


Rec-sub-lm2 : {Δ Γ : ctx}
      -> (f : subst Δ Γ)
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (p' : Δ ==> (d [ f ]) :: C [[  N-sub f  ]] [[ els (Nat-i-O Δ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q  : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (q' : (Δ ▷ Nat Δ ) ▷ (C [[ N-sub f ]])  ==> 
               e [ C-sub f C ] ::  C [[  N-sub f  ]] [[ step-sub Δ ]] [[ ↓ ( C [[  N-sub f  ]]) ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> (r' : Δ ==> (c [ f ]) :: (Nat Γ) [[ f ]])
      -> (x  : || κ Δ ||)
      -> (u v : || κ natV ||) ->  < κ natV > u ~ v
      ->    (ap1  (lmbC {Γ} C (aps f x)) u) ‣ 
                 (natV-rec (lmbC {Γ} C (aps f x)) (pj1 (apel p (aps f x))) 
                          (mk-step-e {Γ} C e q (aps f x)) (mk-step-e-xt {Γ} C e q (aps f x)) 
                     u)
              ≐
            (ap1  (lmbC {Δ} (C [[ N-sub f ]]) x) v) ‣ 
                 (natV-rec (lmbC {Δ} (C [[ N-sub f ]]) x) (pj1 (apel p' x))
                       (mk-step-e {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x) 
                       (mk-step-e-xt {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x)
                  v)
Rec-sub-lm2 {Δ} {Γ} f C d p p' e q q' c r r' x O O eq = 
  let eq3 : apr d (aps f x) ≐ apr (d [ f ]) x
      eq3 = refV _
      eq1 = pj2 (apel p (aps f x))
      eq2 = pj2 (apel p' x)
      lm :  ap1 (lmbC {Γ} C (aps f x)) O ‣ pj1 (apel p (aps f x)) ≐  
            ap1 (lmbC {Δ} (C [[ N-sub f ]]) x) O ‣ pj1 (apel p' x)
      lm = traV (symV eq1) (traV eq3 eq2)
  in lm 

Rec-sub-lm2 {Δ} {Γ} f C d p p' e q q' c r r' x O (s v) eq = exfalso _ (Peano4 _ (>< (sym eq))) 
Rec-sub-lm2 {Δ} {Γ} f C d p p' e q q' c r r' x (s u) O eq = exfalso _ (Peano4 _ (>< eq)) 
Rec-sub-lm2 {Δ} {Γ} f C d p p' e q q' c r r' x (s u) (s v) eq = 
    let eq' : < κ natV > u ~ v
        eq' = succ-inj u v eq
        eq2 : (type (Nat Γ) • aps f x) ‣ u ≐ (type (Nat Γ) • aps f x) ‣ v
        eq2 = >< eq'
        IH  : ap1 (lmbC {Γ} C (aps f x)) u ‣
                  natV-rec (lmbC {Γ} C (aps f x)) (pj1 (apel p (aps f x)))
                         (mk-step-e {Γ} C e q (aps f x)) (mk-step-e-xt {Γ} C e q (aps f x)) u
                        ≐
              ap1 (lmbC {Δ} (C [[ N-sub f ]]) x) v ‣
                  natV-rec (lmbC {Δ} (C [[ N-sub f ]]) x) (pj1 (apel p' x))
                         (mk-step-e {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x)
                           (mk-step-e-xt {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x) v
        IH = Rec-sub-lm2 {Δ} {Γ} f C d p p' e q q' c r r' x u v eq'
        rc1 : || κ (ap1 (lmbC {Γ} C (aps f x)) u) ||
        rc1 = (natV-rec (lmbC {Γ} C (aps f x)) (pj1 (apel p (aps f x)))
                     (mk-step-e {Γ} C e q (aps f x)) 
                     (mk-step-e-xt {Γ} C e q (aps f x)) u)
        rc2 : || κ (ap1 (lmbC {Δ} (C [[ N-sub f ]]) x) v) ||
        rc2 = (natV-rec (lmbC {Δ} (C [[ N-sub f ]]) x) (pj1 (apel p' x))
                     (mk-step-e {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x)
                     (mk-step-e-xt {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x) v) 
        IH'  : apt C (aps f x , u) ‣ rc1
                        ≐
               apt C (aps f x , v) ‣  rc2
        IH' = IH
        IH2  : < κ (Γ ▷ Nat Γ ▷ C) > ((aps f x , u) , rc1) ~ ((aps f x , v) , rc2)
        IH2 = <> (pairV-ext (pairV-ext (refV _) eq2) IH')
  --      lm = (mk-step-e-xt {Γ} C e q (aps f x))
  --      lm2 = (mk-step-e-xt {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x)
        exe :    (apr e ((aps f x , u) , rc1))
                               ≐
                 (apr e ((aps f x , v) , rc2))
        exe = >><< (extensionality1 (raw.rawterm e) 
                              (((aps f x) , u) , rc1) (((aps f x) , v) , rc2) IH2)
        eq1 : apr e ((aps f x , u) , rc1) ≐ 
              apt ((C [[ step-sub Γ ]]) [[ ↓ C ]])
                   ((aps f x , u) , rc1)  ‣
                  pj1 (apel q (((aps f x) , u) , rc1))
        eq1 = pj2 (apel q (((aps f x) , u) , rc1))
        eq2 : apr (e [ C-sub f C ]) ((x , v) , rc2)
                 ≐
             apt (((C [[ N-sub f ]]) [[ step-sub Δ ]]) [[ ↓ (C [[ N-sub f ]]) ]])
                    ((x , v) , rc2)
              ‣   pj1 (apel q' ((x , v) , rc2))
        eq2 = pj2 (apel q' ((x , v) , rc2))
        pf = (>><<
             (ape
              (tyeq-from-eq ((C [[ N-sub f ]]) [[ ↓ (C [[ N-sub f ]]) ]])
               (C [[ N-sub f ⌢ ↓ (C [[ N-sub f ]]) ]])
               (Sub-comp-prop-sym C (N-sub f) (↓ (C [[ N-sub f ]]))))
              ((x , v) , rc2)))
        lm0 :  (apr e ((aps f x , v) , rc2)) ≐ apr (e [ C-sub f C ]) ((x , v) , rc2)
        lm0 = >><< (extensionality1 (raw.rawterm e) _ _ 
                        (<> (pairV-ext (pairV-ext (refV _) (refV _)) (e+prop pf rc2) )))

        lm1 : apt (((C [[ N-sub f ]]) [[ step-sub Δ ]]) [[ ↓ (C [[ N-sub f ]]) ]])
                    ((x , v) , rc2)
              ‣   pj1 (apel q' ((x , v) , rc2))
               ≐
              apt C (aps f x , s v) ‣  pj1 (apel q' ((x , v) , rc2))
        lm1 = refV _
        lm2 : (apr e ((aps f x , v) , rc2)) ≐
              apt C (aps f x , s v) ‣  pj1 (apel q' ((x , v) , rc2))
        lm2 = traV lm0 (traV eq2 lm1)
        lm3 :  apt C (aps f x , s u) ‣
                  pj1 (apel q (((aps f x) , u) , rc1))
                 -- mk-step-e {Γ} C e q (aps f x) u rc1
                  ≐
                apt C (aps f x , s v) ‣
                  pj1 (apel q' ((x , v) , rc2))
                 --  mk-step-e {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x v rc2
        lm3 = traV (symV eq1) (traV exe lm2) 
        main : 
                apt C (aps f x , s u) ‣                  
                  mk-step-e {Γ} C e q (aps f x) u rc1
                  ≐
                apt C (aps f x , s v) ‣
                   mk-step-e {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x v rc2
        main = lm3
    in main 

{--


mk-step-e  {Γ} C e q u m z = pj1 (apel q ((u , m) , z))


mk-step-e-xt2 :  {Γ : ctx}
      -> (C : ty (Γ ▷ Nat Γ))
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (z z' : || κ Γ ||)     
      -> (m m' : N) -> (u :  || κ (apt C (z , m)) ||) -> (v :  || κ (apt C (z' , m')) ||)
               -> < κ Γ > z ~ z'  -> < κ natV > m ~ m'
               -> (apt C (z , m)) ‣ u ≐ (apt C (z' , m')) ‣ v ->
                     (apt C (z , (s m))) ‣ (mk-step-e {Γ} C e q z m u) 
                   ≐ (apt C (z' , (s m'))) ‣ (mk-step-e {Γ} C e q z' m' v)

natV-rec-lm-s : 
         (C : setoidmap1 (κ natV) VV)
      -> (d : || κ (ap1 C O) ||)
      -> (e : (m : || κ natV ||) -> (z :  || κ (ap1 C m) ||) ->  || κ (ap1 C (s m)) ||)
      -> (xt :  (m  k : || κ natV ||) -> (u :  || κ (ap1 C m) ||) -> (v :  || κ (ap1 C k) ||)
               -> < κ natV > m ~ k -> (ap1 C m) ‣ u ≐ (ap1 C k) ‣ v ->
                     (ap1 C (s m)) ‣ (e m u) ≐ (ap1 C (s k)) ‣ (e k v))
      -> (m : || κ natV ||)
      -> (ap1 C (s m)) ‣ (natV-rec C d e xt (s m)) ≐   (ap1 C (s m)) ‣ (e m (natV-rec C d e xt m))

--}

Rec-sub-lm : {Δ Γ : ctx}
      -> (f : subst Δ Γ)
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (p' : Δ ==> (d [ f ]) :: C [[  N-sub f  ]] [[ els (Nat-i-O Δ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q  : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]]) 
      -> (q' : (Δ ▷ Nat Δ ) ▷ (C [[ N-sub f ]])  ==> 
               e [ C-sub f C ] ::  C [[  N-sub f  ]] [[ step-sub Δ ]] [[ ↓ ( C [[  N-sub f  ]]) ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> (r' : Δ ==> (c [ f ]) :: (Nat Γ) [[ f ]])
      -> (x  : || κ Δ ||)
      ->  Rec-op {Γ} C d p e q c r (aps f x) ≐ 
          Rec-op {Δ} (C [[ N-sub f ]]) (d [ f ]) p' (e [ C-sub f C ]) q' (c [ f ])  r' x
Rec-sub-lm {Δ} {Γ} f C d p p' e q q' c r r' x =
     let ts = aps f x
         tm1 = pj1 (apel r (aps f x))
         tm4 = pj2 (apel r (aps f x))
         tm2 = pj1 (apel r' x)
         tm3 = pj2 (apel r' x)
         eq : < κ natV > tm1 ~ tm2
         eq = <> (traV (symV tm4) tm3)
         lm3 : (u v : || κ natV ||) ->  < κ natV > u ~ v ->
             (ap1  (lmbC {Γ} C (aps f x)) u) ‣ 
                 (natV-rec (lmbC {Γ} C (aps f x)) (pj1 (apel p (aps f x))) 
                          (mk-step-e {Γ} C e q (aps f x)) (mk-step-e-xt {Γ} C e q (aps f x)) 
                     u)
              ≐
             -- Rec-op {Δ} (C [[ N-sub f ]]) (d [ f ]) p' (e [ C-sub f C ]) q' (c [ f ])  r'  x
             (ap1  (lmbC {Δ} (C [[ N-sub f ]]) x) v) ‣ 
                 (natV-rec (lmbC {Δ} (C [[ N-sub f ]]) x) (pj1 (apel p' x))
                       (mk-step-e {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x) 
                       (mk-step-e-xt {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x)
                  v)
         lm3 = Rec-sub-lm2 {Δ} {Γ} f C d p p' e q q' c r r' x
         lm2 : (ap1  (lmbC {Γ} C (aps f x)) tm1) ‣ 
                 (natV-rec (lmbC {Γ} C (aps f x)) (pj1 (apel p (aps f x))) 
                          (mk-step-e {Γ} C e q (aps f x)) (mk-step-e-xt {Γ} C e q (aps f x)) 
                     tm1)
              ≐
             -- Rec-op {Δ} (C [[ N-sub f ]]) (d [ f ]) p' (e [ C-sub f C ]) q' (c [ f ])  r'  x
             (ap1  (lmbC {Δ} (C [[ N-sub f ]]) x) tm2) ‣ 
                 (natV-rec (lmbC {Δ} (C [[ N-sub f ]]) x) (pj1 (apel p' x))
                       (mk-step-e {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x) 
                       (mk-step-e-xt {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x)
                  tm2)
         lm2 = lm3 tm1 tm2 eq
         lm : -- Rec-op {Γ} C d p e q c r (aps f x) ≐ 
             (ap1  (lmbC {Γ} C (aps f x)) (pj1 (apel r (aps f x)))) ‣ 
                 (natV-rec (lmbC {Γ} C (aps f x)) (pj1 (apel p (aps f x))) 
                          (mk-step-e {Γ} C e q (aps f x)) (mk-step-e-xt {Γ} C e q (aps f x)) 
                     (pj1 (apel r (aps f x))))
              ≐
             -- Rec-op {Δ} (C [[ N-sub f ]]) (d [ f ]) p' (e [ C-sub f C ]) q' (c [ f ])  r'  x
             (ap1  (lmbC {Δ} (C [[ N-sub f ]]) x) (pj1 (apel r' x))) ‣ 
                 (natV-rec (lmbC {Δ} (C [[ N-sub f ]]) x) (pj1 (apel p' x))
                       (mk-step-e {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x) 
                       (mk-step-e-xt {Δ} (C [[ N-sub f ]]) (e [ C-sub f C ]) q' x)
                  (pj1 (apel r' x)))

         lm = lm2
     in lm



{-- explicitly:
   Rec-op {Γ} C d p e q c r u 
   = (ap1  (lmbC {Γ} C u) (pj1 (apel r u))) ‣ 
     (natV-rec (lmbC {Γ} C u) (pj1 (apel p u)) (mk-step-e {Γ} C e q u) (mk-step-e-xt {Γ} C e q u) (pj1 (apel r u)))
--}


Rec-sub' : {Δ Γ : ctx}
      -> (f : subst Δ Γ)
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (p' : Δ ==> (d [ f ]) :: C [[  N-sub f  ]] [[ els (Nat-i-O Δ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q  : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (q' : (Δ ▷ Nat Δ ) ▷ (C [[ N-sub f ]])  ==> e [ C-sub f C ] ::  C [[  N-sub f  ]] [[ step-sub Δ ]] [[ ↓ ( C [[  N-sub f  ]]) ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> (r' : Δ ==> (c [ f ]) :: (Nat Γ) [[ f ]])
      -> << Raw Δ >> ((Rec {Γ} C d p e q c r) [ f ])
                   ~ (Rec {Δ} (C [[  N-sub f  ]]) (d [ f ]) p' (e [ C-sub f C ])  q' (c [ f ]) r')
Rec-sub' {Δ} {Γ} f C d p p' e q q' c r r' = <<>> (<<>> (λ x → <<>> (Rec-sub-lm {Δ} {Γ} f C d p p' e q q' c r r' x)))








Nat-e : {Γ : ctx} 
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> Γ ==> Rec C d p e q c r :: C [[ els r ]]
Nat-e {Γ} C d p e q c r = 
      mk-elt (λ x ->
                let rx = apel r x
                    rx1 : # (apt (Nat Γ) x)
                    rx1 = pj1 rx
                    rx2 : apr c x ≐ apt (Nat Γ) x ‣ pj1 (apel r x)
                    rx2 = pj2 rx
                    lm : apt (C [[ els r ]]) x ≐ apt C (x , rx1)
                    lm = refV _
                    lm2 :  apr (Rec C d p e q c r) x ∈  apt C (x , rx1)
                    lm2 = Rec-op-lm2 {Γ} C d p e q c r x
                    main : apr (Rec C d p e q c r) x ∈ apt (C [[ els r ]]) x
                    main = lm2
                in main
             )

Nat-c-O-raw-eq : {Γ : ctx} 
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (x : || κ Γ ||)
      -> apr (Rec C d p e q (zero Γ) (Nat-i-O Γ)) x ≐ apr d x
Nat-c-O-raw-eq {Γ} C d p e q x =
   let px = apel p x
       px1 = pj1 px
       px2 = pj2 px
       tm =       (natV-rec (lmbC {Γ} C x) (pj1 (apel p x)) 
                          (mk-step-e {Γ} C e q x) 
                           (mk-step-e-xt {Γ} C e q x) (pj1 (apel (Nat-i-O Γ) x)))
       lm2  : < κ (ap1 (lmbC {Γ} C x) O) > tm ~ px1
       lm2 = refl _ px1
       main : apr (Rec C d p e q (zero Γ) (Nat-i-O Γ)) x ≐ apr d x
       main = symV px2
   in main



Nat-c-O : {Γ : ctx} 
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> Γ ==> Rec C d p e q (zero Γ) (Nat-i-O Γ) == d :: C [[ els (Nat-i-O Γ)]]
Nat-c-O {Γ} C d p e q = pair (Nat-c-O-raw-eq {Γ} C d p e q)
                             (pair (Nat-e {Γ} C d p e q (zero Γ) (Nat-i-O Γ)) p)

Nat-c-s-raw-eq : {Γ : ctx} 
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (a : raw Γ)
      -> (r : Γ ==> a :: Nat Γ)
      -> (x : || κ Γ ||)
      -> apr (Rec C d p e q (succ _ a) (Nat-i-s Γ a r)) x ≐
         apr (e [ ext C (els r) (Rec C d p e q a r) (Nat-e C d p e q a r) ]) x
Nat-c-s-raw-eq {Γ} C d p e q a r x = 
   let ax = apel r x
       ax1 = pj1 ax
       ax2 = pj2 ax
       rcx = apel (Nat-e C d p e q a r) x
       rcx1 = pj1 rcx
       rcx2 = pj2 rcx
       qi = apel q ((x , ax1) , rcx1 )
       qi1 = pj1 qi
       qi2 = pj2 qi
       tm =  (natV-rec (lmbC {Γ} C x) (pj1 (apel p x)) 
                          (mk-step-e {Γ} C e q x) 
                           (mk-step-e-xt {Γ} C e q x) (pj1 (apel (Nat-i-s Γ a r) x)))
       tm' = (mk-step-e {Γ} C e q x) ax1 (natV-rec (lmbC {Γ} C x) 
                  (pj1 (apel p x)) (mk-step-e {Γ} C e q x) (mk-step-e-xt {Γ} C e q x) ax1)
       eq : < κ (apt C (x , s (pj1 (apel r x)))) > tm ~ tm'
       eq = refl _ _
       main : apr (Rec C d p e q (succ _ a) (Nat-i-s Γ a r)) x ≐
              apr (e [ ext C (els r) (Rec C d p e q a r) (Nat-e C d p e q a r) ]) x
       main = traV (>< eq) (symV qi2)
   in main



Nat-c-s : {Γ : ctx} 
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (a : raw Γ)
      -> (r : Γ ==> a :: Nat Γ)
      -> Γ ==> Rec C d p e q (succ Γ a) (Nat-i-s Γ a r) 
           == e [  ext C (els r) (Rec C d p e q a r) (Nat-e {Γ} C d p e q a r) ] :: C [[ els (Nat-i-s Γ a r)]]
-- R d e (s a) = e a (R d e a)
-- < < 1_Γ , a> , Rec C d o e q a r >
-- < els r ,  Rec C d o e q a r  >
Nat-c-s {Γ} C d p e q a r = pair (Nat-c-s-raw-eq {Γ} C d p e q a r) 
                                 (pair (Nat-e {Γ} C d p e q (succ Γ a) (Nat-i-s Γ a r)) 
                                       (subj-red {Γ} {C [[ els (Nat-i-s Γ a r) ]]} 
                                          (Rec C d p e q (succ Γ a) (Nat-i-s Γ a r)) 
                                          (e [ ext C (els r) (Rec C d p e q a r) (Nat-e C d p e q a r) ])
                                           (Nat-e {Γ} C d p e q (succ Γ a) (Nat-i-s Γ a r)) 
                                           (<<>> (<<>> (λ x → <<>> ((Nat-c-s-raw-eq {Γ} C d p e q a r) x))))))

{--
-- recall

ext-eq' : {Γ : ctx}
--
      -> (A  A' : ty Γ) 
      -> (Γ ==> A == A')
-- --------------------------
      -> << Ctx >> (Γ ▷ A) ~ (Γ ▷ A')
ext-eq' {Γ} A A' p = ?

--}


mk-step-e-xt3 :  {Γ : ctx}
      -> (C C' : ty (Γ ▷ Nat Γ))
      -> (Cq : (Γ ▷ Nat Γ)  ==> C == C')
      -> (e  : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (e'  : raw ((Γ ▷ Nat Γ) ▷ C'))
      -> (q : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (q' : (Γ ▷ Nat Γ) ▷ C'  ==> e' :: C' [[ step-sub Γ ]] [[ ↓ C' ]])
      -> << Raw ((Γ ▷ Nat Γ) ▷ C) >> e ~ (e' [ subst-trp (ext-eq' {Γ ▷ Nat Γ} C C' Cq) ])
      -> (z z' : || κ Γ ||)           
      -> (m m' : N) -> (u :  || κ (apt C (z , m)) ||) -> (v :  || κ (apt C' (z' , m')) ||)
               -> < κ Γ > z ~ z'  -> < κ natV > m ~ m'
               -> (apt C (z , m)) ‣ u ≐ (apt C' (z' , m')) ‣ v ->
                     (apt C (z , (s m))) ‣ (mk-step-e {Γ} C e q z m u) 
                   ≐ (apt C' (z' , (s m'))) ‣ (mk-step-e {Γ} C' e' q' z' m' v)
mk-step-e-xt3 {Γ} C C' Cq e e' q q' eq z z' m m' u v p1 p2 p3 = 
    let lm1 : apr e ((z , m) , u) ∈ apt C (z , (s m))
        lm1 = apel q ((z , m) , u)
        eq1 : apr e ((z , m) , u) ≐ apt C (z , s m) ‣ pj1 (apel q ((z , m) , u))
        eq1 = pj2 lm1
        lm2 : apr e' ((z' , m') , v) ∈ apt C' (z' , (s m'))
        lm2 = apel q' ((z' , m') , v)
        eq2 : apr e' ((z' , m') , v) ≐ apt C' (z' , s m') ‣ pj1 (apel q' ((z' , m') , v))
        eq2 = pj2 lm2 
        lmeq = >><< (>><< (>><< eq) ((z , m) , u))
        eq4 : (Γ ▷ Nat Γ) ‣ (z , m)  ≐  (Γ ▷ Nat Γ) ‣ (z' , m')
        eq4 = pairV-ext (>< p1) (>< p2) 
        eq5  : < κ (Γ ▷ Nat Γ ▷ C') >
               ap (κ-trp (ext-eq C C' Cq)) ((z , m) , u) ~
              ((z , m) , ap (κ-Fam ±± ape Cq (z , m)) u)
        eq5 = ext-eq-lm {Γ ▷ Nat Γ} C C' Cq (z , m) u 

        eq8 :  apt C (z , m) ‣ u ≐ apt C' (z , m) ‣ ap (κ-Fam ±± ape Cq (z , m)) u 
        eq8 = e+prop' (apt C (z , m)) (apt C' (z , m)) (>><< (ape Cq  (z , m))) u
        eq7 : (ty.type C' • (z , m)) ‣ ap (κ-Fam ±± ape Cq (z , m)) u ≐
                (ty.type C' • (z' , m')) ‣ v
        eq7 = traV (symV eq8) p3
        eq6 : < κ (Γ ▷ Nat Γ ▷ C') >  (z , m) , ap (κ-Fam ±± ape Cq (z , m)) u ~ ((z' , m') , v)
        eq6 = <> (pairV-ext eq4 eq7)

        eq3 :  < κ (Γ ▷ Nat Γ ▷ C') >   ap (subst.cmap (subst-trp (ext-eq' C C' Cq))) ((z , m) , u) ~
                                           ((z' , m') , v)
        eq3 = tra {κ (Γ ▷ Nat Γ ▷ C')} eq5 eq6   -- to do ***
        lmeq2 :  ap1 (raw.rawterm (e' [ subst-trp (ext-eq' C C' Cq) ])) ((z , m) , u)
                  ≐ ap1 (raw.rawterm e') ((z' , m') , v)
        lmeq2 =  >><< (extensionality1 (raw.rawterm e') _ _ eq3)
    
        main :  (apt C (z , (s m))) ‣ (mk-step-e {Γ} C e q z m u) 
                   ≐ (apt C' (z' , (s m'))) ‣ (mk-step-e {Γ} C' e' q' z' m' v)
        main = traV (symV eq1) (traV (traV lmeq lmeq2) eq2)
    in main

Rec-cong' : {Γ : ctx}
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
Rec-cong' {Γ} C C' d d' p p' e e' q q' c c' r r' Cq dq eq cq = 
     <<>> (<<>> (λ x → 
      <<>> (
           let cqx = (>><< (>><< cq) x)
               eq1 : < κ natV > pj1 (apel r x) ~ pj1 (apel r' x)
               eq1 = <> (traV (symV (pj2 (apel r x))) (traV (>><< cqx) (pj2 (apel r' x))))
               dqx = (>><< (>><< dq) x)
               eq2 : ap1 (lmbC {Γ} C x) O ‣ pj1 (apel p x) ≐ ap1 (lmbC {Γ} C' x) O ‣ pj1 (apel p' x)
               eq2 = traV (symV (pj2 (apel p x))) (traV (>><< dqx) (pj2 (apel p' x)))
               eq3 : (k k' : || κ natV ||) (z : || κ (ap1 (lmbC {Γ} C x) k) ||)
                    (z' : || κ (ap1 (lmbC {Γ} C' x) k') ||) →
                    < κ natV > k ~ k' →
                    ap1 (lmbC {Γ} C x) k ‣ z ≐ ap1 (lmbC {Γ} C' x) k' ‣ z' →
                    ap1 (lmbC {Γ} C x) (s k) ‣ mk-step-e {Γ} C e q x k z ≐
                    ap1 (lmbC {Γ} C' x) (s k') ‣ mk-step-e {Γ} C' e' q' x k' z'
               eq3 = λ k k' z z' pf pf' ->
                       let ts = mk-step-e-xt3 {Γ} C C' Cq e e' q q' eq x x k k' z z' (<> (refV _) ) pf pf'
                           lm : ap1 (lmbC {Γ} C x) (s k) ‣ mk-step-e {Γ} C e q x k z ≐
                                ap1 (lmbC {Γ} C' x) (s k') ‣ mk-step-e {Γ} C' e' q' x k' z'
                           lm = ts
                       in lm


               lm : 
                 (ap1  (lmbC {Γ} C x) (pj1 (apel r x))) ‣ 
                   (natV-rec (lmbC {Γ} C x) (pj1 (apel p x)) 
                     (mk-step-e {Γ} C e q x) (mk-step-e-xt {Γ} C e q x) (pj1 (apel r x)))
                  ≐
                 (ap1  (lmbC {Γ} C' x) (pj1 (apel r' x))) ‣ 
                   (natV-rec (lmbC {Γ} C' x) (pj1 (apel p' x)) 
                     (mk-step-e {Γ} C' e' q' x) (mk-step-e-xt {Γ} C' e' q' x) (pj1 (apel r' x)))
               lm = natV-rec-ext2 
                        (lmbC {Γ} C x) (lmbC {Γ} C' x) 
                        (pj1 (apel p x)) 
                        (pj1 (apel p' x))
                        (mk-step-e {Γ} C e q x) 
                        (mk-step-e-xt {Γ} C e q x) 
                        (mk-step-e {Γ} C' e' q' x) 
                        (mk-step-e-xt {Γ} C' e' q' x)
                        (pj1 (apel r x)) 
                        (pj1 (apel r' x)) 
                        eq1 
                        eq2
                        eq3

               main :  (VV classoid.∼ raw.rawterm (Rec C d p e q c r) • x)
                          (raw.rawterm (Rec C' d' p' e' q' c' r') • x)
               main = lm
           in main
           )))


Rec-cong : {Γ : ctx}
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
      -> (t : (Γ ▷ Nat Γ)  ==> C == C')
      -> (Γ ==> d == d' :: C [[ els (Nat-i-O Γ) ]])
      -> ((Γ ▷ Nat Γ) ▷ C ==> e == (e' [ subst-trp (ext-eq' {Γ ▷ Nat Γ} C C' t) ]) ::
                     C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (Γ ==> c == c' :: Nat Γ)
      -> (Γ ==>  Rec {Γ} C d p e q c r == Rec {Γ} C' d' p' e' q' c' r' :: C [[ els r ]])
Rec-cong {Γ} C C' d d' p p' e e' q q' c c' r r' t dq eq cq =  
    let  dq' = (Raw-lm2 {Γ} {d} {d'} (prj1 dq))
         eq' = (Raw-lm2 {(Γ ▷ Nat Γ) ▷ C } {e} {(e' [ subst-trp (ext-eq' {Γ ▷ Nat Γ} C C' t) ])} (prj1 eq))
         cq' = (Raw-lm2 {Γ} {c} {c'} (prj1 cq))
         lm = Rec-cong' {Γ} C C' d d' p p' e e' q q' c c' r r' t dq' eq' cq'
      
    in pair (Raw-lm lm) (pair (Nat-e {Γ} C d p e q c r) (subj-red _ _ (Nat-e {Γ} C d p e q c r ) lm))
    



Rec-sub : {Δ Γ : ctx}
      -> (h : subst Δ Γ)
      -> (C : ty (Γ ▷ Nat Γ))
      -> (d : raw Γ)
      -> (p : Γ ==> d :: C [[ els (Nat-i-O Γ) ]])
      -> (p' : Δ ==> (d [ h ]) :: C [[  N-sub h  ]] [[ els (Nat-i-O Δ) ]])
      -> (e : raw ((Γ ▷ Nat Γ) ▷ C))
      -> (q  : (Γ ▷ Nat Γ) ▷ C  ==> e :: C [[ step-sub Γ ]] [[ ↓ C ]])
      -> (q' : (Δ ▷ Nat Δ ) ▷ (C [[ N-sub h ]])  ==> e [ C-sub h C ] ::  C [[  N-sub h  ]] [[ step-sub Δ ]] [[ ↓ ( C [[  N-sub h  ]]) ]])
      -> (c : raw Γ)
      -> (r : Γ ==> c :: Nat Γ)
      -> (r' : Δ ==> (c [ h ]) :: (Nat Γ) [[ h ]])
      ->  Δ ==> ((Rec {Γ} C d p e q c r) [ h ])
                   == (Rec {Δ} (C [[  N-sub h  ]]) (d [ h ]) p' (e [ C-sub h C ])  q' (c [ h ]) r') :: C [[ els r ]] [[ h ]]
Rec-sub {Δ} {Γ} h C d p p' e q q' c r r' = 
    let lm = Rec-sub' {Δ} {Γ} h C d p p' e q q' c r r'
        lm2 :  Δ ==> Rec C d p e q c r [ h ] :: (C [[ els r ]]) [[ h ]]
        lm2 = elt-subst h (Nat-e {Γ} C d p e q c r)
    in  pair (Raw-lm lm) (pair lm2 (subj-red _ _ lm2 lm))



-- Empty type

N0 :  (Γ : ctx) -> ty Γ
N0 Γ = Const zeroV Γ

N0-sub :  (Δ Γ : ctx) -> (f : subst Δ Γ)
    -> Δ ==> (N0 Γ) [[ f ]] == (N0 Δ)
N0-sub Δ Γ f = mk-eqty (λ x → <<>> (refV _))


R1₀ : {C : N₀ -> Set1} -> (c : N₀) -> C c
R1₀ ()

Exfalso : (A : Set1) -> False -> A
Exfalso A u = R1₀ {\z -> A} u

R0-op : {Γ : ctx}
      -> (C : ty (Γ ▷ N0 Γ))
      -> (c : raw Γ)
      -> (r : Γ ==> c :: N0 Γ)
      -> || κ Γ ||
      -> V
R0-op {Γ} C c r x = Exfalso _ (pj1 (apel r x))

R0-ext : {Γ : ctx}
      -> (C : ty (Γ ▷ N0 Γ))
      -> (c : raw Γ)
      -> (r : Γ ==> c :: N0 Γ)
      -> (x y : || κ Γ ||) 
      -> < κ Γ > x ~ y 
      -> << VV >> R0-op C c r x ~ R0-op C c r y
R0-ext {Γ} C c r x y p =  exfalso _ (pj1 (apel r x))

R0 : {Γ : ctx}
      -> (C : ty (Γ ▷ N0 Γ))
      -> (c : raw Γ)
      -> (r : Γ ==> c :: N0 Γ)
      -> raw Γ
R0 {Γ} C c r = mkraw (record { op = R0-op {Γ} C c r 
                             ; ext = R0-ext {Γ} C c r })

R0-sub' : {Δ Γ : ctx}
      -> (f : subst Δ Γ)
      -> (C : ty (Γ ▷ N0 Γ))
      -> (c : raw Γ)
      -> (r : Γ ==> c :: N0 Γ)
      -> (r' : Δ ==> c [ f ] :: (N0 Γ) [[ f ]])
      -> << Raw Δ >>  ((R0 {Γ} C c r) [[ f ]])  ~  (R0 {Δ} (C [[ ↑ (N0 Γ) f ]]) (c [ f ]) r')
R0-sub' {Δ} {Γ} f C c r r' = <<>> (<<>> (λ x → <<>> (exfalso _ (pj1 (apel r' x)))))
 

-- ↑ :  {Δ Γ : ctx}  -> (A : ty Γ)    -> (h : subst Δ Γ) 
--     -> subst (Δ ▷ (A [[ h ]])) (Γ ▷ A)
-- ↑ A h = qq A h


N0-e : {Γ : ctx} 
      -> (C : ty (Γ ▷ N0 Γ))
      -> (c : raw Γ)
      -> (r : Γ ==> c :: N0 Γ)
      -> Γ ==> R0 C c r :: C [[ els r ]]
N0-e {Γ} C c r = mk-elt (λ x → exfalso _ (pj1 (apel r x)))


R0-cong' : {Γ : ctx}
      -> (C C' : ty (Γ ▷ N0 Γ))
      -> (c c' : raw Γ)
      -> (r : Γ ==> c :: N0 Γ)
      -> (r' : Γ ==> c' :: N0 Γ)
      -> (Cq : (Γ ▷ N0 Γ)  ==> C == C')
      -> << Raw Γ >> c ~ c'
      -> << Raw Γ >>  R0 {Γ} C c r ~ R0 {Γ} C' c' r'
R0-cong' {Γ} C C' c c' r r' Cq p = <<>> (<<>> (λ x → <<>> (exfalso _ (pj1 (apel r x)))))

-- ** TO DO

R0-cong : {Γ : ctx}
-- 
      -> (C C' : ty (Γ ▷ N0 Γ))
      -> (c c' : raw Γ)
      -> (r : Γ ==> c :: N0 Γ)
      -> (r' : Γ ==> c' :: N0 Γ)
      -> (Cq : (Γ ▷ N0 Γ)  ==> C == C')
      -> (Γ ==> c == c' :: N0 Γ)
      -> Γ ==> R0 {Γ} C c r  ==  R0 {Γ} C' c' r' :: C [[ els r ]]
-- ----------------------------------------------------------------------------------------
R0-cong {Γ} C C' c c' r r' Cq p = pair (Raw-lm (R0-cong' {Γ} C C' c c' r r' Cq (Raw-lm2 (prj1 p)))) 
                                        (pair (N0-e {Γ} C c r) 
                                              (subj-red _ _ (N0-e {Γ} C c r) 
                                                  (R0-cong' {Γ} C C' c c' r r' Cq (Raw-lm2 (prj1 p)))))
-- eq-from-elteq (N0 Γ) p 
R0-sub : {Δ Γ : ctx}
--
      -> (h : subst Δ Γ)
      -> (C  : ty (Γ ▷ N0 Γ))
      -> (c  : raw Γ)
      -> (r : Γ ==> c :: N0 Γ)
      -> (r' : Δ ==> c [ h ] :: N0 Γ [[ h ]])
-- ----------------------------------------------------------------------------------------
      -> Δ ==> R0 {Γ} C c r [ h ]  ==  R0 {Δ} (C [[ ↑ (N0 Γ) h ]]) (c [ h ]) r' :: C [[ els r ]] [[ h ]] 
R0-sub {Δ} {Γ} h C c r r' = pair (Raw-lm (R0-sub' {Δ} {Γ} h C c r r')) 
                                 (pair (elt-subst h (N0-e {Γ} C c r)) 
                                       (subj-red _ _  (elt-subst h (N0-e {Γ} C c r)) (R0-sub' {Δ} {Γ} h C c r r')))


