-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt15 where

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
open import V-model-pt11


-- Bracket type former
-- Awodey and Bauer 2014

Br-op : {Γ : ctx}
   -> (A : ty Γ)
   -> (x : || κ Γ ||)
   -> V
Br-op {Γ} A x = sqV (apt A x)

-- sqV : V -> V
-- sqV u = sup (# u) (\x -> zeroV)


Br : {Γ : ctx}
   -> (A : ty Γ)
   -> ty Γ
Br {Γ} A = mkraw (record { op = Br-op {Γ} A
                         ; ext = λ x y p →
                              <<>> (sqV-ext (apt A x) (apt A y)  (>><< (extensionality1 (ty.type A) x y p)))
                         })


br :  {Γ : ctx} -> (a : raw Γ) -> raw Γ
br {Γ} a = const zeroV Γ


Br-intro :  {Γ : ctx}
--
    -> (A : ty Γ)
    -> (a : raw Γ)
    -> Γ ==> a :: A
--
    -> Γ ==> br a :: Br A
Br-intro {Γ} A a p =
     mk-elt (λ x →
                 let px = apel p x
                     px1 = pj1 px
                     px2 = pj2 px
                 in  px1 , refV _ )


Br-eqty-lm2 :  {Γ : ctx}
    -> (A : ty Γ)
    -> (a : raw Γ)
    -> Γ ==> a :: Br A
    -> (x : || κ Γ ||)
    -> apr a x ≐ zeroV
Br-eqty-lm2 {Γ} A a p x =
   let lm2 : apr a x ≐ apt (Br A) x ‣ pj1 (apel p x)
       lm2 = pj2 (apel p x)
       lm3 : apt (Br A) x ‣ pj1 (apel p x) ≐ zeroV
       lm3 = refV _
   in traV lm2 lm3

Br-eqty-lm :  {Γ : ctx}
    -> (A : ty Γ)
    -> (a b : raw Γ)
    -> Γ ==> a :: Br A
    -> Γ ==> b :: Br A
    -> (x : || κ Γ ||)
    -> apr a x ≐ apr b x
Br-eqty-lm {Γ} A a b p q x = traV (Br-eqty-lm2 {Γ} A a p x) (symV (Br-eqty-lm2 {Γ} A b q x))

Br-eqty :  {Γ : ctx}
--
    -> (A : ty Γ)
    -> (a b : raw Γ)
    -> Γ ==> a :: Br A
    -> Γ ==> b :: Br A
-- -----------------------
    ->  Γ ==> a == b :: Br A
Br-eqty {Γ} A a b p q =
       pair (Br-eqty-lm {Γ} A a b p q) (pair p q)




Br-sub-lm : {Δ Γ : ctx}
--
    -> (A : ty Γ)
    -> (f : subst Δ Γ)
    -> (x : || κ Δ ||)
    ->  (type (Br A [[ f ]]) • x) ≐ (type (Br (A [[ f ]])) • x)
Br-sub-lm {Δ} {Γ} A f x = easy-eqV _ _ _ (λ x₁ → refV _)


Br-sub : {Δ Γ : ctx}
--
    -> (A : ty Γ)
    -> (f : subst Δ Γ)
-- --------------------------------
    ->  Δ ==> (Br A) [[ f ]] == (Br (A [[ f ]]))
Br-sub {Δ} {Γ} A f =  mk-eqty (λ x → <<>> (Br-sub-lm {Δ} {Γ} A f x) )


br-sub-lm : {Δ Γ : ctx}
--
    -> (A : ty Γ)
    -> (f : subst Δ Γ)
    -> (a : raw Γ)
    -> Γ ==> a :: A
    -> << Raw Δ >> (br a) [ f ] ~ (br (a [ f ]))
br-sub-lm {Δ} {Γ} A f a p = <<>> (<<>> (λ x → <<>> (refV _)))

br-sub : {Δ Γ : ctx}
--
    -> (A : ty Γ)
    -> (f : subst Δ Γ)
    -> (a : raw Γ)
    -> Γ ==> a :: A
-- --------------------------------
    ->  Δ ==> (br a) [ f ] == (br (a [ f ])) :: (Br A) [[ f ]]
br-sub {Δ} {Γ} A f a p = pair (Raw-lm (br-sub-lm {Δ} {Γ} A f a p))
                              (pair (elt-subst f (Br-intro {Γ} A a p))
                                   (subj-red _ _ (elt-subst f (Br-intro {Γ} A a p)) (br-sub-lm {Δ} {Γ} A f a p)))


pr-x : {Γ : ctx}
    -> (A : ty Γ)
    ->  subst  (Γ ▷ A ▷ (A [[ ↓ A ]]))  (Γ ▷ A)
pr-x {Γ} A = ↓ (A [[ ↓ A ]])

pr-x-lm : {Γ : ctx}
    -> (A : ty Γ)
    -> (u : || κ Γ ||)
    -> (x y : ||  κ (apt A u) ||)
    -> < κ (Γ ▷ A) > aps (pr-x A) ((u , x) , y) ~ (u , x)
pr-x-lm {Γ} A u x y = <> (refV _)


-- should be in pt0:

apr-ext : {Γ : ctx}
     -> (a : raw Γ)  -> (x y : || κ Γ ||)
     -> < κ Γ > x ~ y
     -> apr a x ≐ apr a y
apr-ext a x y p = >><<  (extensionality1 (raw.rawterm a) x y p)


-- should be in pt1:


eq-on-ext-lm : {Γ : ctx}
    -> (A : ty Γ)
    -> (u : || κ Γ ||)
    -> (x : || κ (apt A u) ||)
    -> (v : || κ Γ ||)
    -> (p : < κ Γ > u  ~ v)
    -> (type A • u) ‣ x ≐ (type A • v) ‣ ap (κ° (type A) ± p) x
eq-on-ext-lm {Γ} A u x v p = κ°-trp-prop (type A) u v p x


eq-on-ext : {Γ : ctx}
    -> (A : ty Γ)
    -> (u : || κ Γ ||)
    -> (x : || κ (apt A u) ||)
    -> (v : || κ Γ ||)
    -> (y : || κ (apt A v) ||)
    -> (p : < κ Γ > u  ~ v)
    -> < κ (apt A v) > (ap (κ° (ty.type A) ± p) x)  ~ y
    -> < κ (Γ ▷ A) > (u , x) ~ (v , y)
eq-on-ext {Γ} A u x v y p q =
   let lm : (type A • v) ‣ ap (κ° (type A) ± p) x ≐  (type A • v) ‣ y
       lm = >< q
       lm3 :  (type A • u)  ≐ (type A • v)
       lm3 = >><< (extensionality1 (type A) u v p)
       lm2 : (type A • u) ‣ x  ≐ (type A • v) ‣ ap (κ° (type A) ± p) x
       lm2 = eq-on-ext-lm {Γ} A u x v p
   in sigmaV-eq-lm2  Γ (ty.type A) (u , x) (v , y) (>< p) (traV lm2 lm)

eq-on-ext-rev-lm : {Γ : ctx}
    -> (A : ty Γ)
    -> (u : || κ Γ ||)
    -> (x : || κ (apt A u) ||)
    -> (v : || κ Γ ||)
    -> (y : || κ (apt A v) ||)
    -> < κ (Γ ▷ A) > (u , x) ~ (v , y)
    -> < κ Γ > u ~ v
eq-on-ext-rev-lm {Γ} A u x v y q =
  let  lm : (Γ ▷ A)  ‣  (u , x)  ≐ (Γ ▷ A)  ‣ (v , y)
       lm = >< q
       lm2 : < Γ ‣ u , ((ty.type A) • u) ‣ x >  ≐ < Γ ‣ v , ((ty.type A) • v) ‣ y >
       lm2 = lm
       lm3 : Γ  ‣ u  ≐  Γ  ‣ v
       lm3 = prj1 (pairV-inv-1 lm2) -- prj1 lm
  in <> lm3


eq-on-ext-rev : {Γ : ctx}
    -> (A : ty Γ)
    -> (u : || κ Γ ||)
    -> (x : || κ (apt A u) ||)
    -> (v : || κ Γ ||)
    -> (y : || κ (apt A v) ||)
    -> (q : < κ (Γ ▷ A) > (u , x) ~ (v , y))
    -> < κ (apt A v) > (ap (κ° (ty.type A) ± (eq-on-ext-rev-lm {Γ} A u x v y q)) x)  ~ y
eq-on-ext-rev {Γ} A u x v y q =
  let  lm : (Γ ▷ A)  ‣  (u , x)  ≐ (Γ ▷ A)  ‣ (v , y)
       lm = >< q
       lm2 : < Γ ‣ u , ((ty.type A) • u) ‣ x >  ≐ < Γ ‣ v , ((ty.type A) • v) ‣ y >
       lm2 = lm
       lm3 : Γ  ‣ u  ≐  Γ  ‣ v
       lm3 = prj1 (pairV-inv-1 lm2)
       lm4 : (type A • u) ‣ x ≐ (type A • v) ‣ y
       lm4 = prj2 (pairV-inv-1 lm2)
       lm5 : (type A • v) ‣  (ap (κ° (ty.type A) ± (eq-on-ext-rev-lm {Γ} A u x v y q)) x) ≐ (type A • u) ‣ x
       lm5 = symV (eq-on-ext-lm {Γ} A u x v (<> lm3))
       main : (type A • v) ‣  (ap (κ° (ty.type A) ± (eq-on-ext-rev-lm {Γ} A u x v y q)) x) ≐ (type A • v) ‣ y
       main = traV lm5 lm4
  in <> main




two-var-lm : {Γ : ctx}
    -> (A : ty Γ)
--     -> (b : raw (Γ ▷ A))
    -> (u v : || κ Γ ||)
    -> (x : || κ (apt A u) ||)
    -> (p : < κ Γ > u ~ v)
    -> < κ (Γ ▷ A) > (u , x) ~ (v , ap (κ° (type A) ± p) x )
two-var-lm {Γ} A u v x  p = eq-on-ext {Γ} A u x v (ap (κ° (type A) ± p) x) p (<> (refV _))


b-up-lm :  {Δ Γ : ctx}  -> (h : subst Δ Γ)
    -> (A : ty Γ)   -> (b : raw (Γ ▷ A))
    -> (x  : || κ Δ ||)
    -> (y : || κ (apt (A [[ h ]]) x) ||)
    -> apr (b [[ ↑ A (h) ]]) (x , y)  ≐ apr b ((aps h x) , y)
b-up-lm {Δ} {Γ} h A b x y = >><< (extensionality1 (raw.rawterm b) _ (((aps h x) , y)) (qq-eq {Δ} {Γ} A h x y ))


pr-x-lm2 : {Γ : ctx}
    -> (A : ty Γ)
    -> (b : raw (Γ ▷ A))
    -> (u : || κ Γ ||)
    -> (x y : ||  κ (apt A u) ||)
    ->  apr (b [ pr-x A ]) ((u , x) , y) ≐ apr b (u , x)
pr-x-lm2 {Γ} A  b u x y = traV (sub-apply b (pr-x A) ((u , x) , y))
                               (apr-ext b (aps (pr-x A) ((u , x) , y)) (u , x) (pr-x-lm A u x y) )


pr-y : {Γ : ctx}
    -> (A : ty Γ)
    ->  subst  (Γ ▷ A ▷ (A [[ ↓ A ]]))  (Γ ▷ A)
pr-y {Γ} A =
  let lm : Γ ▷ A ▷ (A [[ ↓ A ]]) ==> vv (A [[ ↓ A ]]) ::
                        (A [[ ↓ A ]]) [[ ↓ (A [[ ↓ A ]]) ]]
      lm = asm (A [[ ↓ A ]])
      eq : Γ ▷ A ▷ (A [[ ↓ A ]]) ==>
                        (A [[ ↓ A ]]) [[ ↓ (A [[ ↓ A ]]) ]]  == A [[ ↓ A ⌢ ↓ (A [[ ↓ A ]]) ]]
      eq = tysym (tysubst-com A (↓ A) ( ↓ (A [[ ↓ A ]])))
      lm2 : Γ ▷ A ▷ (A [[ ↓ A ]]) ==> vv (A [[ ↓ A ]]) ::
                        A [[ ↓ A ⌢ ↓ (A [[ ↓ A ]]) ]]
      lm2 = elttyeq lm eq

  in ext A ((↓ A) ⌢ (↓ (A [[ ↓ A ]]))) (vv (A [[ ↓ A ]])) lm2

pr-y-lm : {Γ : ctx}
    -> (A : ty Γ)
    -> (u : || κ Γ ||)
    -> (x y : ||  κ (apt A u) ||)
    -> < κ (Γ ▷ A) > aps (pr-y A) ((u , x) , y) ~ (u , y)
pr-y-lm {Γ} A u x y =
     let lm : Γ ‣ aps (↓ A ⌢ ↓ (A [[ ↓ A ]])) ((u , x) , y) ≐ Γ ‣ u
         lm = refV (Γ ‣ u)
         q =  (>><<
                    (ape (tysym (tysubst-com A (↓ A) (↓ (A [[ ↓ A ]]))))
                     ((u , x) , y)))
         lm3 : (type A • aps (↓ A ⌢ ↓ (A [[ ↓ A ]])) ((u , x) , y)) ‣
                  e+
                   (>><<
                    (ape (tysym (tysubst-com A (↓ A) (↓ (A [[ ↓ A ]]))))
                     ((u , x) , y)))
                   y
                   ≐ (type A • u) ‣ y
         lm3 = symV (e+prop q y)
     in   <> (pairV-ext lm lm3)


pr-y-lm2 : {Γ : ctx}
    -> (A : ty Γ)
    -> (b : raw (Γ ▷ A))
    -> (u : || κ Γ ||)
    -> (x y : ||  κ (apt A u) ||)
    ->  apr (b [ pr-y A ]) ((u , x) , y) ≐ apr b (u , y)
pr-y-lm2 {Γ} A b u x y = traV (sub-apply b (pr-y A) ((u , x) , y))
       ( apr-ext b (aps (pr-y A) ((u , x) , y)) (u , y) (pr-y-lm A u x y))


wh-lm-op :  {Γ : ctx}
    -> (A B : ty Γ)
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ A ==> b :: B [[ ↓ A ]])
    -> << Raw (Γ ▷ A ▷ (A [[ ↓ A ]])) >> b [ pr-x A ] ~  (b [ pr-y A ])
    -> (x : || κ Γ ||)
    -> V
wh-lm-op {Γ} A B k b q r p x =  apr b (x , pj1 (apel q x))


wh-lm-op-ext :  {Γ : ctx}
    -> (A B : ty Γ)
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ A ==> b :: B [[ ↓ A ]])
    -> (p : << Raw (Γ ▷ A ▷ (A [[ ↓ A ]])) >> b [ pr-x A ] ~  (b [ pr-y A ]))
    -> (u v : || κ Γ ||)
    -> < κ Γ > u ~ v
    -> << VV >> wh-lm-op A B k b q r p u ~ wh-lm-op A B k b q r p v
wh-lm-op-ext {Γ} A B k b q r p u v t =
  let   lm1 : (z : || κ (Γ ▷ A ▷ (A [[ ↓ A ]])) ||) →
                      apr (b [ pr-x A ]) z ≐ apr (b [ pr-y A ]) z
        lm1 = Raw-lm p
        lm2 : (u : || κ Γ ||) -> (x : ||  κ (apt A u) ||) -> (y : || κ (apt A u) ||) ->
                     apr (b [ pr-x A ]) (( u , x) , y) ≐ apr (b [ pr-y A ])  (( u , x) , y)
        lm2 = λ u x y → lm1  (( u , x) , y)
        lm3 : (u : || κ Γ ||) -> (x : ||  κ (apt A u) ||) -> (y : || κ (apt A u) ||) ->
                     apr b ( u , x)  ≐ apr b (u , y)
        lm3 = λ u x y → traV ( symV (pr-x-lm2 A  b u x y)) (traV (lm2 u x y) (pr-y-lm2 A b u x y))
        lm4 : apr b (u , pj1 (apel q u)) ≐  apr b (v , ap (κ° (type A) ± t) (pj1 (apel q u)))
        lm4 = apr-ext b (u , pj1 (apel q u)) (v , ap (κ° (type A) ± t) (pj1 (apel q u)) )
              (two-var-lm A u v (pj1 (apel q u)) t)
-- now use  u ~ v
        lm :  apr b (u , pj1 (apel q u)) ≐ apr b (v , pj1 (apel q v))
        lm = traV lm4 (lm3 v (ap (κ° (type A) ± t) (pj1 (apel q u))) (pj1 (apel q v)))
  in  <<>> lm


wh-lm :  {Γ : ctx}
    -> (A B : ty Γ)
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ A ==> b :: B [[ ↓ A ]])
    -> << Raw (Γ ▷ A ▷ (A [[ ↓ A ]])) >> b [ pr-x A ] ~  (b [ pr-y A ])
    -> raw Γ
wh-lm  {Γ} A B k b q r p = mkraw (record { op = wh-lm-op {Γ} A B k b q r p
                                         ; ext = wh-lm-op-ext {Γ} A B k b q r p })

wh :  {Γ : ctx}
    -> (A B : ty Γ)
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ A ==> b :: B [[ ↓ A ]])
    -> (p : Γ ▷ A ▷ (A [[ ↓ A ]]) ==> b [ pr-x A ] ==  b [ pr-y A ] :: B  [[ ↓ A ]] [[ ↓ (A [[ ↓ A ]]) ]])
    -> raw Γ
wh {Γ} A B k b q r p = wh-lm  {Γ} A B k b q r (Raw-lm2 (prj1 p))


Br-e-lm :  {Γ : ctx}
--
    -> (A B : ty Γ)
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ A ==> b :: B [[ ↓ A ]])
    -> (p : Γ ▷ A ▷ (A [[ ↓ A ]]) ==> b [ pr-x A  ] ==  b [ pr-y A ] :: B  [[ ↓ A ]] [[ ↓ (A [[ ↓ A ]]) ]])
    -> (x : || κ Γ ||)
    -> apr (wh A B k b q r p) x ∈ apt B x
Br-e-lm {Γ} A B k b q r p x =
     let lm : apr (wh A B k b q r p) x ≐ apr b (x , pj1 (apel q x))
         lm = refV _
         lm2 : apr b (x , pj1 (apel q x))   ∈ apt B x
         lm2 = apel r (x , pj1 (apel q x))
     in memV-left-ext _ _ (apt B x) lm lm2

Br-e :  {Γ : ctx}
--
    -> (A B : ty Γ)
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ A ==> b :: B [[ ↓ A ]])
    -> (p : Γ ▷ A ▷ (A [[ ↓ A ]]) ==> b [ pr-x A  ] ==  b [ pr-y A ] :: B  [[ ↓ A ]] [[ ↓ (A [[ ↓ A ]]) ]])
-- --------------------------------
    -> Γ ==>  wh A B k b q r p :: B
Br-e {Γ} A B k b q r p = mk-elt (Br-e-lm {Γ} A B k b q r p)



Br-beta-raw-lm :  {Γ : ctx}
--
    -> (A B : ty Γ)
    -> (a : raw Γ)
    -> (b  : raw (Γ ▷ A))
    -> (t : Γ ==> a :: A)
    -> (q : Γ ==> (br a) :: Br A)
    -> (r : Γ ▷ A ==> b :: B [[ ↓ A ]])
    -> (p : Γ ▷ A ▷ (A [[ ↓ A ]]) ==> b [ pr-x A  ] ==  b [ pr-y A ] :: B  [[ ↓ A ]] [[ ↓ (A [[ ↓ A ]]) ]])
    -> (x : || κ Γ ||)
    -> (apr (wh A B (br a) b q r p)  x) ≐  (apr (b [ els t ])  x)
Br-beta-raw-lm {Γ} A B a b t q r p x =
     let lm1 : (z : || κ (Γ ▷ A ▷ (A [[ ↓ A ]])) ||) →
                      apr (b [ pr-x A ]) z ≐ apr (b [ pr-y A ]) z
         lm1 = prj1 p
         lm2 : (u : || κ Γ ||) -> (x : ||  κ (apt A u) ||) -> (y : || κ (apt A u) ||) ->
                     apr (b [ pr-x A ]) (( u , x) , y) ≐ apr (b [ pr-y A ])  (( u , x) , y)
         lm2 = λ u x y → lm1  (( u , x) , y)
         lm3 : (u : || κ Γ ||) -> (x : ||  κ (apt A u) ||) -> (y : || κ (apt A u) ||) ->
                     apr b ( u , x)  ≐ apr b (u , y)
         lm3 = λ u x y → traV ( symV (pr-x-lm2 A  b u x y)) (traV (lm2 u x y) (pr-y-lm2 A b u x y))

         main :  apr b (x , pj1 (apel q x))  ≐  apr b (x , pj1 (apel t x))  -- (apr (b [ els t ])  x)
         main = lm3 x  (pj1 (apel q x))  (pj1 (apel t x))
     in main

Br-beta-raw :  {Γ : ctx}
--
    -> (A B : ty Γ)
    -> (a : raw Γ)
    -> (b  : raw (Γ ▷ A))
    -> (t : Γ ==> a :: A)
    -> (q : Γ ==> (br a) :: Br A)
    -> (r : Γ ▷ A ==> b :: B [[ ↓ A ]])
    -> (p : Γ ▷ A ▷ (A [[ ↓ A ]]) ==> b [ pr-x A  ] ==  b [ pr-y A ] :: B  [[ ↓ A ]] [[ ↓ (A [[ ↓ A ]]) ]])
-- --------------------------------
    -> << Raw Γ >>  (wh A B (br a) b q r p) ~ (b [ els t ])
Br-beta-raw {Γ} A B a b t q r p = <<>> (<<>> (λ x → <<>> (Br-beta-raw-lm {Γ} A B a b t q r p x)))

Br-beta :  {Γ : ctx}
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
Br-beta {Γ} A B a b t q r p = pair (Raw-lm (Br-beta-raw {Γ} A B a b t q r p)) (pair (Br-e {Γ} A B (br a) b q r p )
                                              (subj-red _ _ (Br-e {Γ} A B (br a) b q r p )
                                                     (Br-beta-raw {Γ} A B a b t q r p)))




br-sb : {Γ : ctx}
    -> (A  : ty Γ)
    -> subst (Γ ▷ A)  (Γ ▷ (Br A))
br-sb {Γ} A =
  let lm = Br-intro  (A [[ ↓ A ]])  (vv A) (asm A)
    in ext (Br A ) (↓ A) (br (vv A)) lm

br-sb-lm-raw-lm : {Γ : ctx}
    -> (A B : ty Γ)
    -> (b : raw (Γ ▷ Br A))
    -> (u : || κ Γ ||)
    -> (x y : ||  κ (apt A u) ||)
    -> apr (b [ br-sb A ]) (u , x) ≐  apr (b [ br-sb A ]) (u , y)
br-sb-lm-raw-lm {Γ} A B b u x y =
    let lm2 :  < κ (Γ ▷ Br A) > aps (br-sb A) (u , x) ~  aps (br-sb A) (u , y)
        lm2 = <> (pairV-ext (refV _) (refV _))
        lm : apr b (aps (br-sb A) (u , x)) ≐  apr b (aps (br-sb A) (u , y))
        lm = apr-ext b _ _ lm2
        main :   apr (b [ br-sb A ]) (u , x) ≐  apr (b [ br-sb A ]) (u , y)
        main = lm
    in  main


br-sb-lm-raw-lm2 : {Γ : ctx}
    -> (A B : ty Γ)
    -> (b : raw (Γ ▷ Br A))
    -> (z : || κ (Γ ▷ A ▷ (A [[ ↓ A ]])) ||)
    -> apr ((b [ br-sb A ]) [ pr-x A ]) z  ≐ apr  ((b [ br-sb A ]) [ pr-y A ]) z
br-sb-lm-raw-lm2 {Γ} A B b (( u , x) , y) =
      let main :  apr ((b [ br-sb A ]) [ pr-x A ]) ((u , x) , y) ≐
                     apr ((b [ br-sb A ]) [ pr-y A ]) ((u , x) , y)
          main = traV (pr-x-lm2 A (b [ br-sb A ]) u x y)
                      (traV (br-sb-lm-raw-lm {Γ} A B b u x y) (symV (pr-y-lm2 A (b [ br-sb A ]) u x y)))
      in main


br-sb-lm-raw : {Γ : ctx}
    -> (A B : ty Γ)
    -> (b : raw (Γ ▷ Br A))
    -> << Raw (Γ ▷ A ▷ (A [[ ↓ A ]])) >> (b [ br-sb A ]) [ pr-x A ] ~ ((b [ br-sb A ]) [ pr-y A ])
br-sb-lm-raw {Γ} A B b  = Raw-lm2 (br-sb-lm-raw-lm2 {Γ} A B b )



br-sb-lm : {Γ : ctx}
    -> (A B : ty Γ)
    -> (b : raw (Γ ▷ Br A))
    -> (r : Γ ▷ (Br A) ==> b :: B [[ ↓ (Br A) ]])
    -> Γ ▷ A ▷ (A [[ ↓ A ]]) ==> (b [ br-sb A ]) [ pr-x A ] ==
             (b [ br-sb A ]) [ pr-y A ] :: (B [[ ↓ A ]]) [[ ↓ (A [[ ↓ A ]]) ]]
br-sb-lm {Γ} A B b r =
   let lm = br-sb-lm-raw {Γ} A B b
       lm2 : Γ ▷ A ==> b  [ br-sb A ] :: B [[ ↓ (Br A) ]] [ br-sb A ]
       lm2 = elt-subst ( br-sb A) r
       lm4 :  Γ ▷ A ▷ (A [[ ↓ A ]]) ==> (b [ br-sb A ]) [ pr-x A ] :: ((B [[ ↓ (Br A) ]]) [ br-sb A ])  [ pr-x A ]
       lm4 =  elt-subst (pr-x A) lm2
       lm5 :  Γ ▷ A ▷ (A [[ ↓ A ]]) ==> ((B [[ ↓ (Br A) ]]) [ br-sb A ])  [ pr-x A ] ==  (B [[ ↓ A ]]) [[ ↓ (A [[ ↓ A ]]) ]]
       lm5 = mk-eqty (λ x → <<>> (refV _))
       lm3 : Γ ▷ A ▷ (A [[ ↓ A ]]) ==> (b [ br-sb A ]) [ pr-x A ] :: (B [[ ↓ A ]]) [[ ↓ (A [[ ↓ A ]]) ]]
       lm3 = elttyeq lm4 lm5
   in pair (Raw-lm lm) (pair lm3 (subj-red _ _ lm3 lm))

Br-eta-raw-lm :  {Γ : ctx}
--
    -> (A B : ty Γ)
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ Br A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ (Br A) ==> b :: B [[ ↓ (Br A) ]])
    -> (t :  Γ ▷ A ==> b [ br-sb A ] :: B [[ ↓ A ]])
    -> (x : || κ Γ ||)
    -> apr (wh A B k (b [ br-sb A ]) q t (br-sb-lm A B b r)) x ≐
          apr (b [ els q ]) x
Br-eta-raw-lm {Γ} A B k b q r t x = refV _

Br-eta-raw :  {Γ : ctx}
--
    -> (A B : ty Γ)
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ Br A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ (Br A) ==> b :: B [[ ↓ (Br A) ]])
    -> (t :  Γ ▷ A ==> b [ br-sb A ] :: B [[ ↓ A ]])
    -> << Raw Γ >>  wh A B k (b [ br-sb A ]) q t (br-sb-lm {Γ} A B b r) ~ (b [ els q ])
Br-eta-raw  {Γ} A B k b q r t = <<>> (<<>> (λ x → <<>> (Br-eta-raw-lm {Γ} A B k b q r t x)))


Br-eta :  {Γ : ctx}
--
    -> (A B : ty Γ)
    -> (k  : raw Γ)
    -> (b : raw (Γ ▷ Br A))
    -> (q : Γ ==> k :: Br A)
    -> (r : Γ ▷ (Br A) ==> b :: B [[ ↓ (Br A) ]])
    -> (t :  Γ ▷ A ==> b [ br-sb A ] :: B [[ ↓ A ]])
-- --------------------------------
    -> Γ ==>  wh A B k (b [ br-sb A ]) q t (br-sb-lm {Γ} A B b r) == (b [ els q ]) :: B
Br-eta {Γ} A B k b q r t =
  let lm =  Br-e {Γ} A B k (b [ br-sb A ]) q t (br-sb-lm {Γ} A B b r)
      lm2 = Br-eta-raw  {Γ} A B k b q r t
  in pair (Raw-lm lm2) (pair lm (subj-red _ _ lm lm2))

Br-cong-lm : {Γ : ctx}
--
    -> (A B : ty Γ)
    -> Γ ==> A == B
    -> (x : || κ Γ ||)
    -> type (Br A) • x ≐ type (Br B) • x
Br-cong-lm {Γ} A B p x = sqV-ext (apt A x) (apt B x) (>><< (ape p x))
-- sqV-ext : (a b : V) -> a ≐ b -> sqV a ≐ sqV b
-- Br-op {Γ} A x = sqV (apt A x)
Br-cong : {Γ : ctx}
--
    -> (A B : ty Γ)
    -> Γ ==> A == B
-- -------------------
    -> Γ ==> Br A == Br B
Br-cong {Γ} A B p = mk-eqty (λ x → <<>> (Br-cong-lm {Γ} A B p x))


wh-cong-lm :  {Γ : ctx}
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
    -> << Raw Γ >> k ~ k'
    -> << Raw (Γ ▷ A) >> b ~ (b' [ subst-trp (ext-eq' {Γ} A A' Aq) ])
    -> (x  : || κ Γ ||)
    -> apr (wh A B k b q r p) x ≐ apr (wh A' B' k' b' q' r' p')  x
wh-cong-lm {Γ} A B k b q r p A' B' k' b' q' r' p' Aq Bq kq bq x =
   let
       b-eq = prj1 p' ((x ,  pj1 (apel q' x)) , ap (κ-Fam ±± ape Aq x) (pj1 (apel q x)))
       lm6 : apr b (x , pj1 (apel q x)) ≐
                apr (b' [ subst-trp (ext-eq' A A' Aq) ]) (x , pj1 (apel q x))
       lm6 = Raw-lm bq (x ,  pj1 (apel q x))
       lm9 = ext-eq-lm A A' Aq x (pj1 (apel q x))
       lm8 : apr (b' [ pr-y A' ])
                ((x , pj1 (apel q' x)) , ap (κ-Fam ±± ape Aq x) (pj1 (apel q x)))
                     ≐
             apr b' (aps (subst-trp (ext-eq' A A' Aq)) (x , pj1 (apel q x)))
       lm8 = traV (pr-y-lm2 A' b' x (pj1 (apel q' x)) (ap (κ-Fam ±± ape Aq x) (pj1 (apel q x)))) (symV (apr-ext b' _ _ lm9))

       lm7 : apr (b' [ subst-trp (ext-eq' A A' Aq) ]) (x , pj1 (apel q x))
                 ≐ apr b' (x , pj1 (apel q' x))
       lm7 = traV (sub-apply b' (subst-trp (ext-eq' A A' Aq)) (x , pj1 (apel q x))) (symV (traV b-eq lm8))


       lm : apr b (x , pj1 (apel q x)) ≐  apr b' (x , pj1 (apel q' x))
       lm = traV lm6 lm7
   in lm



wh-cong :  {Γ : ctx}
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
    -> << Raw Γ >> k ~ k'
    -> << Raw (Γ ▷ A) >> b ~ (b' [ subst-trp (ext-eq' {Γ} A A' Aq) ])
-- --------------------------------
    -> << Raw Γ >>  wh A B k b q r p ~  wh A' B' k' b' q' r' p'
wh-cong {Γ} A B k b q r p A' B' k' b' q' r' p' Aq Bq kq bq  =
     <<>> (<<>> (λ x → <<>> (wh-cong-lm {Γ} A B k b q r p A' B' k' b' q' r' p' Aq Bq kq bq x)))


Br-e-cong :  {Γ : ctx}
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
Br-e-cong {Γ} A B k b q r p A' B' k' b' q' r' p' Aq Bq kq bq =
   let lm = wh-cong {Γ} A B k b q r p A' B' k' b' q' r' p' Aq Bq (Raw-lm2 (prj1 kq)) (Raw-lm2 (prj1 bq))
       lm2 = Br-e A B k b q r p
   in pair (Raw-lm lm) (pair lm2 (subj-red _ _ lm2 lm))

-- to do :  wh-sub

Br-e-sub-raw-lm :  {Δ Γ : ctx}
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
    -> (z : || κ Δ ||)
    -> apr ((wh A B k b q r p) [ h ]) z ≐ apr  (wh (A [[ h ]]) (B [[ h ]]) (k [ h ]) (b [[ (↑ A h) ]]) q' r' p') z
Br-e-sub-raw-lm {Δ} {Γ} h A B k b q r p q' r' p' z =
  let
      lm1 : (z : || κ (Γ ▷ A ▷ (A [[ ↓ A ]])) ||) →
                      apr (b [ pr-x A ]) z ≐ apr (b [ pr-y A ]) z
      lm1 = prj1 p
      lm2 : (u : || κ Γ ||) -> (x : ||  κ (apt A u) ||) -> (y : || κ (apt A u) ||) ->
                     apr (b [ pr-x A ]) (( u , x) , y) ≐ apr (b [ pr-y A ])  (( u , x) , y)
      lm2 = λ u x y → lm1  (( u , x) , y)
      lm3 : (u : || κ Γ ||) -> (x : ||  κ (apt A u) ||) -> (y : || κ (apt A u) ||) ->
                     apr b ( u , x)  ≐ apr b (u , y)
      lm3 = λ u x y → traV ( symV (pr-x-lm2 A  b u x y)) (traV (lm2 u x y) (pr-y-lm2 A b u x y))
      lm : apr b ((aps h z) , pj1 (apel q  (aps h z))) ≐
           apr (b [[ ↑ A h ]]) (z , pj1 (apel q' z))
      lm = symV (traV (b-up-lm h A b z (pj1 (apel q' z)))  (lm3 (aps h z) (pj1 (apel q' z)) (pj1 (apel q (aps h z)))))
      main : apr (wh A B k b q r p) (aps h z) ≐
             apr (wh (A [[ h ]]) (B [[ h ]]) (k [ h ]) (b [[ ↑ A h ]]) q' r' p') z
      main = lm

  in traV (sub-apply (wh A B k b q r p) h z) main


Br-e-sub-raw :  {Δ Γ : ctx}
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
    -> << Raw Δ >> (wh A B k b q r p) [ h ] ~ (wh (A [[ h ]]) (B [[ h ]]) (k [ h ]) (b [[ (↑ A h) ]]) q' r' p')
Br-e-sub-raw {Δ} {Γ} h A B k b q r p q' r' p' = Raw-lm2 (Br-e-sub-raw-lm {Δ} {Γ} h A B k b q r p q' r' p')

Br-e-sub :  {Δ Γ : ctx}
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
Br-e-sub {Δ} {Γ} h A B k b q r p  q' r' p' =
  let lm : Δ ==>  (wh A B k b q r p) [ h ] :: B [[ h ]]
      lm = elt-subst h (Br-e {Γ} A B k b q r p)
      lm2 = Br-e-sub-raw {Δ} {Γ} h A B k b q r p q' r' p'
  in pair (Raw-lm lm2) (pair lm (subj-red _ _ lm lm2))


-- closure under bracket types

U-br- :   (k : N) -> {Γ : ctx}
--
    ->  (A : ty Γ)
    ->  (q : Γ  ==> A :: U- k Γ)
-- --------------------------------------------
    ->  Γ ==> Br A :: U- k Γ
--
U-br- k {Γ} A q = mk-elt (λ x → sqV-reflection (I- k) (F- k) (apt A x) (apel q x))


-- end of Br

