-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt9 where

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
                     -- this file  441 lines
                     -- total     6859 lines

Σ-f :  {Γ : ctx}
--
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
--     ---------------------------------------
       -> ty Γ
--
Σ-f A B = ty.tyy (comp01 sigmaVV (mk-Par A  B))


Σ-f-exp1 :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       ->  (apt (Σ-f A B)  u) ≐ sigmaV (apt A u) (mk-Par-op-Fx A B u)
Σ-f-exp1 A B u = refV _

-- sigmaV : (a : V) -> (g :  setoidmap1 (κ a) VV) -> V
-- sigmaV a g =  sup (Σ (# a) (\y -> # (g • y)))
--                     (\u -> < a ‣ (pj1 u) , (g • (pj1 u)) ‣ (pj2 u) >)

-- Move to iterative-sets-pt2.agda:

sigmaV-iV : (a : V) -> (g :  setoidmap1 (κ a) VV) -> Set
sigmaV-iV a g = Σ (# a) (\y -> # (g • y))

sigmaV-bV : (a : V) -> (g :  setoidmap1 (κ a) VV) ->  sigmaV-iV a g -> V
sigmaV-bV a g u =  < a ‣ (pj1 u) , (g • (pj1 u)) ‣ (pj2 u) >

Σ-f-exp2 :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       ->  (apt (Σ-f A B)  u) ≐ sup (sigmaV-iV (apt A u) (mk-Par-op-Fx A B u))
                                    (sigmaV-bV (apt A u) (mk-Par-op-Fx A B u))
Σ-f-exp2 A B u = refV _

Σ-f-exp3 :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (x : || κ Γ ||)
       -> (u : # (apt (Σ-f {Γ} A B)  x))
       -> (apt (Σ-f {Γ} A B)  x) ‣ u ≐  < (apt A x) ‣ (pj1 u) , (apt B  (x , (pj1  u))) ‣ (pj2 u) >
Σ-f-exp3  A B x u = refV _



Σ-f-cong : {Γ : ctx}
--
      -> (A  A' : ty Γ)
      -> (p : Γ ==> A == A')
      -> (B : ty (Γ ▷ A))
      -> (B' : ty (Γ ▷ A'))
      -> (Γ ▷ A ==> B == (B' [[  subst-trp (ext-eq' A A' p) ]]))
-- ---------------------
      -> Γ ==> Σ-f A B == Σ-f A' B'
Σ-f-cong {Γ} A A' p B B' q  = mk-eqty (λ x → let lm = mk-Par-cong  {Γ} A A' p B B' q x
                                              in extensionality11 sigmaVV (ap1 (mk-Par A B) x) (ap1 (mk-Par  A' B') x) lm)

pr-op : {Γ : ctx}
--
      -> (a  : raw Γ)
      -> (b : raw Γ)
      -> (|| κ Γ || -> V)
pr-op {Γ} a b x =  < apr a x , apr b x >


pr : {Γ : ctx}
--
      -> (a  : raw Γ)
      -> (b : raw Γ)
      -> raw Γ
pr {Γ} a b = mkraw (record { op = pr-op {Γ} a b
                           ; ext = λ x y p → <<>> (pairV-ext (>><< (extensionality1 (raw.rawterm a) x y p))
                                                       (>><< (extensionality1 (raw.rawterm b) x y p)))
                           })



pr-cong' : {Γ : ctx}
--
      -> (a a'  : raw Γ)
      -> (b b' : raw Γ)
      -> << Raw Γ >> a ~ a'
      -> << Raw Γ >> b ~ b'
      -> << Raw Γ >> pr a b ~ pr a' b'
pr-cong' a a' b b' p q  = Raw-lm2 (\x -> pairV-ext (Raw-lm p x) (Raw-lm q x))


Σ-i : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (a  : raw Γ)
      -> (p : Γ ==> a :: A)
      -> (b : raw Γ)
      -> (Γ ==> b :: (B [[ els p ]]))
      -> Γ ==> pr a b :: Σ-f A B
Σ-i {Γ} A B a p b q = mk-elt (λ x → ((pj1 (apel p x)) , (pj1 (apel q x))) , pairV-ext (pj2 (apel p x)) (pj2 (apel q x)))


pr-cong : {Γ : ctx}
--
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (a a'  : raw Γ)
      -> (b b' : raw Γ)
      -> (p : Γ ==> a :: A)
      -> (Γ ==> a == a' :: A)
      -> (Γ ==> b == b' :: (B [[ els p ]]))
      -> Γ ==> pr a b == pr a' b' :: Σ-f A B

pr-cong {Γ} A B a a' b b' p q1 q2  =
   let --  r' = Σ-e-1 A B c' p'
        -- lm = Σ-e-2 {Γ} A B c' p' r'
        lm2 : < Subst Γ (Γ ▷ A) >  els p ~ els (prj2 (prj2 q1))
        lm2 = els-cong p (prj2 (prj2 q1)) q1 -- els-cong (Σ-e-1 A B c' p') r (pr1-cong A B c' c p' p (tmsym (Σ-f A B) _ _ q ))
        lm3 :  Γ ==>  B [[ els p ]] == B [[ els (prj2 (prj2 q1)) ]]
        lm3 = tyeq-subst2 B _ _ lm2
        lm4 : Γ ==> b' :: B [[ els (prj2 (prj2 q1)) ]]
        lm4 = elttyeq (prj2 (prj2 q2)) lm3

   in  elteq-from-eq (Σ-f A B) (pr a b) (pr a' b')
                (Σ-i {Γ} A B a p b (prj1 (prj2 q2)))
                (Σ-i {Γ} A B a' (prj2 (prj2 q1)) b' lm4)
                (pr-cong' a a' b b' (eq-from-elteq A a a' q1) (eq-from-elteq (B [[ els p ]]) b b' q2) )

{--




eq-from-elteq : {Γ : ctx} -> (A : ty Γ) ->  (a b : raw Γ)
      -> Γ ==> a == b :: A
--   -------------------------
     ->  << Raw Γ >> a ~ b

elteq-from-eq : {Γ : ctx} -> (A : ty Γ) ->  (a b : raw Γ)
     -> Γ ==> a :: A   -> Γ ==> b :: A   ->  << Raw Γ >> a ~ b
--   -------------------------
     -> Γ ==> a == b :: A
elteq-from-eq A a b p q r =  pair (λ x → >><< (>><< (>><< r) x))
                                  (pair p q)

pr1-cong' : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c c'  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (p' : Γ ==> c' :: Σ-f A B)
      -> << Raw Γ >>  c ~ c'
      -> << Raw Γ >> pr1 {Γ} A B c p ~  pr1 {Γ} A B c' p'

--}

-- see iterative-sets-pt2.agd

pr1-op : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (Γ ==> c :: Σ-f A B)
      -> (|| κ Γ || -> V)
pr1-op {Γ} A B c p x =  apt A x  ‣ pj1 (pj1 (apel p x))

-- pj1-sigmaV-op : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
--             ||  κ (sigmaV a g) || -> V
-- pj1-sigmaV-op a g u = a ‣ (pj1 u)

-- pj1-sigmaV : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
--             setoidmap1 (κ (sigmaV a g)) VV

pr1-ext  : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (x y : || κ Γ ||)
      -> (q : < κ Γ > x ~ y)
      -> << VV >> pr1-op A B c p x ~ pr1-op A B c p y
pr1-ext {Γ} A B c p x y q =  -- extensionality1 ((raw.rawterm c)) x y q
       let lm2 = pj2 (apel p x)
           lm4 = pj2 (apel p y)
           eq : apr c x ≐ apr c y
           eq = >><< (extensionality1 (raw.rawterm c) x y q)
           eq2 : apt (Σ-f A B) x ‣ pj1 (apel p x) ≐ apt (Σ-f A B) y ‣ pj1 (apel p y)
           eq2 = traV (symV lm2) (traV eq lm4)
           eq3 : < (apt A x) ‣ (pj1 (pj1 (apel p x))) , (apt B  (x , (pj1  (pj1 (apel p x))))) ‣ (pj2 (pj1 (apel p x))) >
               ≐ < (apt A y) ‣ (pj1 (pj1 (apel p y))) , (apt B  (y , (pj1  (pj1 (apel p y))))) ‣ (pj2 (pj1 (apel p y))) >
           eq3 = traV (symV (Σ-f-exp3 A B x (pj1 (apel p x)))) (traV eq2 (Σ-f-exp3 A B y (pj1 (apel p y))))


           main : apt A x  ‣ pj1 (pj1 (apel p x)) ≐  apt A y  ‣ pj1 (pj1 (apel p y))
           main = prj1 (pairV-inv-1 eq3)
       in <<>> main


pr1 : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (Γ ==> c :: Σ-f A B)
      -> raw Γ
pr1 {Γ} A B c p = mkraw (record { op = pr1-op {Γ} A B c p
                                ; ext = pr1-ext {Γ} A B c p })

pr1-cong' : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c c'  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (p' : Γ ==> c' :: Σ-f A B)
      -> << Raw Γ >>  c ~ c'
      -> << Raw Γ >> pr1 {Γ} A B c p ~  pr1 {Γ} A B c' p'
pr1-cong' {Γ} A B c c' p p' q = Raw-lm2 {Γ}
   (\ x ->
   let lm1 : apt (Σ-f A B) x ‣ pj1 (apel p x) ≐
               < apt A x ‣ pj1 (pj1 (apel p x)) ,  apt B (x , pj1 (pj1 (apel p x))) ‣ pj2 (pj1 (apel p x)) >
       lm1 = Σ-f-exp3 A B x (pj1 (apel p x))
       lm2 = pj2 (apel p x)
       lm3 : apt (Σ-f A B) x ‣ pj1 (apel p' x) ≐
               < apt A x ‣ pj1 (pj1 (apel p' x)) ,  apt B (x , pj1 (pj1 (apel p' x))) ‣ pj2 (pj1 (apel p' x)) >
       lm3 = Σ-f-exp3 A B x (pj1 (apel p' x))
       lm4 = pj2 (apel p' x)
       lm5 : apr c x ≐ apr c' x
       lm5 = (Raw-lm q) x
       lm6 :  < apt A x ‣ pj1 (pj1 (apel p x)) ,  apt B (x , pj1 (pj1 (apel p x))) ‣ pj2 (pj1 (apel p x)) >
             ≐ < apt A x ‣ pj1 (pj1 (apel p' x)) ,  apt B (x , pj1 (pj1 (apel p' x))) ‣ pj2 (pj1 (apel p' x)) >
       lm6 = traV (symV lm1) (traV (traV (symV  lm2) (traV lm5 lm4)) lm3)
       main :   (apr (pr1 A B c p)  x) ≐ (apr (pr1 A B c' p')  x)

       main =  prj1 (pairV-inv-1 lm6)
   in main)




Σ-e-1 : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> Γ ==> pr1 A B c p :: A

Σ-e-1 {Γ} A B c p = mk-elt (λ x → (pj1 (pj1 (apel p x))) , (refV _))




pr1-cong : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c c'  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (p' : Γ ==> c' :: Σ-f A B)
      -> (Γ ==> c == c' :: Σ-f A B)
      -> Γ ==> pr1 {Γ} A B c p ==  pr1 {Γ} A B c' p' :: A
pr1-cong {Γ} A B c c' p p' q =
   elteq-from-eq A (pr1 {Γ} A B c p) (pr1 {Γ} A B c' p') (Σ-e-1 {Γ} A B c p) (Σ-e-1 {Γ} A B c' p')
             (pr1-cong' A B c c' p p' (<<>> (<<>> (λ x → <<>> (prj1 q x)))))


pr2-op : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (Γ ==> c :: Σ-f A B)
      -> (|| κ Γ || -> V)
pr2-op {Γ} A B c p x = (apt B (x , pj1 (pj1 (apel p x)))) ‣ pj2 (pj1 (apel p x))



pr2-ext  : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (x y : || κ Γ ||)
      -> (q : < κ Γ > x ~ y)
      -> << VV >> pr2-op A B c p x ~ pr2-op A B c p y
pr2-ext {Γ} A B c p x y q =
   let     lm2 = pj2 (apel p x)
           lm4 = pj2 (apel p y)
           eq : apr c x ≐ apr c y
           eq = >><< (extensionality1 (raw.rawterm c) x y q)
           eq2 : apt (Σ-f A B) x ‣ pj1 (apel p x) ≐ apt (Σ-f A B) y ‣ pj1 (apel p y)
           eq2 = traV (symV lm2) (traV eq lm4)
           eq3 : < (apt A x) ‣ (pj1 (pj1 (apel p x))) , (apt B  (x , (pj1  (pj1 (apel p x))))) ‣ (pj2 (pj1 (apel p x))) >
               ≐ < (apt A y) ‣ (pj1 (pj1 (apel p y))) , (apt B  (y , (pj1  (pj1 (apel p y))))) ‣ (pj2 (pj1 (apel p y))) >
           eq3 = traV (symV (Σ-f-exp3 A B x (pj1 (apel p x)))) (traV eq2 (Σ-f-exp3 A B y (pj1 (apel p y))))


           main : (apt B (x , pj1 (pj1 (apel p x)))) ‣ pj2 (pj1 (apel p x)) ≐ (apt B (y , pj1 (pj1 (apel p y)))) ‣ pj2 (pj1 (apel p y))
           main = prj2 (pairV-inv-1 eq3)
   in <<>> main



pr2 : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (Γ ==> c :: Σ-f A B)
      -> raw Γ
pr2 {Γ} A B c p = mkraw (record { op = pr2-op {Γ} A B c p
                                ; ext = pr2-ext {Γ} A B c p })



Σ-e-2-lm : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (q : Γ ==> pr1 A B c p :: A)
      -> (x : || κ Γ ||)
      -> apr (pr2 A B c p) x ∈ apt (B [[ els q ]]) x
Σ-e-2-lm {Γ} A B c p q x =
   let lm : apt (Σ-f A B) x ‣ pj1 (apel p x) ≐
               < apt A x ‣ pj1 (pj1 (apel p x)) ,  apt B (x , pj1 (pj1 (apel p x))) ‣ pj2 (pj1 (apel p x)) >
       lm = Σ-f-exp3 A B x (pj1 (apel p x))
       lm2 : < apt A x ‣ pj1 (pj1 (apel p x)) ,  apt B (x , pj1 (pj1 (apel p x))) ‣ pj2 (pj1 (apel p x)) >
             ∈ sigmaV (apt A x) (mk-Par-op-Fx A B x)
       lm2 = memV-right-ext _ _ _ (pj1 (apel p x) , (symV lm)) (symV (Σ-f-exp1 {Γ} A B x))
       lm3 = sigmaV-lm (apt A x) (mk-Par-op-Fx A B x) _ _ lm2
       q2 = pj1 lm3
       pq1 = pj1 (apel q x)
       pq2 = pj2 (apel q x)

       lm4 :  apt B (x , pj1 (pj1 (apel p x))) ‣ pj2 (pj1 (apel p x)) ∈
                      mk-Par-op-Fx A B x • pj1 q2
       lm4 = pj2 lm3
       eq1 : Γ ‣ x ≐ Γ ‣ aps (ids {Γ}) x
       eq1 = refV _
       eq3 :  (ty.type A • x)  ≐  (ty.type A • aps  (ids {Γ}) x)
       eq3 = refV _
       eq2 :  (ty.type A • x) ‣ pj1 (pj1 (apel p x)) ≐  (ty.type A • aps  (ids {Γ}) x) ‣ pj1 (apel q x)
       eq2 = pq2

       eq :  < κ (Γ ▷ A) > x , pj1 (pj1 (apel p x)) ~  ap (subst.cmap (els q)) x
       eq = <> (pairV-ext eq1 eq2)
       lm5 :  mk-Par-op-Fx A B x • pj1 q2 ≐ apt (B [[ els q ]]) x
       lm5 = >><< (extensionality1 (ty.type B) ( x , pj1 (pj1 (apel p x))) ( ap (subst.cmap (els q)) x) eq)
       main : apr (pr2 A B c p) x ∈ apt (B [[ els q ]]) x
       main = memV-right-ext _ _ _ lm4 lm5
   in main




pr2-cong' : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c c'  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (p' : Γ ==> c' :: Σ-f A B)
      -> << Raw Γ >>  c ~ c'
      -> << Raw Γ >> pr2 {Γ} A B c p ~  pr2 {Γ} A B c' p'
pr2-cong' {Γ} A B c c' p p' q = Raw-lm2 {Γ}
   (\x ->
   let lm1 : apt (Σ-f A B) x ‣ pj1 (apel p x) ≐
               < apt A x ‣ pj1 (pj1 (apel p x)) ,  apt B (x , pj1 (pj1 (apel p x))) ‣ pj2 (pj1 (apel p x)) >
       lm1 = Σ-f-exp3 A B x (pj1 (apel p x))
       lm2 = pj2 (apel p x)
       lm3 : apt (Σ-f A B) x ‣ pj1 (apel p' x) ≐
               < apt A x ‣ pj1 (pj1 (apel p' x)) ,  apt B (x , pj1 (pj1 (apel p' x))) ‣ pj2 (pj1 (apel p' x)) >
       lm3 = Σ-f-exp3 A B x (pj1 (apel p' x))
       lm4 = pj2 (apel p' x)
       lm5 : apr c x ≐ apr c' x
       lm5 = (Raw-lm q) x
       lm6 :  < apt A x ‣ pj1 (pj1 (apel p x)) ,  apt B (x , pj1 (pj1 (apel p x))) ‣ pj2 (pj1 (apel p x)) >
             ≐ < apt A x ‣ pj1 (pj1 (apel p' x)) ,  apt B (x , pj1 (pj1 (apel p' x))) ‣ pj2 (pj1 (apel p' x)) >
       lm6 = traV (symV lm1) (traV (traV (symV  lm2) (traV lm5 lm4)) lm3)
       main :  (apr (pr2 A B c p)  x) ≐ (apr (pr2 A B c' p')  x)

       main =  prj2 (pairV-inv-1 lm6)
   in main)


Σ-e-2 : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (q : Γ ==> pr1 A B c p :: A)
      -> Γ ==> pr2 A B c p :: B [[ els q ]]
Σ-e-2 {Γ} A B c p q = mk-elt (Σ-e-2-lm {Γ} A B c p q)


pr2-cong : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c c'  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (p' : Γ ==> c' :: Σ-f A B)
      -> (Γ ==> c == c' :: Σ-f A B)
      -> (r : Γ ==> pr1 {Γ} A B c p :: A)
      -> Γ ==> pr2 {Γ} A B c p ==  pr2{Γ} A B c' p' :: B [[ els r ]]
pr2-cong {Γ} A B c c' p p' q r =
    let r' = Σ-e-1 A B c' p'
        lm = Σ-e-2 {Γ} A B c' p' r'
        lm2 : < Subst Γ (Γ ▷ A) > els (Σ-e-1 A B c' p') ~ els r
        lm2 = els-cong (Σ-e-1 A B c' p') r (pr1-cong A B c' c p' p (tmsym (Σ-f A B) _ _ q ))
        lm3 :  Γ ==> B [[ els (Σ-e-1 A B c' p') ]] == B [[ els r ]]
        lm3 = tyeq-subst2 B _ _ lm2

    in      elteq-from-eq (B [[ els r ]]) (pr2 {Γ} A B c p) (pr2 {Γ} A B c' p')
               (Σ-e-2 {Γ} A B c p r) (elttyeq lm lm3)  (pr2-cong' A B c c' p p' (<<>> (<<>> (λ x → <<>> (prj1 q x)))))

--   elteq-from-eq A (pr1 {Γ} A B c p) (pr1 {Γ} A B c' p') (Σ-e-1 {Γ} A B c p) (Σ-e-1 {Γ} A B c' p')
--             (pr1-cong' A B c c' p p' (<<>> (<<>> (λ x → <<>> (prj1 q x)))))

{--

pr1-cong : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c c'  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (p' : Γ ==> c' :: Σ-f A B)
      -> (Γ ==> c == c' :: Σ-f A B)
      -> Γ ==> pr1 {Γ} A B c p ==  pr1 {Γ} A B c' p' :: A

tyeq-subst2 :  {Δ Γ : ctx} -> (A : ty Γ) -> (f g : subst Δ Γ)
--
                  -> < Subst Δ Γ > f ~ g
--      --------------------------------------------------
         -> Δ ==> A [[ f ]] ==  A [[ g ]]

els-cong :   {Γ : ctx}
    -> {A : ty Γ}
    -> {a a' : raw Γ}
    -> (p : Γ ==> a :: A)
    -> (q : Γ ==> a' :: A)
    -> (Γ ==> a == a' :: A)
    -> < Subst Γ (Γ ▷ A) > els p ~ els q



--}

Σ-c-1-raw : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (a  : raw Γ)
      -> (p : Γ ==> a :: A)
      -> (b : raw Γ)
      -> (Γ ==> b :: (B [[ els p ]]))
      -> (q : Γ ==> pr a b :: Σ-f A B)
      -> (x : || κ Γ ||)
      -> apr (pr1 A B (pr a b) q) x ≐ apr a x
Σ-c-1-raw {Γ} A B a p b r q x =
    let   lm : apt (Σ-f A B) x ‣ pj1 (apel q x) ≐
                 < apt A x ‣ pj1 (pj1 (apel q x)) ,  apt B (x , pj1 (pj1 (apel q x))) ‣ pj2 (pj1 (apel q x)) >
          lm = Σ-f-exp3 A B x (pj1 (apel q x))
          lm2 = pj2 (apel q x)
          lm3 :  apr (pr a b) x ≐
                 < apt A x ‣ pj1 (pj1 (apel q x)) ,  apt B (x , pj1 (pj1 (apel q x))) ‣ pj2 (pj1 (apel q x)) >
          lm3 = traV lm2 lm
          lm4 = pairV-inv-1 lm3
          main :  apr (pr1 A B (pr a b) q) x ≐ apr a x
          main = symV (prj1 lm4)
    in main



Σ-c-1 : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (a  : raw Γ)
      -> (p : Γ ==> a :: A)
      -> (b : raw Γ)
      -> (Γ ==> b :: (B [[ els p ]]))
      -> (q : Γ ==> pr a b :: Σ-f A B)
      -> Γ ==> pr1 A B (pr a b) q == a :: A
Σ-c-1 {Γ} A B a p b r q =  pair (Σ-c-1-raw {Γ} A B a p b r q) (pair (Σ-e-1 {Γ} A B (pr a b) q) p)



Σ-c-2-raw : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (a  : raw Γ)
      -> (p : Γ ==> a :: A)
      -> (b : raw Γ)
      -> (Γ ==> b :: (B [[ els p ]]))
      -> (q : Γ ==> pr a b :: Σ-f A B)
      -> (x : || κ Γ ||)
      -> apr (pr2 A B (pr a b) q) x ≐ apr b x
Σ-c-2-raw {Γ} A B a p b r q x  =
  let     lm : apt (Σ-f A B) x ‣ pj1 (apel q x) ≐
                 < apt A x ‣ pj1 (pj1 (apel q x)) ,  apt B (x , pj1 (pj1 (apel q x))) ‣ pj2 (pj1 (apel q x)) >
          lm = Σ-f-exp3 A B x (pj1 (apel q x))
          lm2 = pj2 (apel q x)
          lm3 :  apr (pr a b) x ≐
                 < apt A x ‣ pj1 (pj1 (apel q x)) ,  apt B (x , pj1 (pj1 (apel q x))) ‣ pj2 (pj1 (apel q x)) >
          lm3 = traV lm2 lm
          lm4 = pairV-inv-1 lm3
          main :  apr (pr2 A B (pr a b) q) x ≐ apr b x
          main = symV (prj2 lm4)
    in main




Σ-c-2 : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (a  : raw Γ)
      -> (p : Γ ==> a :: A)
      -> (b : raw Γ)
      -> (Γ ==> b :: (B [[ els p ]]))
      -> (q : Γ ==> pr a b :: Σ-f A B)
      ->  Γ ==> pr2 A B (pr a b) q == b  :: (B [[ els p ]])
Σ-c-2 {Γ} A B a p b r q = pair (Σ-c-2-raw {Γ} A B a p b r q)
                               (pair (subj-red {Γ} {B [[ els p ]]}
                                               b (pr2 A B (pr a b) q) r
                                               (sym' (Raw-lm2 (Σ-c-2-raw {Γ} A B a p b r q)))) r)





Σ-c-eta-raw : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (x : || κ Γ ||)
      -> apr c x ≐ apr (pr (pr1 A B c p) (pr2 A B c p)) x
Σ-c-eta-raw {Γ} A B c p x =
   let lm : apt (Σ-f A B) x ‣ pj1 (apel p x) ≐
               < apt A x ‣ pj1 (pj1 (apel p x)) ,  apt B (x , pj1 (pj1 (apel p x))) ‣ pj2 (pj1 (apel p x)) >
       lm = Σ-f-exp3 A B x (pj1 (apel p x))
       lm2 = pj2 (apel p x)
       main : apr c x ≐ apr (pr (pr1 A B c p) (pr2 A B c p)) x
       main = traV lm2 (traV lm (pairV-ext (refV _) (refV _)))
   in main




Σ-c-eta : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      ->  Γ ==> c == pr (pr1 A B c p) (pr2 A B c p) :: Σ-f A B
Σ-c-eta {Γ} A B c p = pair (Σ-c-eta-raw {Γ} A B c p)
                           (pair p
                                (Σ-i {Γ} A B (pr1 A B c p) (Σ-e-1 {Γ} A B c p)
                                             (pr2 A B c p) (Σ-e-2 {Γ} A B c p (Σ-e-1 {Γ} A B c p))))


-- substituting into a Pi-type

Σ-f-sub :  {Δ Γ : ctx}
--
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))  -> (h : subst Δ Γ)
--     ---------------------------------------
       -> Δ ==>  (Σ-f A B) [[ h ]] ==  Σ-f (A [[ h ]]) (B [[ ↑ A h ]])
Σ-f-sub {Δ} {Γ} A B h = mk-eqty (\u ->
    let lm :  << VV >> ap11 sigmaVV (ap1 (mk-Par A B) (aps h u)) ~
                      ap11 sigmaVV (ap1 (mk-Par (A [[ h ]]) (B [[ ↑ A h ]]) ) u)
        lm = extensionality11 sigmaVV
                              (ap1 (mk-Par A B) (aps h u))
                              (ap1 (mk-Par (A [[ h ]]) (B [[ ↑ A h ]])) u)
                              (mk-Par-sub {Δ} {Γ} A B h u)
    in lm)



-- move to pt1

els-lm : {Γ : ctx}
--
       -> (A : ty Γ)
       -> (a   : raw Γ)
       -> (p : Γ ==> a :: A)
       -> (x : || κ Γ ||)
       -> < κ (Γ ▷ A) > aps (els p) x  ~ (x , pj1 (apel p x))
els-lm {Γ} A a p x = refl (κ (Γ ▷ A)) (aps (els p) x)

{--
qq-eq :  {Δ Γ : ctx}
       -> (A : ty Γ)    -> (h : subst Δ Γ)
       -> (x : # Δ)
       -> (y : # (apt (A [[ h ]]) x))
       -> < κ (Γ ▷ A) > aps (↑ A h) (x , y) ~ (aps h x , y)
--}

els-h-sub-lm :  {Δ Γ : ctx}
--
       -> (A : ty Γ)
       -> (a   : raw Γ)
       -> (p : Γ ==> a :: A)
       -> (h : subst Δ Γ)
       -> (x : || κ Δ ||)
       -> < κ (Γ ▷ A) >  ap (subst.cmap (els p ⌢ h)) x  ~
                         ap (subst.cmap (↑ A h ⌢ els (elt-subst h p))) x
els-h-sub-lm {Δ} {Γ} A a p h x =
      let  lm1 : < κ (Γ ▷ A) >  ap (subst.cmap (els p ⌢ h)) x  ~ aps (els p) (aps h x)
           lm1 = refl (κ (Γ ▷ A)) (aps (els p) (aps h x))
           lm2 : < κ (Γ ▷ A) >  ap (subst.cmap (↑ A h ⌢ els (elt-subst h p))) x  ~ aps (↑ A h) (aps (els (elt-subst h p)) x)
           lm2 =  refl (κ (Γ ▷ A)) (aps (↑ A h) (aps (els (elt-subst h p)) x))
           lm3 :  < κ (Γ ▷ A) > aps (els p) (aps h x) ~  ((aps h x) , pj1 (apel p (aps h x)))
           lm3 = els-lm {Γ} A a p (aps h x)
           lm4 :  < κ (Δ ▷ (A [[ h ]])) > (aps (els (elt-subst h p)) x)  ~ ( x , pj1 (apel (elt-subst h p) x))
           lm4 = els-lm {Δ} (A [[ h ]]) (a [ h ] ) (elt-subst h p) x
           lm4b : < κ (Γ ▷ A) > aps (↑ A h) (x , pj1 (apel (elt-subst h p) x)) ~  aps (↑ A h) (aps (els (elt-subst h p)) x)
           lm4b = aps-ext (↑ A h) _ _ lm4
           lm5 :  < κ (Γ ▷ A) > aps (↑ A h) (x ,  pj1 (apel (elt-subst h p) x)) ~ (aps h x , pj1 (apel (elt-subst h p) x))
           lm5 = qq-eq A h x (pj1 (apel (elt-subst h p) x))
           lm6 :  < κ (Γ ▷ A) >  ((aps h x) , pj1 (apel p (aps h x))) ~ (aps h x , pj1 (apel (elt-subst h p) x))
           lm6 = <> (pairV-ext (refV _) (refV _))
           lm7 :  < κ (Γ ▷ A) > aps (els p) (aps h x) ~ aps (↑ A h) (aps (els (elt-subst h p)) x)
           lm7 = tra lm3 (tra lm6 (tra (sym lm5) lm4b))

      in tra lm1 (tra lm7 (sym lm2))

  --   pairV-ext {!!} {!!}


{--

qq-eq :  {Δ Γ : ctx}
       -> (A : ty Γ)    -> (h : subst Δ Γ)
       -> (x : # Δ)
       -> (y : # (apt (A [[ h ]]) x))
       -> < κ (Γ ▷ A) > aps (↑ A h) (x , y) ~ (aps h x , y)

_⌢_ : {Θ Δ Γ : ctx} -> (f : subst Δ Γ) -> (g : subst Θ Δ) -> (subst Θ Γ)
f ⌢ g = sb (subst.cmap f ° subst.cmap g)
--}

els-h-sub :  {Δ Γ : ctx}
--
       -> (A : ty Γ)
       -> (a   : raw Γ)
       -> (p : Γ ==> a :: A)
       -> (h : subst Δ Γ)
-- ---------------------------------------------------------------
       -> < Subst Δ (Γ ▷ A) > ((els p) ⌢ h)  ~  (( ↑ A h) ⌢ (els (elt-subst h p)))
els-h-sub {Δ} {Γ} A a p h = <> (<> (λ x → (els-h-sub-lm {Δ} {Γ} A a p h x)))

B-els-h-sub :  {Δ Γ : ctx}
--
       -> (A : ty Γ)
       -> (B : ty (Γ ▷ A))
       -> (a   : raw Γ)
       -> (p : Γ ==> a :: A)
       -> (h : subst Δ Γ)
-- ---------------------------------------------------------------
       ->  Δ ==> (B [[ els p ]] [[ h ]]) == (B [[ ↑ A h ]] [[ els (elt-subst h p) ]])
--
B-els-h-sub {Δ} {Γ} A B a p h =
     let lm1 : Δ ==> (B [[ els p ]] [[ h ]]) == (B [[ (els p) ⌢ h ]])
         lm1 = tysym (tysubst-com  B (els p) h)
         lm2 : Δ ==>  (B [[ ↑ A h ]] [[ els (elt-subst h p) ]]) ==  (B [[ ( ↑ A h) ⌢ (els (elt-subst h p)) ]])
         lm2 = tysym (tysubst-com B (↑ A h) (els (elt-subst h p)))
         lm4 : Δ ==> (B [[ (els p) ⌢ h ]]) == (B [[ ( ↑ A h) ⌢ (els (elt-subst h p)) ]])
         lm4 = tyeq-subst2 B _ _ (els-h-sub {Δ} {Γ} A a p h)
      in  tytra lm1 (tytra lm4 (tysym lm2))

{--
e+prop : {u v : V} -> (p : u ≐ v)
      -> (x : # u) -> u ‣ x ≐ v ‣ (e+ p x)

--}


pr-sub :  {Δ Γ : ctx}
--
       -> (A : ty Γ)
       -> (B : ty (Γ ▷ A))
       -> (h : subst Δ Γ)
       -> (a b  : raw Γ)
       -> (p : Γ ==> a :: A)
       -> (Γ ==> b :: (B [[ els p ]]))

--     ---------------------------------------
       -> Δ ==>  (pr a b) [ h ] ==  pr (a [ h ]) (b [ h ])  :: (Σ-f A B) [[ h ]]
pr-sub {Δ} {Γ} A B h a b p q =
 let
      lm : Δ ==>  (Σ-f A B) [[ h ]] ==  Σ-f (A [[ h ]]) (B [[ ↑ A h ]])
      lm = Σ-f-sub {Δ} {Γ} A B h
      ph : Δ ==> a [ h ] :: A  [[ h ]]
      ph = elt-subst h p
      q' : Δ ==> b [ h ] :: (B [[ els p ]] [[ h ]])
      q' = elt-subst h q
      lm1 :  Δ ==> (B [[ els p ]] [[ h ]]) == (B [[ ↑ A h ]] [[ els ph ]])
      lm1 = B-els-h-sub {Δ} {Γ} A B a p h
      qh : Δ ==> b [ h ] :: (B [[ ↑ A h ]] [[ els ph ]])
      qh =  elttyeq q' lm1


      lm2 : Δ ==>  pr (a [ h ]) (b [ h ])  ::  Σ-f (A [[ h ]]) (B [[ ↑ A h ]])
      lm2 = Σ-i (A [[ h ]]) (B [[ ↑ A h ]]) (a [ h ]) ph (b [ h ]) qh


      lm3 : Δ ==> pr (a [ h ]) (b [ h ]) :: Σ-f A B [[ h ]]
      lm3 = elttyeq lm2 (tysym lm)
 in  pair (λ x → refV _) (pair (elt-subst h (Σ-i  A B a p b q)) lm3)

{--

pr1-op : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (Γ ==> c :: Σ-f A B)
      -> (|| κ Γ || -> V)
pr1-op {Γ} A B c p x =  apt A x  ‣ pj1 (pj1 (apel p x))

pr1 : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (Γ ==> c :: Σ-f A B)
      -> raw Γ
pr1 {Γ} A B c p = mkraw (record { op = pr1-op {Γ} A B c p
                                ; ext = pr1-ext {Γ} A B c p })

sub-apply : {Δ Γ : ctx}
     -> (a : raw Γ) ->  (f : subst Δ Γ) -> (x : || κ Δ ||)
     -> apr (a [ f ]) x ≐ apr a (aps f x)
sub-apply a f x = refV _

      eq2 : apt (Σ-f A B) x ‣ pj1 (apel p x) ≐ apt (Σ-f A B) y ‣ pj1 (apel p y)
           eq2 = traV (symV lm2) (traV eq lm4)
           eq3 : < (apt A x) ‣ (pj1 (pj1 (apel p x))) , (apt B  (x , (pj1  (pj1 (apel p x))))) ‣ (pj2 (pj1 (apel p x))) >
               ≐ < (apt A y) ‣ (pj1 (pj1 (apel p y))) , (apt B  (y , (pj1  (pj1 (apel p y))))) ‣ (pj2 (pj1 (apel p y))) >
           eq3 = traV (symV (Σ-f-exp3 A B x (pj1 (apel p x)))) (traV eq2 (Σ-f-exp3 A B y (pj1 (apel p y))))

Σ-f-exp3 :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (x : || κ Γ ||)
       -> (u : # (apt (Σ-f {Γ} A B)  x))
       -> (apt (Σ-f {Γ} A B)  x) ‣ u ≐  < (apt A x) ‣ (pj1 u) , (apt B  (x , (pj1  u))) ‣ (pj2 u) >
Σ-f-exp3  A B x u = refV _

--}

pr1-sub-raw :  {Δ Γ : ctx}
--
       -> (A : ty Γ)
       -> (B : ty (Γ ▷ A))
       -> (h : subst Δ Γ)
       -> (c  : raw Γ)
       -> (p : Γ ==> c :: Σ-f A B)
       -> (q : Δ ==> c [ h ] ::  Σ-f (A [[ h ]]) (B [[ ↑ A h ]]))
       -> (x :  || κ Δ ||)
       ->  apr (pr1 A B c p [ h ]) x ≐ apr (pr1 (A [[ h ]]) (B [[ ↑ A h ]]) (c [ h ]) q) x
pr1-sub-raw {Δ} {Γ} A B h c p q x =
   let
       eq1 : apr c (aps h x) ≐
                 apt (Σ-f A B) (aps h x) ‣ pj1 (apel p (aps h x))
       eq1 = pj2 (apel p (aps h x))
       eq2 : apr (c [ h ]) x ≐
                 apt (Σ-f (A [[ h ]]) (B [[ ↑ A h ]])) x ‣ pj1 (apel q x)
       eq2 = pj2 (apel q x)
       eq3 : apt (Σ-f A B) (aps h x) ‣ pj1 (apel p (aps h x))
                  ≐
             apt (Σ-f (A [[ h ]]) (B [[ ↑ A h ]])) x ‣ pj1 (apel q x)
       eq3 = traV (symV eq1) eq2
       eq4 : apt (Σ-f A B) (aps h x) ‣ (pj1 (apel p (aps h x)))  ≐
                  < (apt A (aps h x)) ‣ (pj1 (pj1 (apel p (aps h x)))) ,
                     (apt B  ((aps h x) , (pj1  (pj1 (apel p (aps h x)))))) ‣ (pj2 (pj1 (apel p (aps h x)))) >
       eq4 = Σ-f-exp3  A B (aps h x) (pj1 (apel p (aps h x)))
       eq5 : apt (Σ-f (A [[ h ]]) (B [[ ↑ A h ]])) x ‣ (pj1 (apel q x))  ≐
               < (apt (A [[ h ]]) x) ‣ (pj1 (pj1 (apel q x))) ,
                   (apt (B [[ ↑ A h ]])  (x , (pj1  (pj1 (apel q x))))) ‣ (pj2 (pj1 (apel q x))) >
       eq5 =  Σ-f-exp3 (A [[ h ]]) (B [[ ↑ A h ]]) x (pj1 (apel q x))
       eq6 : (apt A (aps h x)) ‣ (pj1 (pj1 (apel p (aps h x))))
              ≐ (apt (A [[ h ]]) x) ‣ (pj1 (pj1 (apel q x)))
       eq6 =  prj1 (pairV-inv-1 (traV (symV eq4) (traV eq3 eq5)))
-- pairV-inv-1 : {x y z u : V} -> < x , y > ≐ < z , u > ->  and (x ≐ z) (y ≐ u)
       lm1 :  apr (pr1 A B c p [ h ]) x  ≐  apr (pr1 A B c p) (aps h x)
       lm1 = sub-apply (pr1 A B c p) h x
       lm2 : apr (pr1 A B c p) (aps h x) ≐ apt A (aps h x)  ‣  pj1 (pj1 (apel p (aps h x)))
       lm2 = refV _
       lm3 :  apr (pr1 (A [[ h ]]) (B [[ ↑ A h ]]) (c [ h ]) q) x  ≐  apt (A [[ h ]]) x  ‣ pj1 (pj1 (apel q x))
       lm3 = refV _
       lm4 : apt A (aps h x)  ‣  pj1 (pj1 (apel p (aps h x))) ≐  apt (A [[ h ]]) x  ‣ pj1 (pj1 (apel q x))
       lm4 = eq6
   in traV lm1 (traV lm2 (traV lm4 (symV lm3)))

pr1-sub :  {Δ Γ : ctx}
--
       -> (A : ty Γ)
       -> (B : ty (Γ ▷ A))
       -> (h : subst Δ Γ)
       -> (c  : raw Γ)
       -> (p : Γ ==> c :: Σ-f A B)
       -> (q : Δ ==> c [ h ] ::  Σ-f (A [[ h ]]) (B [[ ↑ A h ]]))
--     ---------------------------------------
       -> Δ ==>  (pr1 A B c p) [ h ] ==  pr1 (A [[ h ]]) (B [[ ↑ A h ]]) (c [ h ]) q  :: A [[ h ]]

pr1-sub {Δ} {Γ} A B h c p q = pair (pr1-sub-raw {Δ} {Γ} A B h c p q)
                                   (pair (elt-subst h (Σ-e-1  {Γ} A B c p ))
                                         (Σ-e-1 {Δ} (A [[ h ]]) (B [[ ↑ A h ]]) (c [ h ]) q))

pr2-sub-raw :  {Δ Γ : ctx}
--
       -> (A : ty Γ)
       -> (B : ty (Γ ▷ A))
       -> (h : subst Δ Γ)
       -> (c  : raw Γ)
       -> (p : Γ ==> c :: Σ-f A B)
       -> (q : Δ ==> c [ h ] ::  Σ-f (A [[ h ]]) (B [[ ↑ A h ]]))
       -> (r : Δ ==> (pr1 A B c p) [ h ] :: A [[ h ]])
       -> (x : || κ Δ ||)
       -> apr (pr2 A B c p [ h ]) x ≐  apr (pr2 (A [[ h ]]) (B [[ ↑ A h ]]) (c [ h ]) q) x
pr2-sub-raw {Δ} {Γ} A B h c p q r x =
  let
       eq1 : apr c (aps h x) ≐
                 apt (Σ-f A B) (aps h x) ‣ pj1 (apel p (aps h x))
       eq1 = pj2 (apel p (aps h x))
       eq2 : apr (c [ h ]) x ≐
                 apt (Σ-f (A [[ h ]]) (B [[ ↑ A h ]])) x ‣ pj1 (apel q x)
       eq2 = pj2 (apel q x)
       eq3 : apt (Σ-f A B) (aps h x) ‣ pj1 (apel p (aps h x))
                  ≐
             apt (Σ-f (A [[ h ]]) (B [[ ↑ A h ]])) x ‣ pj1 (apel q x)
       eq3 = traV (symV eq1) eq2
       eq4 : apt (Σ-f A B) (aps h x) ‣ (pj1 (apel p (aps h x)))  ≐
                  < (apt A (aps h x)) ‣ (pj1 (pj1 (apel p (aps h x)))) ,
                     (apt B  ((aps h x) , (pj1  (pj1 (apel p (aps h x)))))) ‣ (pj2 (pj1 (apel p (aps h x)))) >
       eq4 = Σ-f-exp3  A B (aps h x) (pj1 (apel p (aps h x)))
       eq5 : apt (Σ-f (A [[ h ]]) (B [[ ↑ A h ]])) x ‣ (pj1 (apel q x))  ≐
               < (apt (A [[ h ]]) x) ‣ (pj1 (pj1 (apel q x))) ,
                   (apt (B [[ ↑ A h ]])  (x , (pj1  (pj1 (apel q x))))) ‣ (pj2 (pj1 (apel q x))) >
       eq5 =  Σ-f-exp3 (A [[ h ]]) (B [[ ↑ A h ]]) x (pj1 (apel q x))
       eq6 : (apt B  ((aps h x) , (pj1  (pj1 (apel p (aps h x)))))) ‣ (pj2 (pj1 (apel p (aps h x))))
                ≐
             (apt (B [[ ↑ A h ]])  (x , (pj1  (pj1 (apel q x))))) ‣ (pj2 (pj1 (apel q x)))
       eq6 =  prj2 (pairV-inv-1 (traV (symV eq4) (traV eq3 eq5)))
-- pairV-inv-1 : {x y z u : V} -> < x , y > ≐ < z , u > ->  and (x ≐ z) (y ≐ u)

   in eq6

-- TO DO : good formulation?

pr2-sub :  {Δ Γ : ctx}
--
       -> (A : ty Γ)
       -> (B : ty (Γ ▷ A))
       -> (h : subst Δ Γ)
       -> (c  : raw Γ)
       -> (p : Γ ==> c :: Σ-f A B)
       -> (q : Δ ==> c [ h ] ::  Σ-f (A [[ h ]]) (B [[ ↑ A h ]]))
       -> (r : Δ ==> (pr1 A B c p) [ h ] :: A [[ h ]])
--     ---------------------------------------
       -> Δ ==>  (pr2 A B c p) [ h ] ==  pr2 (A [[ h ]]) (B [[ ↑ A h ]]) (c [ h ]) q
                      ::  (B [[ ↑ A h ]] [[ els r ]])

pr2-sub {Δ} {Γ} A B h c p q r =
  let lm0 : << Raw Δ >> (pr2 A B c p) [ h ] ~ pr2 (A [[ h ]]) (B [[ ↑ A h ]]) (c [ h ]) q
      lm0 = <<>> (<<>> (λ x → <<>> ((pr2-sub-raw {Δ} {Γ} A B h c p q r) x)))
      lm1 :  Γ ==> pr1 A B c p :: A
      lm1 = Σ-e-1 {Γ} A B c p
      lm2 :  Γ ==> pr2 A B c p ::  B [[ els lm1 ]]
      lm2 = Σ-e-2 {Γ} A B c p lm1
      lm3 :  Δ ==> pr2 A B c p [ h ] ::  B [[ els lm1 ]] [ h ]
      lm3 = elt-subst h lm2
      lm3b : < Subst Δ (Δ ▷ (A [[ h ]])) >  (els (elt-subst h (Σ-e-1 A B c p))) ~ (els r)
      lm3b = els-irr (elt-subst h (Σ-e-1 A B c p)) r
      lm4 :  Δ ==>  B [[ els lm1 ]] [ h ] == (B [[ ↑ A h ]]) [[ els r ]]
      lm4 = tytra (B-els-h-sub A B _ lm1 h) (tyeq-subst2 (B [[ ↑ A h ]]) _ _ lm3b)
      lm5 :  Δ ==> pr2 A B c p [ h ] :: (B [[ ↑ A h ]]) [[ els r ]]
      lm5 = elttyeq lm3 lm4

      lm9 : Δ ==> pr2 (A [[ h ]]) (B [[ ↑ A h ]]) (c [ h ]) q ::  (B [[ ↑ A h ]]) [[ els r ]]
      lm9 =  subj-red _ _ lm5 lm0
     --
  in
        pair (pr2-sub-raw {Δ} {Γ} A B h c p q r)  (pair lm5 lm9)

{--

els-irr :   {Γ : ctx}
    -> {A : ty Γ}
    -> {a : raw Γ}
    -> (p : Γ ==> a :: A)
    -> (q : Γ ==> a :: A)
    -> < Subst Γ (Γ ▷ A) > els p ~ els q

tyeq-subst2 :  {Δ Γ : ctx} -> (A : ty Γ) -> (f g : subst Δ Γ)
--
                  -> < Subst Δ Γ > f ~ g
--      --------------------------------------------------
         -> Δ ==> A [[ f ]] ==  A [[ g ]]


B-els-h-sub :  {Δ Γ : ctx}
--
       -> (A : ty Γ)
       -> (B : ty (Γ ▷ A))
       -> (a   : raw Γ)
       -> (p : Γ ==> a :: A)
       -> (h : subst Δ Γ)
-- ---------------------------------------------------------------
       ->  Δ ==> (B [[ els p ]] [[ h ]]) == (B [[ ↑ A h ]] [[ els (elt-subst h p) ]])
--


       -> (r : Δ ==> (pr1 A B c p) [ h ] :: A [[ h ]])

Σ-e-1 : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> Γ ==> pr1 A B c p :: A

Σ-e-2 {Δ} (A [[ h ]]) (B [[ ↑ A h ]]) (c [ h ]) r

Σ-e-2 : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> (q : Γ ==> pr1 A B c p :: A)
      -> Γ ==> pr2 A B c p :: B [[ els q ]]
Σ-e-2 {Γ} A B c p q = mk-elt (Σ-e-2-lm {Γ} A B c p q)

Σ-e-1 : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (c  : raw Γ)
      -> (p : Γ ==> c :: Σ-f A B)
      -> Γ ==> pr1 A B c p :: A

elt-subst :  {Δ Γ : ctx} -> {a : raw Γ} -> {A : ty Γ} -> (f : subst Δ Γ)
--
         -> Γ ==> a :: A
--   --------------------------------------------------------
         -> Δ ==> a [ f ] ::  A [[ f ]]

Σ-i : {Γ : ctx}
      -> (A  : ty Γ)
      -> (B : ty (Γ ▷ A))
      -> (a  : raw Γ)
      -> (p : Γ ==> a :: A)
      -> (b : raw Γ)
      -> (Γ ==> b :: (B [[ els p ]]))
      -> Γ ==> pr a b :: Σ-f A B

--}
