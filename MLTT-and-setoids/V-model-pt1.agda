-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt1 where

open import basic-types
open import basic-setoids
open import dependent-setoids
open import subsetoids
open import iterative-sets
open import iterative-sets-pt2
open import iterative-sets-pt3
open import V-model-pt0




-- context extensions


Ext : (Γ : ctx) -> (A : ty Γ) -> ctx
Ext Γ A = sigmaV Γ (ty.type A)

infixl 20 _▷_

_▷_ : (Γ : ctx) -> (A : ty Γ) -> ctx
Γ ▷ A = Ext Γ A


pp-ext : {Γ : ctx} -> (A : ty Γ) -> (u v : || κ (Γ ▷ A) ||) -> (p : < κ (Γ ▷ A) > u ~ v)
     ->  < κ Γ > pj1 u ~ pj1 v
pp-ext {Γ} A (u1 , u2) (v1 , v2) p = <> (prj1 (pairV-inv-1 (>< p)))

pp : {Γ : ctx} -> (A : ty Γ) -> subst (Γ ▷ A) Γ
pp A = sb (record { op = λ u → pj1 u
                        ; ext = λ u v p → pp-ext A u v p   })



-- short for pp is downarrow ↓  typed \d

↓ : {Γ : ctx} -> (A : ty Γ) -> subst (Γ ▷ A) Γ
↓ A = pp A

-- the variable term

vv : {Γ : ctx} -> (A : ty Γ) -> raw (Γ ▷ A)
vv {Γ} A = mkraw (pj2-sigmaV  Γ (ty.type A))



asm : {Γ : ctx}
--
      -> (A : ty Γ)
--   --------------------------------------------------------
      -> Γ ▷ A ==> vv A :: A [[ ↓ A ]]
--
asm {Γ} A =  mk-elt (pj2-sigmaV-prop Γ (ty.type A))



asm-apply : {Γ : ctx}  -> (A : ty Γ)
     -> (x :  || κ Γ ||) ->  (y : || κ (apt A x) ||)
     ->  apr (vv A) (x , y) ≐ apt (A [[ ↓ A ]]) (x , y) ‣ y
asm-apply A x y = (pj2 (apel (asm A) (x , y)))



ext-op : {Δ Γ : ctx} -> (A : ty Γ)
        ->  (f : subst Δ Γ) -> (a : raw Δ)
        -> Δ ==> a :: A [[ f ]]
        -> || κ Δ || -> || κ (Γ ▷ A) ||
ext-op A f a p u = (aps f u) , (pj1 (apel p u))



ext-ext : {Δ Γ : ctx} -> (A : ty Γ)
        ->  (f : subst Δ Γ) -> (a : raw Δ)
        -> (p : Δ ==> a :: A [[ f ]])
        -> (u  v : || κ Δ ||)
        -> < κ Δ > u ~ v
        -> < κ (Γ ▷ A) > ext-op A f a p u ~ ext-op A f a p v
ext-ext {Δ} {Γ} A f a p u v q =
       let  lm1 : < κ Γ > ap (subst.cmap f) u ~ ap (subst.cmap f) v
            lm1 = (extensionality (subst.cmap f) _ _ q)
            lmA : << VV >> (apt A  (ap (subst.cmap f) u)) ~ (apt A  (ap (subst.cmap f) v))
            lmA  = extensionality1 (ty.type A) (ap (subst.cmap f) u) (ap (subst.cmap f) v) lm1
            lmC : (apr a u) ≐ (apt (A [[ f ]]) u) ‣ pj1 (apel p u)
            lmC = pj2 (apel p u)
            lmD : (apr a v) ≐ (apt (A [[ f ]]) v) ‣ pj1 (apel p v)
            lmD = pj2 (apel p v)
            lmE : << VV >> (apr a u) ~ (apr a v)
            lmE = extensionality1 (raw.rawterm a) u v q
            lm2 :  (apt A (ap (subst.cmap f) u)) ‣ pj1 (apel p u) ≐
                   (apt A (ap (subst.cmap f) v)) ‣ pj1 (apel p v)
            lm2 = traV (symV lmC) (traV (>><< lmE) lmD)

       in <> (pairV-ext (>< lm1) lm2)



ext : {Δ Γ : ctx} -> (A : ty Γ)
      ->  (f : subst Δ Γ) -> (a : raw Δ)
      -> Δ ==> a :: A [[ f ]]
      -> subst Δ (Γ ▷ A)
ext {Δ} {Γ} A f a p = sb (record { op = ext-op A f a p
                                       ; ext = ext-ext A f a p })



ext-irr : {Δ Γ : ctx} -> (A : ty Γ)
      ->  (f : subst Δ Γ) -> (a : raw Δ)
      -> (p : Δ ==> a :: A [[ f ]])
      -> (q : Δ ==> a :: A [[ f ]])
      -> < Subst Δ (Γ ▷ A) >  (ext A f a p) ~  (ext A f a q)
ext-irr {Δ} {Γ} A f a p q  =
    <> (<> (\ x -> <> (pairV-ext (refV (Γ ‣ aps f x)) (traV (symV (pj2 (apel p x))) (pj2 (apel q x))))))




ext-prop1 : {Δ Γ : ctx} -> (A : ty Γ)
      -> (f : subst Δ Γ) -> (a : raw Δ)
      -> (p : Δ ==> a :: A [[ f ]])
      -> < Subst Δ Γ >  ((↓ A) ⌢ (ext A f a p)) ~ f
ext-prop1 {Δ} {Γ} A f a p = <> (<> (λ x → refl (κ Γ) (ap (subst.cmap f) x)))



ext-prop2 : {Δ Γ : ctx} -> (A : ty Γ)
      ->  (f : subst Δ Γ) -> (a : raw Δ)
      -> (p : Δ ==> a :: A [[ f ]])
      -> << Raw Δ >>  (vv A) [ ext A f a p ] ~ a
ext-prop2  A f a p = <<>> (<<>> (λ x →
                              let lm5 : (apt A (ap (subst.cmap f) x)) ‣ (pj1 (apel p x)) ≐ (apr a  x)
                                  lm5 = symV (pj2 (apel p x))
                                  main : << VV >> apr (sub (vv A) (ext A f a p)) x ~ (apr a x)
                                  main = <<>> lm5
                               in main))


ext-prop3-lm : {Γ : ctx}-> (A : ty Γ) ->
        (ctx-maps (Γ ▷ A) (Γ ▷ A) setoid.∼
          subst.cmap (ext A (↓ A) (vv A) (asm A)))
          (subst.cmap (ids {Γ ▷ A}))
ext-prop3-lm {Γ} A (x , y) =
                  <> (  let    lm2 :  < κ (Γ ▷ A) > (x , y)  ~  (x , y)
                               lm2 = refl (κ (Γ ▷ A)) (x , y)
                               lm1 :  < κ (Γ ▷ A) >
                                        (ap (subst.cmap (pp A)) (x , y)  ,  (pj1 (apel (asm A) (x , y))))
                                       ~  (x , y)
                               lm1 = lm2
                               main : < κ (Γ ▷ A) >
                                       (ext-op A (pp A) (vv A) (asm A)) (x , y)
                                       ~  (x , y)
                               main = lm1
                        in >< main)

ext-prop3 : {Γ : ctx}-> (A : ty Γ) ->
            < Subst (Γ ▷ A) (Γ ▷ A) >  (ext A (↓ A) (vv A) (asm A)) ~ ids {Γ ▷ A}
ext-prop3 {Γ} A  = <> (<> (ext-prop3-lm {Γ} A))





ext-prop4-lm : {Θ Δ Γ : ctx} -> (A : ty Γ)
      -> (f : subst Δ Γ) -> (a : raw Δ)
      -> (p : Δ ==> a :: A [[ f ]])
      -> (h : subst Θ Δ)
      -> Θ ==> a [ h ] :: A [[ f ⌢ h ]]
ext-prop4-lm  {Θ} {Δ} {Γ} A f a p h =
          let lm1 :  Θ ==> sub a h :: Sub (Sub  A f) h
              lm1  = elt-subst h p
              lm2a : << Ty Θ >>  (A [[ f ]] [[ h ]])  ~  (A [[ f ⌢ h ]])
              lm2a = Sub-comp-prop-sym {Θ} {Δ} {Γ} A f h
              lm2 : Θ ==> Sub (Sub A f) h == Sub A (f ⌢ h)
              lm2 = tyeq-from-eq _ _ lm2a
              main :  Θ ==> sub a h :: Sub A (f ⌢ h)
              main = elttyeq lm1 lm2
          in main


ext-prop4-lm2 : {Θ Δ Γ : ctx} -> (A : ty Γ)
      -> (f : subst Δ Γ) -> (a : raw Δ)
      -> (p : Δ ==> a :: A [[ f ]])
      -> (h : subst Θ Δ)
      -> (q : Θ ==> a [ h ] :: A [[ f ⌢ h ]])
--    --------------------------------------------
      -> < Subst Θ (Γ ▷ A) > ((ext A f a p) ⌢ h) ~ (ext A (f ⌢ h) (a [ h ]) q)
--
ext-prop4-lm2 {Θ} {Δ} {Γ} A f a p h q = <> (<> (λ u →
              let lm1 :  Γ ‣ ap (subst.cmap f) (ap (subst.cmap h) u) ≐ Γ ‣ ap (subst.cmap (f ⌢ h)) u
                  lm1 = refV _
                  lm2 : << VV >> (apt A  (ap (subst.cmap f) (ap (subst.cmap h) u))) ~
                               (apt A  (ap (subst.cmap (f ⌢ h)) u))
                  lm2 = extensionality1 (ty.type A) (ap (subst.cmap f) (ap (subst.cmap h) u))
                                                    (ap (subst.cmap (f ⌢ h)) u)  (<> lm1)
                  p2  : apr a (ap (subst.cmap h) u) ≐
                        (apt (A [[ f ]])  (ap (subst.cmap h) u) ‣ pj1 (apel p (ap (subst.cmap h) u)))
                  p2 = pj2 (apel p (ap (subst.cmap h) u))
                  q2  : apr (a [ h ])  u ≐ (apt (A [[ f ⌢ h ]])  u) ‣ pj1 (apel q u)
                  q2 = pj2 (apel q u)
                  lm3 : (apt A  (ap (subst.cmap f) (ap (subst.cmap h) u))) ‣ pj1 (apel p (ap (subst.cmap h) u))
                          ≐ (apt A (ap (subst.cmap (f ⌢ h)) u)) ‣ pj1 (apel q u)
                  lm3 = traV (symV p2) (traV q2 (refV _))
                  main : < κ (Γ ▷ A) >  ap (subst.cmap (ext A f a p))  (ap (subst.cmap h) u) ~
                                        ap (subst.cmap (ext A (f ⌢ h) (sub a h) q)) u
                  main = <> (pairV-ext lm1 lm3)
              in main))





ext-prop4 : {Θ Δ Γ : ctx} -> (A : ty Γ)
      -> (f : subst Δ Γ) -> (a : raw Δ)
      -> (p : Δ ==> a :: A [[ f ]])
      -> (h : subst Θ Δ)
--  --------------------------
      -> < Subst Θ (Γ ▷ A) > ((ext A f a p) ⌢ h) ~ (ext A (f ⌢ h) (a [ h ]) (ext-prop4-lm  A f a p h ))
--
ext-prop4 {Θ} {Δ} {Γ} A f a p h = ext-prop4-lm2 A f a p h (ext-prop4-lm  A f a p h )





ext-eq-half-lm : {Γ : ctx}
--
      -> (A  A' : ty Γ)
      -> (Γ ==> A == A')
-- --------------------------
      -> (Γ ▷ A) ≤ (Γ ▷ A')
ext-eq-half-lm {Γ} A A' p (x , y) =  ( (x , (ap (κ-Fam ±± ape p x) y))) , (pairV-ext (refV (Γ ‣ x)) (e+prop (>><< (ape p x)) y))


ext-eq-half2-lm : {Γ : ctx}
--
      -> (A  A' : ty Γ)
      -> (Γ ==> A == A')
-- --------------------------
      -> (Γ ▷ A) ≥ (Γ ▷ A')
ext-eq-half2-lm {Γ} A A' p (x , y) =  (x , (ap (κ-Fam ±± ape (tysym p) x) y)) , pairV-ext (refV (Γ ‣ x)) (symV (e+prop (>><< (ape (tysym p) x)) y))


-- ** Same as ext-eq' later ?

ext-eq : {Γ : ctx}
--
      -> (A  A' : ty Γ)
      -> (Γ ==> A == A')
-- --------------------------
      -> (Γ ▷ A) ≐ (Γ ▷ A')
ext-eq {Γ} A A' p = pair (ext-eq-half-lm  {Γ} A A' p) (ext-eq-half2-lm {Γ} A A' p)




ext-eq-lm : {Γ : ctx}
      -> (A  A' : ty Γ)
      -> (p : Γ ==> A == A')
      -> (x : || κ Γ ||)
      -> (y : || κ (apt A x)||)
      -> < κ (Γ ▷ A') > (ap (κ-trp (ext-eq A A' p) ) (x , y)) ~ (x , (ap (κ-Fam ±± ape p x) y))
ext-eq-lm {Γ} A A' p x y = refl _ _




subst-trp-id :  {Γ : ctx} ->  (p : << Ctx >> Γ ~ Γ)
      -> < Subst Γ Γ > subst-trp p ~ ids {Γ}
subst-trp-id {Γ} p = <> (<> (λ x → κ-trp-id (>><< p) x))



subst-trp-irr :  {Γ Δ : ctx}
      ->  (p q : << Ctx >> Γ ~ Δ)
      -> < Subst Γ Δ > subst-trp p ~ subst-trp q
subst-trp-irr {Γ} {Δ} p q = <> (<> (λ x → κ-trp-irr (>><< p) (>><< q) x))


subst-trp-fun :  {Γ Δ  Θ : ctx}
    ->  (p : << Ctx >> Γ ~ Δ)   ->  (q : << Ctx >> Δ ~ Θ)
    ->  (r : << Ctx >> Γ ~ Θ)
    -> < Subst Γ Θ > ((subst-trp q) ⌢ (subst-trp p)) ~ subst-trp r
subst-trp-fun {Γ} {Δ} {Θ} p q r = <> (<> (λ x → sym (κ-trp-fn (>><< q) (>><< p) (>><< r) x)))

subst-trp-inv :  {Γ Δ : ctx}
    ->  (p : << Ctx >> Γ ~ Δ)   ->  (q : << Ctx >> Δ ~ Γ)
    -> < Subst Γ Γ > ((subst-trp q) ⌢ (subst-trp p)) ~ ids {Γ}
subst-trp-inv {Γ} {Δ} p q = tra (subst-trp-fun p q (tra' p q)) (subst-trp-id _)

subst-trp-lm :  {Γ Δ : ctx}
      ->  (p : << Ctx >> Γ ~ Δ)
      ->  (x : # Γ)
      ->  Γ ‣ x ≐ Δ ‣ aps (subst-trp p) x
subst-trp-lm {Γ} {Δ} p x =
     let q : Γ ≐ Δ
         q = >><< p
         main :  Γ ‣ x ≐ Δ ‣ aps (subst-trp p) x
         main = e+prop q x
     in main

half1-ext-eq'' : {Γ Δ : ctx}
--
      -> (A : ty Γ)
      -> (B : ty Δ)
      -> (p : << Ctx >> Γ ~ Δ)
      -> (Γ ==> A == B [[ subst-trp p ]])
-- --------------------------
      -> (Γ ▷ A) ≤ (Δ ▷ B)
half1-ext-eq'' {Γ} {Δ} A B p q (x , y) =
          let eq :  (type A • x) ≐ (type B • aps (subst-trp p) x)
              eq = >><< (ape q x)
          in ((aps (subst-trp p) x) ,  (ap (κ-Fam ±± ape q x) y)) ,
                    pairV-ext (subst-trp-lm {Γ} {Δ} p x) (e+prop eq y)




half2-ext-eq'' : {Γ Δ : ctx}
--
      -> (A : ty Γ)
      -> (B : ty Δ)
      -> (p : << Ctx >> Γ ~ Δ)
      -> (Γ ==> A == B [[ subst-trp p ]])
-- --------------------------
      -> (Γ ▷ A) ≥ (Δ ▷ B)
half2-ext-eq'' {Γ} {Δ} A B p q (x , y) =
  let lm : (Δ ==> A [[ subst-trp (sym' p) ]] == B [[ subst-trp p ]] [[ subst-trp (sym' p) ]])
      lm = tyeq-subst (subst-trp (sym' p)) q
      lm0 : < Subst Δ Δ >  (subst-trp p) ⌢ (subst-trp (sym' p))  ~  ids
      lm0 = subst-trp-inv (sym' p) p
      lm1 : Δ ==> B [[ (subst-trp p) ⌢ (subst-trp (sym' p)) ]] == B [[ ids ]]
      lm1 = tyeq-subst2 B _ _ lm0
      lm2 : Δ ==> (B [[ subst-trp p ]]) [[ subst-trp (sym' p) ]] == B [[ ids ]]
      lm2 = tytra (tysym (tysubst-com B (subst-trp p) (subst-trp (sym' p)))) lm1
      lm3 : Δ ==> B [[ ids ]] == B
      lm3 = tysubst-id B
      q' :  (Δ ==> B == A [[ subst-trp (sym' p) ]])
      q' = tysym (tytra lm (tytra lm2 lm3))
      eq :  (type B • x) ≐ (type A • aps (subst-trp (sym' p)) x)
      eq =  >><< (ape q' x)

  in ((aps (subst-trp (sym' p)) x) ,  (ap (κ-Fam ±± ape q' x) y)) ,
       pairV-ext (symV (subst-trp-lm (sym' p) x )) (symV (e+prop eq y))



ext-eq'' : {Γ Δ : ctx}
--
      -> (A : ty Γ)
      -> (B : ty Δ)
      -> (p : << Ctx >> Γ ~ Δ)
      -> (Γ ==> A == B [[ subst-trp p ]])
-- --------------------------
      -> << Ctx >> (Γ ▷ A) ~ (Δ ▷ B)
ext-eq'' {Γ} {Δ} A B p q = <<>> (pair (half1-ext-eq'' {Γ} {Δ} A B p q) (half2-ext-eq'' {Γ} {Δ} A B p q))


↓-cong-lm  : {Γ Δ : ctx}
--
      -> (A : ty Γ)
      -> (B : ty Δ)
      -> (p : << Ctx >> Γ ~ Δ)
      -> (q : Γ ==> A == B [[ subst-trp p ]])
      -> (x : || κ (Γ ▷ A) ||)
      ->  (κ Δ setoid.∼
           setoidmap.op (subst.cmap (subst-trp p ⌢ ↓ A)) x)
           (setoidmap.op (subst.cmap (↓ B ⌢ subst-trp (ext-eq'' A B p q))) x)
↓-cong-lm  {Γ} {Δ} A B p q (x , y) = refV _

↓-cong  : {Γ Δ : ctx}
--
      -> (A : ty Γ)
      -> (B : ty Δ)
      -> (p : << Ctx >> Γ ~ Δ)
      -> (q : Γ ==> A == B [[ subst-trp p ]])
-- --------------------------
      -> < Subst (Γ ▷ A) Δ > ((subst-trp p) ⌢ (↓ A)) ~ ((↓ B) ⌢ (subst-trp (ext-eq'' {Γ} {Δ} A B p q)))
↓-cong {Γ} {Δ} A B p q = <> (<> (λ x → <> (↓-cong-lm  {Γ} {Δ} A B p q x)))



asm-cong-raw-lm  : {Γ Δ : ctx}
--
      -> (A : ty Γ)
      -> (B : ty Δ)
      -> (p : << Ctx >> Γ ~ Δ)
      -> (q : Γ ==> A == B [[ subst-trp p ]])
      -> (x : || κ (Γ ▷ A) ||)
      -> (VV classoid.∼ raw.rawterm (vv A) • x)
            (raw.rawterm (vv B [ subst-trp (ext-eq'' A B p q) ]) • x)
asm-cong-raw-lm {Γ} {Δ} A B p q (x , y) =
   let lm : raw.rawterm (vv A) • (x , y) ≐ (apt A  x) ‣ y
       lm = refV _
       lm0 :  apt A x ≐  apt (B [[ subst-trp p ]]) x
       lm0 = >><< (ape q x)
       lm0b :  apt (B [[ subst-trp p ]]) x ≐  apt B (aps (subst-trp p) x)
       lm0b = Sub-apply B (subst-trp p) x
       lm0c :  apt A x ≐ apt B (aps (subst-trp p) x)
       lm0c = traV lm0 lm0b
       lm0d :  apt B (aps (subst-trp p) x) ‣ e+ (traV (>><< (ape q x)) (Sub-apply B (subst-trp p) x)) y
                ≐ apt B (aps (subst-trp p) x) ‣ ap (κ-Fam ±± ape q x) y
       lm0d = >< (κ-trp-irr (traV (>><< (ape q x)) (Sub-apply B (subst-trp p) x)) lm0 y)
       lm1 :  (apt A x) ‣ y ≐ (apt B (aps (subst-trp p) x)) ‣ (ap (κ-Fam ±± ape q x) y)
       lm1 = traV (e+prop lm0c y) lm0d
       lm2 : apr (vv B [ subst-trp (ext-eq'' A B p q) ]) (x , y)  ≐
             apr (vv B) (aps (subst-trp (ext-eq'' A B p q)) (x , y))
       lm2 = sub-apply (vv B) (subst-trp (ext-eq'' A B p q)) (x , y)
       main : raw.rawterm (vv A) • (x , y) ≐ (raw.rawterm (vv B [ subst-trp (ext-eq'' A B p q) ]) • (x , y))
       main = traV lm (traV lm1 (symV lm2))
   in main



asm-cong-raw  : {Γ Δ : ctx}
--
      -> (A : ty Γ)
      -> (B : ty Δ)
      -> (p : << Ctx >> Γ ~ Δ)
      -> (q : Γ ==> A == B [[ subst-trp p ]])
-- --------------------------
      -> << Raw (Γ ▷ A) >>  vv A ~ ((vv B) [ subst-trp (ext-eq'' {Γ} {Δ} A B p q) ])
asm-cong-raw {Γ} {Δ} A B p q = <<>> (<<>> (λ x → <<>> (asm-cong-raw-lm {Γ} {Δ} A B p q x)))

asm-cong  : {Γ Δ : ctx}
--
      -> (A : ty Γ)
      -> (B : ty Δ)
      -> (p : << Ctx >> Γ ~ Δ)
      -> (q : Γ ==> A == B [[ subst-trp p ]])
-- --------------------------
      ->  Γ ▷ A ==>  vv A == (vv B) [ subst-trp (ext-eq'' {Γ} {Δ} A B p q) ] :: A [[ ↓ A ]]
asm-cong {Γ} {Δ} A B p q =
   let rw = (asm-cong-raw {Γ} {Δ} A B p q)
   in  pair (Raw-lm rw)
            (pair (asm A)
                  (subj-red _ _  (asm A) rw))


ext-cong-lm : {Δ Γ : ctx} -> (A : ty Γ)
      -> (f g : subst Δ Γ) -> (a b : raw Δ)
      -> (p : Δ ==> a :: A [[ f ]])
      -> (q : Δ ==> b :: A [[ g ]])
      ->  < Subst Δ Γ > f ~ g
      -> (r : Δ ==> a == b :: A [[ f ]])
      -> (u  : || κ Δ ||)
      -> < κ (Γ ▷ A) >  (ext-op A f a p u) ~ (ext-op A g b q u)
ext-cong-lm {Δ} {Γ} A f g a b p q eq r u =
  let eq' = (>< (>< eq)) u
      lm :  Γ ‣ aps f u ≐ Γ ‣ aps g u
      lm = >< eq'
      lma = pj2 (apel p u)
      lmb = pj2 (apel q u)
      eq2 : apr a u ≐ apr b u
      eq2 = prj1 r u
      lm2 : (type A • aps f u) ‣ pj1 (apel p u) ≐  (type A • aps g u) ‣ pj1 (apel q u)
      lm2 = traV (traV (symV lma) eq2) lmb
  in <> (pairV-ext lm lm2)


ext-cong : {Δ Γ : ctx} -> (A : ty Γ)
      -> (f g : subst Δ Γ) -> (a b : raw Δ)
      -> (p : Δ ==> a :: A [[ f ]])
      -> (q : Δ ==> b :: A [[ g ]])
      ->  < Subst Δ Γ > f ~ g
      -> (r : Δ ==> a == b :: A [[ f ]])
      -> < Subst Δ (Γ ▷ A) >  (ext A f a p) ~ (ext A g b q)
ext-cong {Δ} {Γ} A f g a b p q eq r = <> (<> (λ u → (ext-cong-lm {Δ} {Γ} A f g a b p q eq r u)))



-- substitution of an element in the last argument and a short form

ext-el :
       {Γ : ctx}
    -> (A : ty Γ)
    -> (a : raw Γ)
    -> (Γ ==> a :: A)
    -> subst Γ (Γ ▷ A)
ext-el {Γ} A a p = ext A (ids {Γ}) a p




els  :
       {Γ : ctx}
    -> {A : ty Γ}
    -> {a : raw Γ}
    -> (Γ ==> a :: A)
    -> subst Γ (Γ ▷ A)
els {Γ} {A} {a} p = ext-el {Γ} A a p


els-irr :   {Γ : ctx}
    -> {A : ty Γ}
    -> {a : raw Γ}
    -> (p : Γ ==> a :: A)
    -> (q : Γ ==> a :: A)
    -> < Subst Γ (Γ ▷ A) > els p ~ els q
els-irr {Γ} {A} {a} p q = ext-irr A (ids {Γ}) a p q


els-cong :   {Γ : ctx}
    -> {A : ty Γ}
    -> {a a' : raw Γ}
    -> (p : Γ ==> a :: A)
    -> (q : Γ ==> a' :: A)
    -> (Γ ==> a == a' :: A)
    -> < Subst Γ (Γ ▷ A) > els p ~ els q
els-cong {Γ} {A} {a} {a'} p q r =
 <> (<>
   (\ x ->

     let lm1 : apr a x ≐ apt A x ‣ pj1 (apel p x)
         lm1 = pj2 (apel p x)
         lm2 : apr a' x ≐ apt A x ‣ pj1 (apel q x)
         lm2 = pj2 (apel q x)
         lm : (ty.type A • aps (ids {Γ}) x) ‣ pj1 (apel p x) ≐ (ty.type A • aps (ids {Γ}) x) ‣ pj1 (apel q x)
         lm = traV (symV lm1) (traV (prj1 r x) lm2)
     in <> (pairV-ext (refV (Γ ‣ aps (ids {Γ}) x)) lm)
  ))


els-exp : {Γ : ctx}
    -> {A : ty Γ}
    -> {a : raw Γ}
    -> (p : Γ ==> a :: A)
    -> < Subst Γ (Γ ▷ A) > els p ~  ext A (ids {Γ}) a p
els-exp {Γ} {A} {a} p = refl (Subst Γ (Γ ▷ A)) (els p)


qq :  {Δ Γ : ctx}
--
     -> (A : ty Γ)    -> (h : subst Δ Γ)
--  --------------------------------------
     -> subst (Δ ▷ (A [[ h ]])) (Γ ▷ A)
qq A h = ext  A
                         (h ⌢ (↓ (A [[ h ]])))
                         (vv (A [[ h ]])) (elttyeq
                                     (asm (A [[ h ]]))
                                     (tyeq-from-eq  ((A [[ h ]]) [[ ↓ (A [[ h ]]) ]]) (A [[ h ⌢ ↓ (A [[ h ]]) ]])
                                           (Sub-comp-prop-sym A h (↓ (A [[ h ]])))
                                     ))


-- the q-operation in terms of extension


-- short for qq is ↑ entered  \u

↑ :  {Δ Γ : ctx}  -> (A : ty Γ)    -> (h : subst Δ Γ)
     -> subst (Δ ▷ (A [[ h ]])) (Γ ▷ A)
↑ A h = qq A h




qq-eq :  {Δ Γ : ctx}
       -> (A : ty Γ)    -> (h : subst Δ Γ)
       -> (x : # Δ)
       -> (y : # (apt (A [[ h ]]) x))
       -> < κ (Γ ▷ A) > aps (↑ A h) (x , y) ~ (aps h x , y)
qq-eq {Δ} {Γ} A h x y =

    let lm2 = elttyeq-lm (asm (A [[ h ]]))
                         (tyeq-from-eq
                           ((A [[ h ]]) [[ ↓ (A [[ h ]]) ]])
                           (A [[ h ⌢ ↓ (A [[ h ]]) ]])
                           (Sub-comp-prop-sym A h (↓ (A [[ h ]]))))
                         (x , y)

        lm : (apt A (aps (h ⌢ ↓ (A [[ h ]])) (x , y))) ‣
              pj1
             (apel (elttyeq
                      (asm (A [[ h ]]))
             (tyeq-from-eq
               ((A [[ h ]]) [[ ↓ (A [[ h ]]) ]])
               (A [[ h ⌢ ↓ (A [[ h ]]) ]])
               (Sub-comp-prop-sym A h (↓ (A [[ h ]])))
               ))
               (x , y))
               ≐ (apt A (aps h x)) ‣ y
        lm = symV lm2
    in <> (pairV-ext (refV _) lm)



qq-ext-el-lm :  {Γ : ctx}
    -> (A : ty Γ)
    -> < Subst (Γ ▷ A) (Γ ▷ A) >  ((↑ A (↓ A))  ⌢  (els (asm A)))
                                         ~ (ids {Γ ▷ A})
qq-ext-el-lm {Γ} A  =
  <> (<> (λ z →
   let lm2 = elttyeq-lm
                (asm {Γ ▷ A} (A [[ ↓ A ]]))
                (tyeq-from-eq
                 ((A [[ ↓ A ]]) [[ ↓ (A [[ ↓ A ]]) ]])
                    (A [[ ↓ A ⌢ ↓ (A [[ ↓ A ]]) ]])
                 (Sub-comp-prop-sym A (↓ A) (↓ (A [[ ↓ A ]]))))
                (aps (els (asm A))
                  z)

       lm : (apt A
             (aps (pp A ⌢ ↓ (A [[ ↓ A ]]))
             (aps (els (asm A))
              z)))
            ‣
            pj1
            (apel (elttyeq
                  (asm (A [[ ↓ A ]]))
                  (tyeq-from-eq
                      ((A [[ ↓ A ]]) [[ ↓ (A [[ ↓ A ]]) ]])
                      (A [[ ↓ A ⌢ ↓ (A [[ ↓ A ]]) ]])
                     (Sub-comp-prop-sym A ( ↓ A) ( ↓ (A [[ ↓ A ]])))))
                  (aps (els (asm A))
              z))
            ≐ (apt A (pj1 z)) ‣ (pj2 z)
       lm = traV (symV lm2) (refV _)

   in <> (pairV-ext (refV (Γ ‣ (pj1 z))) lm )))


B-up-lm :  {Δ Γ : ctx}  -> (h : subst Δ Γ)
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (x  : || κ Δ ||)
    -> (y : || κ (apt (A [[ h ]]) x) ||)
    -> apt (B [[ ↑ A (h) ]]) (x , y)  ≐ apt B ((aps h x) , y)
B-up-lm {Δ} {Γ} h A B x y = >><< (extensionality1 (ty.type B) _ (((aps h x) , y)) (qq-eq {Δ} {Γ} A h x y ))

B-up-lm2 :  {Δ Γ : ctx}  -> (h : subst Δ Γ)
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (x  : || κ Δ ||)
    -> (y : || κ (apt (A [[ h ]]) x) ||)
    -> (z : || κ (apt (B [[ ↑ A (h) ]]) (x , y)) ||)
    -> apt (B [[ ↑ A (h) ]]) (x , y)  ‣ z  ≐ apt B ((aps h x) , y)  ‣ (e+ (B-up-lm {Δ} {Γ} h A B x y) z)
B-up-lm2 {Δ} {Γ} h A B x y z = e+prop  (B-up-lm {Δ} {Γ} h A B x y) z

B-up-down-lm :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (x  : || κ (Γ ▷ A) ||)
    -> (y : || κ (apt (A [[ (↓ A) ]]) x) ||)
    -> apt (B [[ ↑ A (↓ A) ]]) (x , y)  ≐ apt B ((aps (↓ A) x) , y)
B-up-down-lm  {Γ} A B x y = >><< (extensionality1 (ty.type B) _ (((aps (↓ A) x) , y)) (qq-eq {Γ ▷ A} {Γ} A (↓ A) x y ))


B-up-down-lm2 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (x  : || κ (Γ ▷ A) ||)
    -> (y : || κ (apt (A [[ ↓ A ]]) x) ||)
    -> (z : || κ (apt (B [[ ↑ A (↓ A) ]]) (x , y)) ||)
    -> apt (B [[ ↑ A (↓ A) ]]) (x , y)  ‣ z  ≐ apt B ((aps (↓ A) x) , y)  ‣ (e+ (B-up-down-lm {Γ} A B x y) z)
B-up-down-lm2 {Γ} A B x y z = e+prop  (B-up-down-lm  {Γ}  A B x y) z






qq-exp : {Δ Γ : ctx}
       -> (A : ty Γ)  -> (h : subst Δ Γ)
       -> (a : raw Δ)
       -> (p : (Δ  ▷ (A [[ h ]]) ==> (vv (A [[ h ]])) :: A [[ h ⌢ (↓ (A [[ h ]])) ]]))
       -> < Subst (Δ ▷ (A [[ h ]])) (Γ ▷ A) > (↑ A h) ~ (ext A (h ⌢ (↓ (A [[ h ]]))) (vv (A [[ h ]])) p)
qq-exp {Δ} {Γ} A h a p = ext-irr A (h ⌢ (↓ (A [[ h ]]))) (vv (A [[ h ]]))
             (elttyeq (asm (A [[ h ]])) (tyeq-from-eq  ((A [[ h ]]) [[ ↓ (A [[ h ]]) ]]) (A [[ h ⌢ ↓ (A [[ h ]]) ]])
                                           (Sub-comp-prop-sym A h (↓ (A [[ h ]])))
                                     )) p
