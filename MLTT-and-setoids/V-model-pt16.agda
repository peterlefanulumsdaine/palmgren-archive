-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt16 where

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
open import V-model-pt15


binrel-is-extensional : (A B : setoid) -> (R :  || A ||  -> || B || -> Set) -> Set
binrel-is-extensional A B R = (x x' :  || A ||) -> (y y' :  || B ||)
                          -> < A > x ~ x' -> < B > y ~ y' -> R x y -> R x' y'

ext-binrel-on :  (α : V) -> (R :  || κ α ||  -> || κ α || -> Set) -> Set
ext-binrel-on α R = binrel-is-extensional (κ α) (κ α) R




-- Quotient set α/R with universal properties

Q-set :  (α : V) -> (R :  || κ α ||  -> || κ α || -> Set) ->  V
Q-set α R =
      sup (# α)
          (\x -> sup (Σ (|| κ α ||) (\y ->  R x y))
                     (\u -> α ‣ (pj1 u)))



Q-map-op : (α : V) -> (R :  || κ α ||  -> || κ α || -> Set)
                   -> || κ α || ->  || κ (Q-set α R) ||
Q-map-op α R x  = x



Q-map-ext :  (α : V) -> (R :  || κ α ||  -> || κ α || -> Set)
                             -> ext-binrel-on α R
                             -> (x : || κ α ||)
                             -> (y : || κ α ||)
                             -> < κ α > x ~ y
                             -> < κ (Q-set α R) > Q-map-op α R x ~ Q-map-op α R y
Q-map-ext α R q x y r = <> (eqV-unexpand' _ _
                                       (λ u → (pj1 u , q _ _ _ _ r (refl _ (pj1 u)) (pj2 u)) , refV _)
                                       (λ v → (pj1 v , q _ _ _ _ (sym r) (refl _ (pj1 v)) (pj2 v)) , refV _)
                         )



Q-map :   (α : V) -> (R :  || κ α ||  -> || κ α || -> Set)
                             -> ext-binrel-on α R
                             -> setoidmap (κ α) (κ (Q-set α R))
Q-map α R r = record { op = Q-map-op α R;
                       ext = Q-map-ext α R r }



Q-map-prop1 : (α : V) -> (R :  || κ α ||  -> || κ α || -> Set)
                             -> (e : ext-binrel-on α R)
                             -> Eqrel (|| κ α ||) R
                             -> (x y :  || κ α ||)
                             -> R x y
                             ->  < κ (Q-set α R) > ap (Q-map α R e) x ~ ap (Q-map α R e) y
Q-map-prop1 α R e q x y p =
  let  lm : (Q-set α R) ‣ x ≐  (Q-set α R) ‣ y
       lm = eqV-unexpand' (Q-set α R ‣ x) (Q-set α R ‣ y)
                (λ u → let  z = pj1 u
                            lm = pj2 u
                       in  (z , (prj2 (prj2 q) _ _ _  (prj1 (prj2 q) x y p) lm)) , (refV _))
                (λ u →  let  z = pj1 u
                             lm = pj2 u
                        in (z ,  (prj2 (prj2 q) _ _ _  p lm)) , refV _)
       main : < κ (Q-set α R) > x ~ y
       main = <> lm
  in main



Q-map-prop2 : (α : V) -> (R :  || κ α ||  -> || κ α || -> Set)
                             -> (e : ext-binrel-on α R)
                             -> Eqrel (|| κ α ||) R
                             -> (x y :  || κ α ||)
                             -> < κ (Q-set α R) > ap (Q-map α R e) x ~ ap (Q-map α R e) y
                             -> R x y
Q-map-prop2 α R e q x y p =
     let rfl : R y y
         rfl = prj1 q y
         u :  Σ (Σ || κ α || (R (Q-map-op α R x)))
                  (λ x₁ → eqV (α ‣ pj1 x₁) (α ‣ y))
         u = prj2 (>< p) (y , rfl)
         u1 = pj1 (pj1 u)
         u2 :  R x u1
         u2 = pj2 (pj1 u)
         u3 : α ‣ u1 ≐ α ‣ y
         u3 = pj2 u

     in  e x x _ _ (refl _ x) (<> u3) u2



un-Q  : (α : V) -> (R :  || κ α ||  -> || κ α || -> Set)
                             -> (u :  || κ  (Q-set α R) ||)
                             -> || κ α ||
un-Q α R u = u



Q-map-prop3 : (α : V) -> (R :  || κ α ||  -> || κ α || -> Set)
                             -> (e : ext-binrel-on α R)
                             -> (u :  || κ  (Q-set α R) ||)
                             ->  < κ (Q-set α R) > u ~ ap (Q-map α R e) (un-Q α R u)
Q-map-prop3 α R e u = refl (κ (Q-set α R)) u


Q-lift-op :   (α : V) -> (R :  || κ α ||  -> || κ α || -> Set)
                -> (β : V)
                -> (f : setoidmap (κ α) (κ β))
                -> || κ  (Q-set α R) ||
                -> || κ β ||
Q-lift-op α R β f u = ap f (un-Q α R u)


Q-lift-ext :   (α : V) -> (R :  || κ α ||  -> || κ α || -> Set)
                -> ext-binrel-on α R
                -> Eqrel (|| κ α ||) R
                -> (β : V)
                -> (f : setoidmap (κ α) (κ β))
                -> ((x y :  || κ α ||) ->  (R x y) ->  < κ β > (ap f x) ~ (ap f y))
                -> (u v  : || κ (Q-set α R) ||)
                -> < κ (Q-set α R) > u ~ v
                -> < κ β > Q-lift-op α R β f u ~ Q-lift-op α R β f v
Q-lift-ext α R e q β f p u v t =
        let lm3 : R u v
            lm3 = Q-map-prop2 α R e q u v t
            main : < κ β > (ap f u) ~ (ap f v)
            main = p u v lm3
        in main --  p u v lm3


Q-lift : (α : V) -> (R :  || κ α ||  -> || κ α || -> Set)
                -> ext-binrel-on α R
                -> Eqrel (|| κ α ||) R
                -> (β : V)
                -> (f : setoidmap (κ α) (κ β))
                -> ((x y :  || κ α ||) ->  R x y ->  < κ β > (ap f x) ~ (ap f y))
                -> setoidmap (κ (Q-set α R)) (κ β)
Q-lift α R e q β f p = record { op = Q-lift-op α R β f
                              ; ext = Q-lift-ext α R e q β f p }


Q-lift-Prop1 : (α : V) -> (R :  || κ α ||  -> || κ α || -> Set)
                -> (e : ext-binrel-on α R)
                -> (q : Eqrel (|| κ α ||) R)
                -> (β : V)
                -> (f : setoidmap (κ α) (κ β))
                -> (p : ((x y :  || κ α ||) ->  R x y ->  < κ β > (ap f x) ~ (ap f y)))
                -> (z : || κ α ||)
                ->  < κ β > (ap f z)  ~ (ap (Q-lift α R e q β f p) (ap (Q-map α R e) z))
Q-lift-Prop1 α R e q β f p x = <> (refV _)

Q-lift-Prop2 : (α : V) -> (R :  || κ α ||  -> || κ α || -> Set)
                -> (e : ext-binrel-on α R)
                -> (q : Eqrel (|| κ α ||) R)
                -> (β : V)
                -> (f : setoidmap (κ α) (κ β))
                -> (p : ((x y :  || κ α ||) ->  R x y ->  < κ β > (ap f x) ~ (ap f y)))
                -> (k : setoidmap (κ (Q-set α R)) (κ β))
                -> ((z : || κ α ||)  -> < κ β >  (ap k (ap (Q-map α R e) z)) ~ (ap f z))
                -> ((u : || κ (Q-set α R) ||)  -> < κ β > (ap k u)  ~ ap (Q-lift α R e q β f p) u)
Q-lift-Prop2 α R e q β f p k m u = m u



mk-rel : (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α)) ->
              || κ α || -> || κ α || -> Set
mk-rel ρ α r1 r2 x y = Σ (|| κ ρ ||) (\t ->  and (< κ α > x  ~  ap r1 t)  (< κ α > y  ~  ap r2 t))

span-is-ext  : (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α)) ->
               ext-binrel-on α (mk-rel ρ α r1 r2)
span-is-ext ρ α r1 r2  x x' y y' e e' (p , (pair p1 p2)) =
      p , (pair (tra (sym e) p1) (tra (sym e') p2))


{-- TO DO :

-- interpreting quotient types

-- following Maietti 2005, p 1101 or the HoTT book ?

isEq : {Γ : ctx}
     -> (A : ty Γ)
     -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
     -> Set
isEq = ?

Quot : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> isEq A R
   -> ty Γ
Quot {Γ} A R = {!!}

quot : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> isEq A R
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> raw Γ
quot {Γ} A R a p = {!!}

Quot-i : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> isEq A R
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> Γ ==> quot {Γ} A R a p :: Quot {Γ} A R
Quot-i {Γ} A R a p = {!!}




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

--}
