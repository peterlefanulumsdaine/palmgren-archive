-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module iterative-sets-pt7 where

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

-- quotient construction

V-extensional : (a : V) -> (R : # a -> # a -> Set) -> (pf : Eqrel (# a) R) -> Set
V-extensional a R pf = (x y : # a) -> (a ‣ x ≐ a ‣ y) -> R x y


quot : (a : V) -> (R : # a -> # a -> Set) -> (pf : Eqrel (# a) R) -> (V-extensional a R pf)
   -> V
quot a R epf xpf = sup (# a) (λ x → sup (Σ (# a) (R x)) (λ z → a ‣ (pj1 z)))

qmap-op : (a : V) -> (R : # a -> # a -> Set) -> (epf : Eqrel (# a) R)
 -> (xpf : V-extensional a R epf) -> (|| κ a ||) -> || κ (quot a R epf xpf) ||
qmap-op a R epf xpf x = x

qmap-ext : (a : V) -> (R : # a -> # a -> Set)
  -> (epf : Eqrel (# a) R)
  -> (xpf : V-extensional a R epf)
  -> (x y :  || κ a ||)
  -> < κ a > x ~ y
  ->  < κ (quot a R epf xpf) > qmap-op a R epf xpf x ~
                               qmap-op a R epf xpf y
qmap-ext a R epf xpf x y p =
  let lm2 : sup (Σ (# a) (R x)) (λ z → a ‣ (pj1 z)) ≐
            sup (Σ (# a) (R y)) (λ z → a ‣ (pj1 z))
      lm2 = pair (λ x' → ((pj1 x') ,
                  (let lm3 = pj2 x'
                   in Tra epf _ _ _ (xpf _ _ (symV (>< p))) lm3)) ,
                    refV (a ‣ pj1 x'))
                 (λ y' → ((pj1 y') ,
                   (let lm3 = pj2 y'
                    in Tra epf _ _ _ (xpf _ _  (>< p)) lm3)) ,
                    refV (a ‣ pj1 y'))
      lm :  (quot a R epf xpf) ‣ x ≐  (quot a R epf xpf) ‣ y
      lm = lm2
  in  <> lm

qmap : (a : V) -> (R : # a -> # a -> Set) -> (epf : Eqrel (# a) R)
 -> (xpf : V-extensional a R epf) -> || (κ a) => (κ (quot a R epf xpf)) ||
qmap a R epf xpf = record { op = qmap-op a R epf xpf
                          ; ext = qmap-ext a R epf xpf
                          }


qmap-prop1 : (a : V) -> (R : # a -> # a -> Set) -> (epf : Eqrel (# a) R)
  -> (xpf : V-extensional a R epf)
  -> (x y : # a) -> R x y
  ->  < κ (quot a R epf xpf) > ap (qmap a R epf xpf) x ~ ap (qmap a R epf xpf) y
qmap-prop1 a R epf xpf x y p =
   <> (pair (λ z → (
                   let
                       z2  : R x (pj1 z)
                       z2 = pj2 z
                       u1 : Σ (# a) (R y) -- (ap (qmap a R epf xpf) y) = y
                       u1 = pj1 z , Tra epf _ _ _ (Sym epf _ _ p) z2
                       main :  Σ (Σ (# a) (R (ap (qmap a R epf xpf) y)))
                                  (λ y₁ → eqV (a ‣ pj1 z) (a ‣ pj1 y₁))
                       main = u1 , refV (a ‣ pj1 z)
                   in main))
            (λ z → let
                       z2  : R y (pj1 z)
                       z2 = pj2 z
                       u1 : Σ (# a) (R x) -- (ap (qmap a R epf xpf) x) = x
                       u1 = pj1 z , Tra epf _ _ _ p z2
                       main :  Σ (Σ (# a) (R (ap (qmap a R epf xpf) x)))
                                  (λ x₁ → eqV (a ‣ pj1 x₁) (a ‣ pj1 z))
                       main = u1 , refV (a ‣ pj1 z)
                   in main
        )
                     )


qmap-prop2 : (a : V) -> (R : # a -> # a -> Set) -> (epf : Eqrel (# a) R)
  -> (xpf : V-extensional a R epf)
  -> (x y : # a)
  -> < κ (quot a R epf xpf) > ap (qmap a R epf xpf) x ~ ap (qmap a R epf xpf) y
  -> R x y
qmap-prop2 a R epf xpf x y p =
   let lm : < κ (quot a R epf xpf) > ap (qmap a R epf xpf) x ~
                                     ap (qmap a R epf xpf) y
       lm = p
       lm2 : (quot a R epf xpf) ‣ x ≐ (quot a R epf xpf) ‣ y
       lm2 = >< lm
       lm3 : sup (Σ (# a) (R x)) (λ z → a ‣ (pj1 z)) ≐
             sup (Σ (# a) (R y)) (λ z → a ‣ (pj1 z))
       lm3 = lm2
       lm4 : (x₁ : Σ (# a) (R x)) →
             Σ (Σ (# a) (R y)) (λ y₁ → eqV (a ‣ pj1 x₁) (a ‣ pj1 y₁))
       lm4 = prj1 lm3
       lm5 : R x x
       lm5 = Refl epf x
       lm6 :  Σ (Σ (# a) (R y)) (λ y₁ → eqV (a ‣ x) (a ‣ pj1 y₁))
       lm6 = lm4 (x , lm5)
       lm61 = pj1 lm6
       lm62 = pj2 lm6
       lm7 : R y (pj1 lm61)
       lm7 = pj2 lm61
       lm8 : R x (pj1 (pj1 (prj1 (>< p) (x , Refl epf x))))
       lm8 = xpf _ _ lm62

   in  Tra epf _ _ _ lm8 (Sym epf _ _ lm7)


-- representatives exists

qmap-prop3 : (a : V) -> (R : # a -> # a -> Set) -> (epf : Eqrel (# a) R)
  -> (xpf : V-extensional a R epf)
  -> (u : # (quot a R epf xpf))
  -> Σ (# a) (\x ->  < κ (quot a R epf xpf) > ap (qmap a R epf xpf) x ~ u)
qmap-prop3 a R epf xpf u = u , refl (κ (quot a R epf xpf)) u

-- universal properties

qmap-univ-map-op :  (a : V) -> (R : # a -> # a -> Set) -> (epf : Eqrel (# a) R)
    -> (xpf : V-extensional a R epf)
    -> (b : V)
    -> (f : || κ a => κ b ||)
    -> (rpf : (x y : # a) -> R x y -> < κ b > ap f x ~ ap f y)
    -> || κ (quot a R epf xpf) ||
    -> || κ b ||
qmap-univ-map-op a R epf xpf b f rpf x = ap f x

qmap-univ-map :  (a : V) -> (R : # a -> # a -> Set) -> (epf : Eqrel (# a) R)
    -> (xpf : V-extensional a R epf)
    -> (b : V)
    -> (f : || κ a => κ b ||)
    -> (rpf : (x y : # a) -> R x y -> < κ b > ap f x ~ ap f y)
    -> || κ (quot a R epf xpf) => κ b  ||
qmap-univ-map a R epf xpf b f rpf =
         record { op = qmap-univ-map-op a R epf xpf b f rpf
                ; ext = λ x y q → rpf x y
                                  (let
                                       main : R x y
                                       main = qmap-prop2 a R epf xpf x y q
                                    in main)
                }

qmap-universal :  (a : V) -> (R : # a -> # a -> Set) -> (epf : Eqrel (# a) R)
    -> (xpf : V-extensional a R epf)
    -> (b : V)
    -> (f : || κ a => κ b ||)
    -> (rpf : (x y : # a) -> R x y -> < κ b > ap f x ~ ap f y)
    -> < κ a => κ b > f ~ ((qmap-univ-map a R epf xpf b f rpf) ° (qmap a R epf xpf))
qmap-universal a R epf xpf b f rpf = <> (λ x → <>  (refV _))

qmap-epi : (a : V) -> (R : # a -> # a -> Set) -> (epf : Eqrel (# a) R)
    -> (xpf : V-extensional a R epf)
    -> (b : V)
    -> (g h : || κ (quot a R epf xpf) => κ b ||)
    -> < κ a => κ b > (g ° (qmap a R epf xpf))  ~  (h ° (qmap a R epf xpf))
    -> < κ (quot a R epf xpf) => κ b > g ~ h
qmap-epi a R epf xpf b g h cpf = <> (λ x → <> (>< (>< cpf x)))

