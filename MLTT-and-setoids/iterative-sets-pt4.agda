-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module iterative-sets-pt4 where

open import basic-types
open import basic-setoids
open import dependent-setoids
open import subsetoids
open import iterative-sets
open import iterative-sets-pt2
open import iterative-sets-pt3


-- natural numbers
-- encoded as 0, {0}, {{0}}, ...

br-zeroV :  N₀ -> V
br-zeroV () 

zeroV : V
zeroV = sup N₀ br-zeroV


supN1-lm : (f g : N₁ -> V) -> (f 0₁ ≐ g 0₁) -> (sup N₁ f) ≐ (sup N₁ g)
supN1-lm f g p = easy-eqV  N₁ f g (λ x → R₁ {\y ->  f y ≐ g y } p x)


supN1-lm-rev : (f g : N₁ -> V) -> (sup N₁ f) ≐ (sup N₁ g)  -> (f 0₁ ≐ g 0₁) 
supN1-lm-rev f g p = 
  let lm = eqV-expand (sup N₁ f) (sup N₁ g) p
      lm2 = prj1 lm 0₁
      lm3 = pj2 lm2
  in traV lm3 (R₁ {\z -> sup N₁ g ‣ z ≐ g 0₁} (refV _) (pj1 (prj1 p 0₁)))


br-singV : V -> N₁ -> V
br-singV x  0₁ = x

singV : V -> V
singV x = sup N₁ (br-singV x)

singV-ext : (x y : V) 
    -> x ≐ y -> singV x ≐ singV y
singV-ext x y p = supN1-lm _ _ p

singV-inj : (x y : V) ->
   singV x ≐ singV y -> x ≐ y
singV-inj x y p = supN1-lm-rev (br-singV x)  (br-singV y) p


succV : V -> V
succV x = singV x

succV-ext : (x y : V) 
    -> x ≐ y -> succV x ≐ succV y
succV-ext x y p = singV-ext x y p

succV-inj : (x y : V) 
   -> succV x ≐ succV y  -> x ≐ y 
succV-inj x y p = singV-inj x y p

Peano4 : (x : V)
    -> succV x ≐ zeroV -> N₀
Peano4 x p = pj1 (prj1 (eqV-expand  (succV x) (zeroV) p) 0₁)


oneV : V
oneV = succV zeroV

twoV : V
twoV = succV oneV

nV : N -> V
nV O = zeroV
nV (s m) = succV (nV m)

natV : V
natV = sup N nV

zeroV-in-natV : zeroV ∈ natV
zeroV-in-natV = O , (refV _)

succ-op : || (κ natV) || ->  || (κ natV) ||
succ-op x =   s x


succ-fun : || κ natV  => κ natV ||
succ-fun = record { op = succ-op 
                  ; ext = λ x y p → <> (succV-ext (nV x) (nV y) (>< p))
                  }

succ-inj : (x y : || κ natV ||) -> (< κ natV > succ-op x ~ succ-op y) -> < κ natV > x ~  y
succ-inj x y p = <> (succV-inj _ _ (>< p)) 

-- succV-inj : (x y : V) 
--   -> succV x ≐ succV y  -> x ≐ y 

eqN : N -> N -> Set
eqN O O = True
eqN O (s y)  = False 
eqN (s x) O = False
eqN (s x) (s y) = eqN x y 

eqN-refl : (x : N) -> eqN x x
eqN-refl O = 0₁
eqN-refl (s x) = eqN-refl x


eqN-sym : (x y : N) -> eqN x y -> eqN y x
eqN-sym O O p =  p
eqN-sym O (s y) p = p
eqN-sym (s x) O p = p
eqN-sym (s x) (s y) p = eqN-sym x y p

eqN-tra : (x y z : N) -> eqN x y -> eqN y z -> eqN x z
eqN-tra O O z p q = q
eqN-tra O (s y) z p q = exfalso _ p
eqN-tra (s x) O z p q = exfalso _ p
eqN-tra (s x) (s y) O p q = q
eqN-tra (s x) (s y) (s z) p q = eqN-tra x y z p q

N-std : setoid
N-std = record { object = N 
               ; _∼_ = eqN 
               ; eqrel = pair eqN-refl (pair eqN-sym eqN-tra) }

N-to-natV-ext : (x y : || N-std ||) -> < N-std > x ~ y  -> < κ natV > x ~ y
N-to-natV-ext O O p = <> (refV _)
N-to-natV-ext O (s y) p = exfalso _ (>< p)
N-to-natV-ext (s x) O p = exfalso _ (>< p)
N-to-natV-ext (s x) (s y) p =  
    let lm : < N-std > x ~ y
        lm = <> (>< p)
        lm2 :  < κ natV > x ~ y
        lm2 = N-to-natV-ext x y lm
    in extensionality succ-fun _ _ lm2


N-to-natV : || N-std  => κ natV ||
N-to-natV = record { op = λ x → x 
                   ; ext = N-to-natV-ext }

natV-to-N-ext : (x y : || N-std ||)  -> < κ natV > x ~ y -> < N-std > x ~ y
natV-to-N-ext O O p = refl _ O
natV-to-N-ext O (s y) p = exfalso _ (Peano4 _ (symV (>< p)))
natV-to-N-ext (s x) O p = exfalso _ (Peano4 _ (>< p))
natV-to-N-ext (s x) (s y) p =
    let p' : < κ natV > x ~ y
        p' = succ-inj _ _ p
        lm :  < N-std > x ~ y
        lm = natV-to-N-ext x y p'
    in <> (>< lm)  

natV-to-N : || κ natV => N-std ||
natV-to-N = record { op = λ x → x 
                   ; ext = natV-to-N-ext }


N-isomorphism : N-std ≅ κ natV
N-isomorphism = N-to-natV , (natV-to-N  , 
                           (pair (λ x → refl (N-std) x ) (λ y → refl (κ natV) y )))

preserve-0-natV-to-N  : < N-std > ap natV-to-N O ~ O
preserve-0-natV-to-N  = refl (N-std) O
preserve-s-natV-to-N : (x : || κ natV ||) 
     ->  < N-std > ap natV-to-N (succ-op x) ~ s (ap natV-to-N x)
preserve-s-natV-to-N x = refl (N-std) _

preserve-0-N-to-natV  : < κ natV > ap N-to-natV O ~ O
preserve-0-N-to-natV  = refl (κ natV) O
preserve-s-N-to-natV : (x : || N-std ||) 
     ->  < κ natV > ap  N-to-natV (s x) ~ succ-op (ap N-to-natV x)
preserve-s-N-to-natV x = refl (κ natV) _




-- dependent recursion - what is the most natural formulation for V ?


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

natV-rec-ext : 
         (C : setoidmap1 (κ natV) VV)
      -> (d : || κ (ap1 C O) ||)
      -> (e : (m : || κ natV ||) -> (z :  || κ (ap1 C m) ||) ->  || κ (ap1 C (s m)) ||)
      -> (xt :  (m  k : || κ natV ||) -> (u :  || κ (ap1 C m) ||) -> (v :  || κ (ap1 C k) ||)
               -> < κ natV > m ~ k -> (ap1 C m) ‣ u ≐ (ap1 C k) ‣ v ->
                     (ap1 C (s m)) ‣ (e m u) ≐ (ap1 C (s k)) ‣ (e k v))
      -> (m k : || κ natV ||)
      -> (< κ natV > m ~ k)
      -> (ap1 C m) ‣ (natV-rec C d e xt m) ≐ (ap1 C k) ‣ (natV-rec C d e xt k)
natV-rec-ext C d e xt O O         p = refV _
natV-rec-ext C d e xt  O (s k)    p = exfalso _ (Peano4 (nV k) (symV (>< p)))
natV-rec-ext C d e xt (s m) O     p = exfalso _ (Peano4 (nV m) (>< p))
natV-rec-ext C d e xt (s m) (s k) p = 
        xt m k (natV-rec C d e xt m) (natV-rec C d e xt k) 
               (succ-inj _ _ p) (natV-rec-ext C d e xt m k ((succ-inj _ _ p)))


natV-rec-ext2 : 
         (C C' : setoidmap1 (κ natV) VV)
      -> (d : || κ (ap1 C O) ||)
      -> (d' : || κ (ap1 C' O) ||)
      -> (e : (m : || κ natV ||) -> (z :  || κ (ap1 C m) ||) ->  || κ (ap1 C (s m)) ||)
      -> (xt :  (m  k : || κ natV ||) -> (u :  || κ (ap1 C m) ||) -> (v :  || κ (ap1 C k) ||)
               -> < κ natV > m ~ k -> (ap1 C m) ‣ u ≐ (ap1 C k) ‣ v ->
                     (ap1 C (s m)) ‣ (e m u) ≐ (ap1 C (s k)) ‣ (e k v))
      -> (e' : (m : || κ natV ||) -> (z :  || κ (ap1 C' m) ||) ->  || κ (ap1 C' (s m)) ||)
      -> (xt' :  (m  k : || κ natV ||) -> (u :  || κ (ap1 C' m) ||) -> (v :  || κ (ap1 C' k) ||)
               -> < κ natV > m ~ k -> (ap1 C' m) ‣ u ≐ (ap1 C' k) ‣ v ->
                     (ap1 C' (s m)) ‣ (e' m u) ≐ (ap1 C' (s k)) ‣ (e' k v))

      -> (m m' : || κ natV ||)
      -> (< κ natV > m ~ m')
      -> ((ap1 C O) ‣ d ≐ (ap1 C' O) ‣ d')
      -> ((k k' : || κ natV ||) -> (z :  || κ (ap1 C k) ||) ->  (z' :  || κ (ap1 C' k') ||) ->
               (< κ natV > k ~ k') ->
               (ap1 C k) ‣ z ≐ (ap1 C' k') ‣ z' ->
               (ap1 C (s k)) ‣ (e k z) ≐ (ap1 C' (s k')) ‣ (e' k' z'))
      -> (ap1 C m) ‣ (natV-rec C d e xt m) ≐ (ap1 C' m') ‣ (natV-rec C' d' e' xt' m')
natV-rec-ext2 C C' d d' e xt e' xt' O O          p1 p2 p3 = p2
natV-rec-ext2 C C' d d' e xt e' xt' (s m) O      p1 p2 p3 = exfalso _ (Peano4 (nV m) (>< p1))
natV-rec-ext2 C C' d d' e xt e' xt' O (s m')     p1 p2 p3 = exfalso _ (Peano4 (nV m') (symV (>< p1)))
natV-rec-ext2 C C' d d' e xt e' xt' (s m) (s m') p1 p2 p3 =
      p3 m m' (natV-rec C d e xt m) (natV-rec C' d' e' xt' m') (succ-inj _ _ p1) 
                  (natV-rec-ext2 C C' d d' e xt e' xt' m m' (succ-inj _ _ p1) p2 p3)
  