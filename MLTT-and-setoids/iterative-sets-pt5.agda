-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module iterative-sets-pt5 where

open import basic-types
open import basic-setoids
open import dependent-setoids
open import subsetoids
open import iterative-sets
open import iterative-sets-pt2
open import iterative-sets-pt3
open import iterative-sets-pt4


-- Small set-theoretic universe

-- small version of V based on the TT universe U, T

-- Use only


-- data sV  : Set where
--   ssup : (A : U) -> (f : T A -> sV) -> sV

sV : (I : Set) -> (F : I -> Set)  -> Set
sV I F = W (Uo I F) (To {I} {F})

-- index and branching components

isV : (I : Set) -> (F : I -> Set)  -> sV I F -> Uo I F
isV I F (sup A f) = A

bsV : (I : Set) -> (F : I -> Set)  -> (t : sV I F) -> (To {I} {F} (isV I F t)) ->  sV I F
bsV I F (sup A f) = f

-- equality

-- fails termination check

-- eq-sV : sV -> sV -> U
-- eq-sV u v =  
--           (π (isV u) (\x -> σ (isV v) (\y -> eq-sV (bsV u x) (bsV v y))))
--            ⊗
--           (π (isV v) (\y -> σ (isV u) (\x -> eq-sV (bsV u x) (bsV v y))))

eq-sV : (I : Set) -> (F : I -> Set)  -> sV I F -> sV I F -> Uo I F
eq-sV I F (sup A f) (sup B g) =  
           (π A (\x -> σ B (\y -> eq-sV I F (f x) (g y))))
            ⊗
           (π B (\y -> σ A (\x -> eq-sV I F (f x) (g y))))



memb-sV :  (I : Set) -> (F : I -> Set) -> sV I F -> sV I F -> Uo I F
memb-sV I F u (sup B g) = σ B (\y -> eq-sV I F u (g y))

br-zero-sV :  (I : Set) -> (F : I -> Set) -> N₀ -> sV I F
br-zero-sV I F () 

zero-sV : (I : Set) -> (F : I -> Set) -> sV I F
zero-sV I F = sup n₀ (br-zero-sV I F)

br-sing-sV : (I : Set) -> (F : I -> Set) -> sV I F -> N₁ -> sV I F
br-sing-sV I F x 0₁ = x

sing-sV : (I : Set) -> (F : I -> Set) -> sV I F -> sV I F
sing-sV I F x = sup n₁ (br-sing-sV I F x)

succ-sV :  (I : Set) -> (F : I -> Set) -> sV I F -> sV I F
succ-sV I F x = sing-sV I F x

unord-sV-branch :  (I : Set) -> (F : I -> Set) -> sV I F -> sV I F -> Bool -> sV I F
unord-sV-branch I F x y (inr _) = y
unord-sV-branch I F x y (inl _)  = x



-- 

bool :  (I : Set) -> (F : I -> Set) -> Uo I F
bool I F = n₁ ⊕ n₁

unord-sV :  (I : Set) -> (F : I -> Set) -> sV I F -> sV I F -> sV I F
unord-sV I F x y = sup (bool I F) (unord-sV-branch I F x y)

pair-sV : (I : Set) -> (F : I -> Set) -> sV I F -> sV I F -> sV I F
pair-sV I F x y = unord-sV I F (unord-sV I F x x) (unord-sV I F x y)




-- embedd sV in V


emb :   (I : Set) -> (F : I -> Set) -> sV I F -> V 
emb I F (sup A f) = sup (To {I} {F} A) (\x -> emb I F (f x))

emb+ : (I : Set) -> (F : I -> Set) -> (u : sV I F) -> To {I} {F} (isV I F u) -> iV (emb I F u)
emb+ I F (sup A f) x = x

emb- : (I : Set) -> (F : I -> Set) -> (u : sV I F) -> iV (emb I F u) -> To {I} {F} (isV I F u) 
emb- I F (sup A f) x = x




emb+- : (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (x : iV (emb I F a))
    -> < κ (emb I F a) > x ~ emb+ I F a (emb- I F a x)
emb+- I F (sup A f) x = refl (κ (emb I F (sup A f))) x

emb-x :  (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (x y : iV (emb I F a)) 
   -> emb I F a ‣ x ≐ emb I F a ‣ y
   -> emb I F (bsV I F a (emb- I F a x)) ≐ emb I F (bsV I F a (emb- I F a y))
emb-x I F (sup A f) x y p = p




emb-ext : (I : Set) -> (F : I -> Set) -> (u v : sV I F) -> To {I} {F} (eq-sV I F u v) -> emb I F u ≐ emb I F v
emb-ext I F (sup A f) (sup B g) p = eqV-unexpand 
                                    (sup (To {I} {F} A) (λ x → emb I F (f x)))
                                    (sup (To {I} {F} B) (λ x → emb I F (g x)))
                                 (λ x → (pj1 (prj1 p x)) , (emb-ext I F _ _ (pj2 (prj1 p x))))
                                 (λ y → (pj1 (prj2 p y)) , (emb-ext I F _ _ (pj2 (prj2 p y))))




emb+x : (I : Set) -> (F : I -> Set) -> (a b : sV I F) -> (x : To {I} {F} (isV I F a)) -> (y : To {I} {F} (isV I F b))
      -> To {I} {F} (eq-sV I F (bsV I F a x) (bsV I F b y)) 
      -> emb I F a ‣ (emb+ I F a x) ≐ emb I F b ‣ (emb+ I F b y ) 
emb+x I F (sup A f) (sup B g) x y p = emb-ext I F _ _ p

emb-bsV : (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (x : To {I} {F} (isV I F a)) 
               -> emb I F (bsV I F a x) ≐ (emb I F a ‣ (emb+ I F a x))
emb-bsV I F (sup A f) x = refV (emb I F (f x)) 




emb-inj : (I : Set) -> (F : I -> Set) -> (u v : sV I F)  
                -> emb I F u ≐ emb I F v -> To {I} {F} (eq-sV I F u v)
emb-inj I F (sup A f) (sup B g) p = 
   let  lm : and
            ((x : # (sup (To {I} {F} A) (λ x₁ → emb I F (f x₁)))) →
              Σ (# (sup (To {I} {F} B) (λ x₁ → emb I F (g x₁))))
              (λ y →
              sup (To {I} {F} A) (λ x₁ → emb I F (f x₁)) ‣ x ≐
              sup (To {I} {F} B) (λ x₁ → emb I F (g x₁)) ‣ y))
            ((y : # (sup (To {I} {F} B) (λ x → emb I F (g x)))) →
              Σ (# (sup (To {I} {F} A) (λ x → emb I F (f x))))
             (λ x →
              sup (To {I} {F} A) (λ x₁ → emb I F (f x₁)) ‣ x ≐
              sup (To {I} {F} B) (λ x₁ → emb I F (g x₁)) ‣ y))
        lm = eqV-expand  (sup (To {I} {F} A) (λ x → emb I F (f x))) 
                         (sup (To {I} {F} B) (λ x → emb I F (g x))) p
   in pair (λ x →   pj1 (prj1 lm x) , emb-inj I F _ _ (pj2 (prj1 p x)))
           (λ x → (pj1 (prj2 lm x)) , (emb-inj I F _ _ (pj2 (prj2 p x))))




sVV :  (I : Set) -> (F : I -> Set) -> setoid
sVV I F = 
      record { object = sV I F
             ; _∼_ = λ x y → To {I} {F} (eq-sV I F x y) 
             ; eqrel = pair (λ x → emb-inj I F x x (refV (emb I F x))) 
                            (pair (λ x y p → emb-inj I F y x (symV (emb-ext I F x y p)))
                                  (λ x y z p q → emb-inj I F x z (traV (emb-ext I F x y p) (emb-ext I F y z q)))) 
             }

embVV : (I : Set) -> (F : I -> Set) -> setoidmap1 (sVV I F) VV
embVV I F = record { op = emb I F
                   ; ext = λ x y p → <<>> (emb-ext I F x y (>< p)) }



emb-memb-fwd : (I : Set) -> (F : I -> Set) -> (u v : sV I F) 
            -> To {I} {F} (memb-sV I F u v) -> emb I F u ∈ emb I F v
emb-memb-fwd I F u (sup A f) p = (pj1 p) , (emb-ext I F _ _ (pj2 p))

emb-memb-rev : (I : Set) -> (F : I -> Set) -> (u v : sV I F) 
            -> emb I F u ∈ emb I F v -> To {I} {F} (memb-sV I F u v) 
emb-memb-rev I F u (sup A f) (p1 , p2) = p1 , (emb-inj I F _ _ p2)

emb-zero : (I : Set) -> (F : I -> Set) -> emb I F (zero-sV I F) ≐ zeroV
emb-zero I F = eqV-unexpand 
                  (emb I F (zero-sV I F)) 
                  zeroV 
                  (λ x → exfalso _ x) 
                  (λ y → exfalso _ y)

emb-succ : (I : Set) -> (F : I -> Set) -> (u : sV I F) -> emb I F (succ-sV I F u) ≐ succV (emb I F u)
emb-succ I F u = supN1-lm _ _ (refV (emb I F u)) 






{--
Bool : Set
Bool = N₁ + N₁

true : Bool
true = inl 0₁

false : Bool
false = inr 0₁
--}

BoolE : {C : Bool -> Set}
   -> C true -> C false -> (c : Bool) -> C c
BoolE {C} p q (inl 0₁) = p
BoolE {C} p q (inr 0₁) = q

emb-unord : (I : Set) -> (F : I -> Set) -> (u v : sV I F) 
        -> emb I F (unord-sV I F u v) ≐ unord (emb I F u) (emb I F v)
emb-unord I F (sup A f) (sup B g) = easy-eqV Bool _ _ (BoolE (refV _) (refV _))


emb-pair : (I : Set) -> (F : I -> Set) -> (u v : sV I F) 
    -> emb I F (pair-sV I F u v) ≐ pairV (emb I F u) (emb I F v)
emb-pair I F u v = traV (emb-unord I F (unord-sV I F u u) (unord-sV I F u v))
                        (unord-ext (emb-unord I F u u) (emb-unord I F u v))

-- pair-sV : sV -> sV -> sV
-- pair-sV x y = unord-sV (unord-sV x x) (unord-sV x y)



-- uV as a subset of V

uV : (I : Set) -> (F : I -> Set) -> V
uV I F = sup (sV I F) (emb I F)



-- emb is onto uV

emb-surj-uV : (I : Set) -> (F : I -> Set) -> (u : V) -> (u ∈ uV I F) 
            -> Σ (sV I F) (\v -> emb I F v ≐ u)
emb-surj-uV I F u p = (pj1 p) , (symV (pj2 p))




-- Thus emb is an isomorphism between (sV, memb-sV) and (uV , memV | uV x uV)

tV : (I : Set) -> (F : I -> Set) -> setoidmap1 (κ (uV I F)) VV
tV I F = record { op = emb I F ;
                ext = λ x y p → <<>> (>< p) }

zeroV-in-uV : (I : Set) -> (F : I -> Set) -> zeroV ∈ uV I F
zeroV-in-uV I F =  zero-sV I F , (symV (emb-zero I F))

uV-is-succV-closed : (I : Set) -> (F : I -> Set) -> (x : V) -> (x ∈ uV I F) -> (succV x ∈ uV I F) 
uV-is-succV-closed I F x p =  (succ-sV I F (pj1 p)) , (traV (singV-ext _ _ (pj2 p)) (symV (emb-succ I F (pj1 p))))
   



n-to-sV : (I : Set) -> (F : I -> Set) -> N → sV I F
n-to-sV I F O = zero-sV I F
n-to-sV I F (s x)  = succ-sV I F (n-to-sV I F x)

nat-sV-V  :  (I : Set) -> (F : I -> Set) -> (x : N) → emb I F (n-to-sV I F x) ≐ nV x
nat-sV-V I F O = emb-zero I F
nat-sV-V I F (s x) = 
   let    ih : emb I F (n-to-sV I F x) ≐ nV x
          ih = nat-sV-V I F x
          sih :  succV (emb I F (n-to-sV I F x)) ≐ succV (nV x)
          sih = succV-ext _ _ ih
          lm2 : emb I F (n-to-sV I F (s x)) ≐ emb I F (succ-sV I F (n-to-sV I F x)) 
          lm2 = emb-ext I F (n-to-sV I F (s x)) (succ-sV I F (n-to-sV I F x)) 
                      (emb-inj I F (n-to-sV I F (s x)) (succ-sV I F (n-to-sV I F x)) (refV _))  

-- emb-inj : (u v : sV)  -> emb u ≐ emb v -> T (eq-sV u v)
-- emb-ext : (u v : sV) -> T (eq-sV u v) -> emb u ≐ emb v
          lm : emb I F (n-to-sV I F (s x)) ≐ succV (emb I F (n-to-sV I F x))
          lm = traV lm2 (emb-succ I F _)
          main :  emb I F (n-to-sV I F (s x))  ≐  succV (nV x)
          main = traV lm sih
   in main


nat-sV :  (I : Set) -> (F : I -> Set) -> sV I F
nat-sV I F = sup n (n-to-sV I F)

emb-nat :  (I : Set) -> (F : I -> Set) -> emb I F (nat-sV I F) ≐ natV
emb-nat I F = easy-eqV N _ _ (nat-sV-V I F)



natV-in-uV : (I : Set) -> (F : I -> Set) -> natV ∈ uV I F
natV-in-uV I F = nat-sV I F , symV (emb-nat I F)



fnk : (I : Set) -> (F : I -> Set) -> (a : V) -> (p1 : # (uV I F)) 
           -> (p2 :  a ≐ (uV I F) ‣ p1 ) -> To {I} {F} (isV I F p1) -> || κ a ||
fnk I F (sup B g) (sup A f) p2 x =  e+ (symV p2) x

bnk : (I : Set) -> (F : I -> Set) -> (a : V) -> (p1 : # (uV I F)) 
           -> (p2 :  a ≐ (uV I F) ‣ p1 ) ->  || κ a || -> To {I} {F} (isV I F p1)
bnk I F (sup B g) (sup A f) p2 x =  e+  p2 x

fnkbnk-eq : (I : Set) -> (F : I -> Set) -> (a : V) -> (p1 : # (uV I F)) 
          -> (p2 :  a ≐ (uV I F) ‣ p1 ) -> (x : || κ a ||) 
          -> a ‣ (fnk I F a p1 p2 (bnk I F a p1 p2 x)) ≐ a ‣ x
fnkbnk-eq I F (sup B g) (sup A f) p2 x = 
         traV (e+fun p2 (symV p2) (refV (sup B g)) x) 
              (symV (e+prop (refV (sup B g)) x)) 




-- emb-surj-uV : (u : V) -> (u ∈ uV) -> Σ sV (\v -> emb v ≐ u)
-- emb-surj-uV u p = (pj1 p) , (symV (pj2 p))


-- bnkfnk-eq : (a : V) -> (p1 : # uV) -> (p2 :  a ≐ uV ‣ p1 ) -> (x : || κ a ||) 
--          -> {! uV ‣ p1 ‣ (bnk a p1 p2 (fnk a p1 p2 x)) ≐ uV ‣ p1 ‣ x!}
-- bnkfnk-eq (sup B g) (ssup A f) p2 x = {!!}

-- e+fun : {u v z : V} -> (p : u ≐ v) -> (q : v ≐ z) ->  (r : u ≐ z)
--      -> (x : # u)  ->  z ‣ (e+ q (e+ p x)) ≐ z ‣ (e+ r x)
-- e+prop : {u v : V} -> (p : u ≐ v)
--      -> (x : # u) -> u ‣ x ≐ v ‣ (e+ p x)


-- compare:
--
-- sigmaV : (a : V) -> (g :  setoidmap1 (κ a) VV) -> V
-- sigmaV a g =  sup (Σ (# a) (\y -> # (g • y))) 
--                     (\u -> < a ‣ (pj1 u) , (g • (pj1 u)) ‣ (pj2 u) >)

-- embVV : setoidmap1 sVV VV


-- comp1 : {A B : setoid} -> {C : classoid} -> (f : setoidmap1 B C) -> (g : || A => B ||) -> setoidmap1 A C


sigma-sV :  (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (g : setoidmap (κ (emb I F a)) (sVV I F)) -> sV I F
sigma-sV I F a g = sup  (σ (isV I F a) (λ y → isV I F (ap g (emb+ I F a y))))
                        (λ u → pair-sV I F (bsV I F a (pj1 u)) (bsV I F (ap g (emb+ I F a (pj1 u))) (pj2 u)))


 

emb-sigma-sV-half1-lm2 :   (I : Set) -> (F : I -> Set) -> (z : sV I F) -> (u2 : To {I} {F} (isV I F z))
   ->  emb I F (bsV I F z u2) ≐ ap1 (embVV I F) z ‣ (emb+ I F z u2)
emb-sigma-sV-half1-lm2 I F (sup A f) u2 = refV (emb I F (f u2))


emb-sigma-sV-half1-lm :  (I : Set) -> (F : I -> Set) -> (A  : Uo I F) -> (f  : To {I} {F} A -> sV I F) 
    -> (g  : setoidmap (κ (sup (To {I} {F} A) (λ x → emb I F (f x)))) (sVV  I F))
    -> (u1 : To {I} {F} A) -> (u2 : To {I} {F} (isV I F (ap g u1))) 
    ->  emb I F (bsV I F (ap g u1) u2) ≐
        ap1 (embVV I F) (ap g u1) ‣ emb+ I F (ap g u1) u2
emb-sigma-sV-half1-lm I F  A f g u1 u2 = emb-sigma-sV-half1-lm2 I F (ap g u1) u2



emb-sigma-sV-half1 :  (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (g : setoidmap (κ (emb I F a)) (sVV I F))
      -> emb I F (sigma-sV I F a g) ≤ sigmaV (emb I F a) (comp1 (embVV I F) g)
emb-sigma-sV-half1 I F (sup A f) g (u1 , u2) =
  let lm2 : emb I F (bsV I F (ap g u1) u2) ≐ (ap1 (embVV I F) (ap g  u1)) ‣ emb+ I F (ap g u1) u2
      lm2 = emb-sigma-sV-half1-lm I F A f g u1 u2
      lm : emb I F (bsV I F (ap g u1) u2) ≐ (comp1 (embVV I F) g • u1) ‣ emb+ I F (ap g u1) u2
      lm = lm2
  in (u1 , (emb+ I F (ap g u1) u2)) , 
     traV (emb-pair I F _ _) 
          (pairV-ext (refV (emb I F (f u1))) 
                     lm)



emb-sigma-sV-half2-lm2 :  (I : Set) -> (F : I -> Set) -> (z : sV I F) -> (u2 : # (ap1 (embVV I F) z))
   ->  emb I F (bsV I F z (emb- I F z u2)) ≐ ap1 (embVV I F) z ‣ u2
emb-sigma-sV-half2-lm2 I F (sup A f) u2 = refV (emb I F (f u2))

emb-sigma-sV-half2-lm :  (I : Set) -> (F : I -> Set) -> (A : Uo I F) -> (f  : To {I} {F} A -> sV I F) 
    -> (g  : setoidmap (κ (sup (To {I} {F} A) (λ x → emb I F (f x)))) (sVV I F))
    -> (u1 : To {I} {F} A) -> (u2 : # (comp1 (embVV I F) g • u1)) 
    -> emb I F (bsV I F (ap g u1) (emb- I F (ap g u1) u2)) ≐
        ap1 (embVV I F) (ap g u1) ‣ u2
emb-sigma-sV-half2-lm I F A f g u1 u2 = emb-sigma-sV-half2-lm2 I F (ap g u1) u2



emb-sigma-sV-half2 :  (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (g : setoidmap (κ (emb I F a)) (sVV I F))
      -> emb I F (sigma-sV I F a g) ≥ sigmaV (emb I F a) (comp1 (embVV I F) g)
emb-sigma-sV-half2 I F (sup A f) g (u1 , u2) = 
  let lm2 :  emb I F (bsV I F (ap g u1) (emb- I F (ap g u1) u2)) ≐  (ap1 (embVV I F) (ap g  u1)) ‣ u2
      lm2 = emb-sigma-sV-half2-lm I F A f g u1 u2
      lm : emb I F (bsV I F (ap g u1) (emb- I F (ap g u1) u2)) ≐ (comp1 (embVV I F) g • u1) ‣ u2 
      lm = lm2
  in
     (u1 , emb-  I F (ap g u1) u2) , 
     traV (emb-pair I F _ _) 
          (pairV-ext (refV (emb I F (f u1))) lm)

emb-sigma-sV : (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (g : setoidmap (κ (emb  I F a)) (sVV I F))
      -> emb I F (sigma-sV  I F a g) ≐ sigmaV (emb  I F a) (comp1 (embVV I F) g)
emb-sigma-sV I F a g = pair (emb-sigma-sV-half1 I F a g)  (emb-sigma-sV-half2 I F a g) 





pi-sV-iV : (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (g :  setoidmap (κ (emb  I F a)) (sVV I F)) -> Uo I F
pi-sV-iV I F a g = σ (π (isV I F a) (λ y → isV I F (ap g (emb+ I F a y))))
                     (λ f → π (isV I F a) (λ x → 
                            π (isV I F a) (λ y → 
                            π (eq-sV I F (bsV I F a x) (bsV I F a y)) 
                                     (λ p → eq-sV I F (bsV I F (ap g (emb+ I F a x)) (f x))
                                                                       (bsV I F (ap g (emb+ I F a y)) (f y))))))

pi-sV-bV : (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (g :  setoidmap (κ (emb I F a)) (sVV I F)) 
          ->  To {I} {F} (pi-sV-iV I F a g) -> sV I F
pi-sV-bV I F a g h =  sup (isV I F a) (λ x → pair-sV I F (bsV I F a x) (bsV I F (ap g (emb+ I F a x)) (pj1 h x)))

pi-sV : (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (g :  setoidmap (κ (emb I F a)) (sVV I F)) -> sV I F
pi-sV I F a g = sup (pi-sV-iV I F a g) (pi-sV-bV I F a g)





emb-pi-sV-half1-ix-fn :  (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (g : setoidmap (κ (emb I F a)) (sVV I F)) 
    ->  To {I} {F} (pi-sV-iV I F a g) ->  (x : # (emb I F a)) → # (comp1 (embVV I F) g • x)
emb-pi-sV-half1-ix-fn I F a g (f , fx) x = 
  let lm  : To {I} {F} (isV I F (ap g (emb+ I F a (emb- I F a x))))
      lm = f (emb- I F a x)
      lm3 : To {I} {F} (eq-sV I F (ap g x) (ap g (emb+ I F a (emb- I F a x))))
      lm3 = >< (extensionality g x (emb+ I F a (emb- I F a x)) (emb+- I F a x))
      lm4 : emb I F (ap g x) ≐ emb I F (ap g (emb+ I F a (emb- I F a x)))
      lm4 = emb-ext I F _ _ lm3
      lm2 : # (emb I F (ap g x))
      lm2 = e+ (symV lm4) (emb+ I F (ap g (emb+ I F a (emb- I F a x))) lm) 
      main : # (comp1 (embVV I F) g • x)
      main = lm2
  in main

-- emb-ext : (u v : sV) -> T (eq-sV u v) -> emb u ≐ emb v

-- emb+ : (u : sV) -> T (isV u) -> iV (emb u)
-- emb+ (ssup A f) x = x

-- emb- : (u : sV) -> iV (emb u) -> T (isV u) 
-- emb- (ssup A f) x = x

-- emb : sV -> V
-- emb (ssup A f) = sup (T A) (\x -> emb (f x))

-- emb-pi-sV-half1-ix-fn : (a : sV) -> (g : setoidmap (κ (emb a)) sVV) 
--    ->  T (pi-sV-iV a g)

-- emb-inj : (u v : sV)  -> emb u ≐ emb v -> T (eq-sV u v)
-- emb-x : (a : sV) -> (x y : iV (emb a)) 
--   -> emb a ‣ x ≐ emb a ‣ y
--   -> emb (bsV a (emb- a x)) ≐ emb (bsV a (emb- a y))





ag-setoid-lm :  (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (g : setoidmap (κ (emb I F a)) (sVV I F)) 
          -> (y : # (emb I F a))
          -> (u v :  || κ° (comp1 (embVV  I F) g) § y ||)
          -- -> < κ (emb I F (ap g y)) > u ~ v
          -> (emb I F (ap g y)) ‣ u ≐ (emb I F (ap g y)) ‣ v
          -> < κ° (comp1 (embVV I F) g) § y > u ~ v
ag-setoid-lm I F a g y u v p = <> p




κ-trp-fn2 : {a b  c : V} -> (q : b ≐ c) -> (p : a ≐ b) 
      -> (x : || κ a ||)
      ->  < κ c >   κ-trp-op q (κ-trp-op p x) ~ κ-trp-op (traV p q) x 
κ-trp-fn2 {a} {b} {c} q p x = sym (κ-trp-fn q p (traV p q) x)

κ-trp-ext-irr : {a b : V} -> (p q : a ≐ b) ->  (x y : || κ a ||)
      ->  < κ a > x ~ y ->  < κ b > κ-trp-op p x ~ κ-trp-op q y
κ-trp-ext-irr {a} {b} p q x y r = <> (traV (traV (symV (e+prop p x)) (>< r)) (e+prop q y))
 
κ-trp-ext-irr2 : {a b c : V} -> (p : a ≐ c) -> (q : b ≐ c) ->  (x : || κ a ||)
           ->  (y : || κ b ||)  ->  a ‣ x ≐ b ‣ y ->  < κ c > κ-trp-op p x ~ κ-trp-op q y
κ-trp-ext-irr2 {a} {b} {c} p q x y r =  <> (traV (traV (symV (e+prop p x)) r) (e+prop q y))



emb-pi-sV-half1-ix : (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (g : setoidmap (κ (emb I F a)) (sVV I F)) 
      -> To {I} {F} (pi-sV-iV I F a g) -> piV-iV (emb I F a) (comp1 (embVV I F) g) 
emb-pi-sV-half1-ix I F a g (f , fx) = 
       emb-pi-sV-half1-ix-fn I F a g (f , fx) ,
       (λ x y p → 
       let p' : (emb I F a) ‣ x ≐  (emb I F a) ‣ y
           p' = >< p
           lmq : To {I} {F} (eq-sV I F (bsV I F a (emb- I F a x)) (bsV I F a (emb- I F a y)))
           lmq = emb-inj I F (bsV I F a (emb- I F a x)) (bsV I F a (emb- I F a y)) (emb-x I F a _ _ p')
           lmx : To {I} {F} (eq-sV I F (bsV I F (ap g (emb+ I F a (emb- I F a x))) (f (emb- I F a x)))
                          (bsV I F (ap g (emb+ I F a (emb- I F a y))) (f (emb- I F a y))))   
           lmx = fx (emb- I F a x) (emb- I F a y) lmq
           lmx1 : emb I F (ap g (emb+ I F a (emb- I F a x))) ‣
                   emb+ I F (ap g (emb+ I F a (emb- I F a x))) (f (emb- I F a x))
                     ≐
                  emb I F (ap g (emb+ I F a (emb- I F a y))) ‣
                    emb+ I F (ap g (emb+ I F a (emb- I F a y))) (f (emb- I F a y))
           lmx1 = emb+x I F (ap g (emb+ I F a (emb- I F a x))) (ap g (emb+ I F a (emb- I F a y))) 
                    (f (emb- I F a x))  (f (emb- I F a y)) lmx
           lmx2 : emb I F (bsV I F (ap g (emb+ I F a (emb- I F a x))) (f (emb- I F a x))) 
                   ≐ emb I F (bsV I F (ap g (emb+ I F a (emb- I F a y))) (f (emb- I F a y)))
           lmx2 = traV (emb-bsV I F (ap g (emb+ I F a (emb- I F a x))) (f (emb- I F a x)))
                       (traV lmx1 (symV (emb-bsV I F (ap g (emb+ I F a (emb- I F a y))) (f (emb- I F a y))))) 
           tsp1 : emb I F (ap g (emb+ I F a (emb- I F a x))) ≐ emb I F (ap g y) -- comp1 (embVV I F) g • y
           tsp1 = (traV
                 (symV
                  (emb-ext I F (ap g x) (ap g (emb+ I F a (emb- I F a x)))
                   (>< (extensionality g x (emb+ I F a (emb- I F a x)) (emb+- I F a x)))))
                 (>><< (extensionality1 (comp1 (embVV I F) g) x y p)))
           tsp2 : emb I F (ap g (emb+ I F a (emb- I F a y))) ≐ emb I F (ap g y)
           tsp2 = (symV
                 (emb-ext I F (ap g y) (ap g (emb+ I F a (emb- I F a y)))
                  (>< (extensionality g y (emb+ I F a (emb- I F a y)) (emb+- I F a y)))))

           lm4 :  < κ (comp1 (embVV I F) g • y) >
                κ-trp-op
                (traV
                 (symV
                  (emb-ext I F (ap g x) (ap g (emb+ I F a (emb- I F a x)))
                   (>< (extensionality g x (emb+ I F a (emb- I F a x)) (emb+- I F a x)))))
                 (>><< (extensionality1 (comp1 (embVV I F) g) x y p)))
                (emb+ I F (ap g (emb+ I F a (emb- I F a x))) (f (emb- I F a x)))
                ~
                κ-trp-op
                (symV
                 (emb-ext I F (ap g y) (ap g (emb+ I F a (emb- I F a y)))
                  (>< (extensionality g y (emb+ I F a (emb- I F a y)) (emb+- I F a y)))))
                (emb+ I F (ap g (emb+ I F a (emb- I F a y))) (f (emb- I F a y)))
           lm4 = κ-trp-ext-irr2 tsp1 tsp2 
                   (emb+ I F (ap g (emb+ I F a (emb- I F a x))) (f (emb- I F a x))) 
                   (emb+ I F (ap g (emb+ I F a (emb- I F a y))) (f (emb- I F a y))) lmx1
           lm3 :  < κ (comp1 (embVV I F) g • y) >
                κ-trp-op
                (traV
                 (symV
                  (emb-ext I F (ap g x) (ap g (emb+ I F a (emb- I F a x)))
                   (>< (extensionality g x (emb+ I F a (emb- I F a x)) (emb+- I F a x)))))
                 (>><< (extensionality1 (comp1 (embVV I F) g) x y p)))
                (emb+ I F (ap g (emb+ I F a (emb- I F a x))) (f (emb- I F a x)))
                ~
                e+
                (symV
                 (emb-ext I F (ap g y) (ap g (emb+ I F a (emb- I F a y)))
                  (>< (extensionality g y (emb+ I F a (emb- I F a y)) (emb+- I F a y)))))
                (emb+ I F (ap g (emb+ I F a (emb- I F a y))) (f (emb- I F a y)))
           lm3 = lm4


           main : < κ° (comp1 (embVV I F) g) § y >
                ap (κ° (comp1 (embVV I F) g) ± p)
               (e+
                (symV
                 (emb-ext I F (ap g x) (ap g (emb+ I F a (emb- I F a x)))
                  (>< (extensionality g x (emb+ I F a (emb- I F a x)) (emb+- I F a x)))))
                (emb+ I F (ap g (emb+ I F a (emb- I F a x))) (f (emb- I F a x))))
               ~
               e+
               (symV
                (emb-ext I F (ap g y) (ap g (emb+ I F a (emb- I F a y)))
                 (>< (extensionality g y (emb+ I F a (emb- I F a y)) (emb+- I F a y)))))
               (emb+ I F (ap g (emb+ I F a (emb- I F a y))) (f (emb- I F a y)))
           main = tra (κ-trp-fn2 _ (symV
                 (emb-ext I F (ap g x) (ap g (emb+ I F a (emb- I F a x)))
                  (>< (extensionality g x (emb+ I F a (emb- I F a x)) (emb+- I F a x)))))  
                         (emb+ I F (ap g (emb+ I F a (emb- I F a x))) (f (emb- I F a x))))
                  lm3
                       
       in main)



emb-pi-sV-half1 :  (I : Set) -> (F : I -> Set) -> (a : sV I F) -> (g : setoidmap (κ (emb I F a)) (sVV I F))
      -> emb I F (pi-sV I F a g) ≤ piV (emb I F a) (comp1 (embVV I F) g)
emb-pi-sV-half1 I F (sup A f) g (h , hx) = 
  let lm2 : (x : To {I} {F} A) -> 
         emb I F (pair-sV I F (bsV I F (sup A f) x) (bsV I F (ap g (emb+ I F (sup A f) x)) (h x)))
                  ≐ < (emb I F (sup A f)) ‣ x , 
                    (ap1 (comp1 (embVV I F) g) x) ‣ (pj1 (emb-pi-sV-half1-ix I F (sup A f) g (h , hx)) x)   >
                   
      lm2 = λ x → traV (emb-pair I F _ _) 
                       (pairV-ext (refV (emb I F (f x))) 
                                  (traV (emb-bsV I F (ap g x) (h x)) 
                                        ((e+prop (symV
                                                   (emb-ext I F (ap g x) (ap g x)
                                                    (><
                                                     (extensionality g x x
                                                      (refl (κ (sup (To {I} {F} A) (λ x₁ → emb I F (f x₁)))) x))))) 
                                                 (emb+ I F (ap g x) (h x))))))
  

      lm : (emb I F (pi-sV I F (sup A f) g)) ‣ (h , hx) ≐ 
             (piV (emb I F (sup A f)) (comp1 (embVV I F) g)) ‣ (emb-pi-sV-half1-ix I F (sup A f) g (h , hx))
      lm = easy-eqV (To {I} {F} A) _ _ lm2 
  in 
         emb-pi-sV-half1-ix  I F (sup A f) g (h , hx) ,  lm




emb-pi-sV-half2-ix-fn :  (I : Set) -> (F : I -> Set) 
    -> (a : sV I F) -> (g : setoidmap (κ (emb I F a)) (sVV I F)) 
    ->   piV-iV (emb I F a) (comp1 (embVV I F) g) -> (x : To {I} {F} (isV I F a)) 
    -> To {I} {F} (isV I F (ap g (emb+ I F a x)))
emb-pi-sV-half2-ix-fn I F a g (h , hx) x = 
   let h' :  # (emb I F (ap g (emb+ I F a x)))
       h' = h (emb+ I F a x)
       main :  To {I} {F} (isV I F (ap g (emb+ I F a x)))
       main = emb- I F (ap g (emb+ I F a x)) h'
   in main 



emb-pi-sV-half2-ix :  (I : Set) -> (F : I -> Set) 
      -> (a : sV I F) -> (g : setoidmap (κ (emb I F a)) (sVV I F)) 
      -> piV-iV (emb I F a) (comp1 (embVV I F) g) -> To {I} {F} (pi-sV-iV I F a g)
emb-pi-sV-half2-ix I F a g (h , hx) =  
     emb-pi-sV-half2-ix-fn  I F a g (h , hx) ,
      (λ x y p -> 
         let p'' : emb I F (bsV I F a x) ≐ emb I F (bsV I F a y)
             p'' = emb-ext I F _ _ p 
             p' = < κ (emb I F a) > emb+ I F a x ~ emb+ I F a y
             p' = <> (traV (symV (emb-bsV I F a x)) (traV p'' (emb-bsV I F a y)))
             hx' : < κ (emb I F (ap g (emb+ I F a y))) > 
                     (ap  (κ° (comp1 (embVV I F) g) ±
                     (<> (traV (symV (emb-bsV I F a x))
                        (traV (emb-ext I F (bsV I F a x) (bsV I F a y) p) (emb-bsV I F a y)))))
                          (h (emb+ I F a x)))  
                     ~ (h (emb+ I F a y)) 
             hx' = hx (emb+ I F a x) (emb+ I F a y) p'
             hx2 : (emb I F (ap g (emb+ I F a y))) ‣
                     (ap  (κ° (comp1 (embVV I F) g) ±
                     (<> (traV (symV (emb-bsV I F a x))
                        (traV (emb-ext I F (bsV I F a x) (bsV I F a y) p) (emb-bsV I F a y)))))
                          (h (emb+ I F a x)))  
                          ≐
                   (emb I F (ap g (emb+ I F a y))) ‣ (h (emb+ I F a y))
             hx2 = >< hx'
             lm4 :  (emb I F (ap g (emb+ I F a x))) ‣  (h (emb+ I F a x))
                          ≐
                    (emb I F (ap g (emb+ I F a y))) ‣
                     (ap  (κ° (comp1 (embVV I F) g) ±
                     (<> (traV (symV (emb-bsV I F a x))
                        (traV (emb-ext I F (bsV I F a x) (bsV I F a y) p) (emb-bsV I F a y)))))
                          (h (emb+ I F a x))) 
             lm4 = e+prop {emb I F (ap g (emb+ I F a x))} {emb I F (ap g (emb+ I F a y))} _ (h (emb+ I F a x))  

             lm3 : (emb I F (ap g (emb+ I F a x))) ‣ 
                    (emb+ I F (ap g (emb+ I F a x)) (emb- I F (ap g (emb+ I F a x)) (h (emb+ I F a x))))
                          ≐
                   (emb I F (ap g (emb+ I F a y))) ‣
                     (ap  (κ° (comp1 (embVV I F) g) ±
                     (<> (traV (symV (emb-bsV I F a x))
                        (traV (emb-ext I F (bsV I F a x) (bsV I F a y) p) (emb-bsV I F a y)))))
                          (h (emb+ I F a x)))  
             lm3 = traV (symV (>< (emb+- I F (ap g (emb+ I F a x)) _))) lm4    
             lm2 : (emb I F (ap g (emb+ I F a x))) ‣ 
                    (emb+ I F (ap g (emb+ I F a x)) (emb- I F (ap g (emb+ I F a x)) (h (emb+ I F a x))))
                          ≐
                   (emb I F (ap g (emb+ I F a y))) ‣ 
                    (emb+ I F (ap g (emb+ I F a y)) (emb- I F (ap g (emb+ I F a y)) (h (emb+ I F a y))))
             lm2 = traV (traV lm3 hx2) (>< (emb+- I F (ap g (emb+ I F a y)) (h (emb+ I F a y))))
             lm : emb I F (bsV I F (ap g (emb+ I F a x)) (emb- I F (ap g (emb+ I F a x)) (h (emb+ I F a x)))) 
                ≐ emb I F (bsV I F (ap g (emb+ I F a y)) (emb- I F (ap g (emb+ I F a y)) (h (emb+ I F a y))))
             lm = traV (emb-bsV I F (ap g (emb+ I F a x)) _) (traV lm2 (symV (emb-bsV I F (ap g (emb+ I F a y)) _)))
             main : To {I} {F} (eq-sV I F
                       (bsV I F (ap g (emb+ I F a x)) (emb- I F (ap g (emb+ I F a x)) (h (emb+ I F a x))))
                       (bsV I F (ap g (emb+ I F a y)) (emb- I F (ap g (emb+ I F a y)) (h (emb+ I F a y)))))
             main = emb-inj I F _ _ lm
         in main 

      )


emb-pi-sV-half2 :  (I : Set) -> (F : I -> Set) 
      -> (a : sV I F) -> (g : setoidmap (κ (emb I F a)) (sVV I F))
      -> emb I F (pi-sV I F a g) ≥ piV (emb I F a) (comp1 (embVV I F) g)
emb-pi-sV-half2 I F (sup A f) g (h , hx) = 
 
  let lm2 : (x : To {I} {F} A) -> emb I F (pair-sV I F (bsV I F (sup A f) x) (bsV I F (ap g (emb+ I F (sup A f) x)) 
                                (pj1 (emb-pi-sV-half2-ix I F (sup A f) g (h , hx)) x)))
                  ≐ < (emb I F (sup A f)) ‣ x , 
                    (ap1 (comp1 (embVV I F) g) x) ‣ (h x)   >
                   
      lm2 = λ x -> traV (emb-pair I F _ _) 
                        (pairV-ext (refV (emb I F (f x))) 
                                   (traV (emb-bsV I F (ap g x) (emb- I F (ap g x) (h x))) 
                                         (symV (>< (emb+- I F (ap g x) (h x))) ))) 


      lm : (emb I F (pi-sV I F (sup A f) g)) ‣ (emb-pi-sV-half2-ix I F (sup A f) g (h , hx))
           ≐ (piV (emb I F (sup A f)) (comp1 (embVV I F) g)) ‣ (h , hx)
      lm = easy-eqV (To {I} {F} A) _ _ lm2
  in 
         (emb-pi-sV-half2-ix I F (sup A f) g (h , hx)) ,  lm





emb-pi-sV :  (I : Set) -> (F : I -> Set) 
      -> (a : sV I F) -> (g : setoidmap (κ (emb I F a)) (sVV I F))
      -> emb I F (pi-sV I F a g) ≐ piV (emb I F a) (comp1 (embVV I F) g)
emb-pi-sV I F a g = pair (emb-pi-sV-half1 I F a g)  (emb-pi-sV-half2 I F a g) 





