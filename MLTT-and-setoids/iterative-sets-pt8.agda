-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module iterative-sets-pt8 where

open import basic-types
open import basic-setoids
open import dependent-setoids
open import subsetoids
open import iterative-sets
open import iterative-sets-pt2
open import iterative-sets-pt3
open import iterative-sets-pt4
open import iterative-sets-pt5 -- wop = use universe operator and W
open import iterative-sets-pt6


-- Squashed sets.

--- sq : sup A f  |-> sup A (\x -> 0)


-- br-zeroV :  N₀ -> V
-- br-zeroV () 

-- zeroV : V
-- zeroV = sup N₀ br-zeroV

-- singV : V -> V
-- singV x = sup N₁ (br-singV x)


sqV : V -> V
sqV u = sup (# u) (\x -> zeroV)

sqV-prop-1 : (u : V) -> (v : V) -> v ∈ sqV u -> v ≐ zeroV
sqV-prop-1 (sup A f) v (p1 , p2) = p2

sqV-prop-2 : (u : V) -> (v : V) -> v ∈ sqV u -> Σ10 V (\z -> z ∈ u)
sqV-prop-2 (sup A f) v (p1 , p2) = sup A f ‣ p1 , (p1 , refV _)

sqV-prop-3 :  (u : V) -> sqV u ≤ singV zeroV
sqV-prop-3 u x = 0₁ , refV _

sqV-ext-half : (a b : V) -> a ≤ b -> sqV a ≤ sqV b
sqV-ext-half (sup A f) (sup B g) p  x = 
    let p1 = pj1 (p x)
        p2 = pj2 (p x)
    in p1 , refV _

-- eqV-unexpand' : (u v : V) ->   (u ≤ v) -> (u ≥ v) ->  (u ≐ v) 



≥-≤-lm : (a b : V) -> a ≥ b -> b ≤ a
≥-≤-lm (sup A f)  (sup B g) p = λ x → (pj1 (p x)) , (symV (pj2 (p x)))

singV-zeroV-lm : (x : # (singV zeroV)) -> singV zeroV ‣ x ≐ zeroV
singV-zeroV-lm 0₁ = refV _

sqV-prop-4 : (u : V) -> u ≤ singV zeroV -> sqV u ≐ u
sqV-prop-4 (sup A f) p =  
       eqV-unexpand' (sqV (sup A f)) (sup A f) 
                (λ x → x , (let  px = p x
                                 px2 = pj2 px
                                 lm : sup A f ‣ x ≐ zeroV
                                 lm = traV px2 (singV-zeroV-lm (pj1 (p x)))
                                 main : sqV (sup A f) ‣ x ≐ sup A f ‣ x
                                 main = symV lm
                            in main
                             )) 
                (λ y → y , (let  py = p y
                                 py2 = pj2 py
                                 lm : sup A f ‣ y ≐ zeroV
                                 lm = traV py2 (singV-zeroV-lm (pj1 (p y)))
                                 main : sqV (sup A f) ‣ y ≐ sup A f ‣ y
                                 main = symV lm
                            in main))


sqV-prop-5 :  (u : V) -> sqV (sqV u) ≐ sqV u
sqV-prop-5 u = sqV-prop-4 (sqV u) (sqV-prop-3 u)

sqV-ext : (a b : V) -> a ≐ b -> sqV a ≐ sqV b
sqV-ext a b p = pair (sqV-ext-half a b (prj1 (eqV-expand' a b p))) 
                     (sqV-ext-half b a (≥-≤-lm a b (prj2 (eqV-expand' a b p)))) 



sqV-sV : (I : Set) -> (F : I -> Set) 
           -> (u : sV I F) -> sV I F
sqV-sV I F u =  sup (isV I F u) (\x -> zero-sV I F)


{--


emb :   (I : Set) -> (F : I -> Set) -> sV I F -> V 
emb I F (sup A f) = sup (To {I} {F} A) (\x -> emb I F (f x))

emb+ : (I : Set) -> (F : I -> Set) -> (u : sV I F) -> To {I} {F} (isV I F u) -> iV (emb I F u)
emb+ I F (sup A f) x = x

emb- : (I : Set) -> (F : I -> Set) -> (u : sV I F) -> iV (emb I F u) -> To {I} {F} (isV I F u) 
emb- I F (sup A f) x = x


uV : (I : Set) -> (F : I -> Set) -> V
uV I F = sup (sV I F) (emb I F)

--}


sqV-reflection-lm-half1 : (I : Set) -> (F : I -> Set) 
              -> (a : V) 
              -> (p : a ∈ uV I F) 
              -> sqV a ≤ uV I F ‣ sqV-sV I F (pj1 p)
sqV-reflection-lm-half1 I F (sup A f) (p1 , p2) x =
      let  lm5 = prj1 (eqV-expand' _ _ p2)
           lm : # (uV I F ‣ sqV-sV I F p1) 
              -- # (emb I F (sqV-sV I F p1))
              -- # (emb I F (sup (isV I F p1) (\x -> zero-sV I F))) 
              -- To {I} {F}  (isV I F p1)
               
              -- sqV-sV I F u =  sup (isV I F u) (\x -> zero-sV I F)
           lm = emb- I F p1 (pj1 (lm5 x))
           lm4 : sqV (sup A f) ‣ x ≐  zeroV
           lm4 = refV _
           lm3 :  uV I F ‣ sqV-sV I F p1 ‣
                       emb- I F p1 (pj1 (prj1 (eqV-expand' (sup A f) (emb I F p1) p2) x))
                  ≐ emb I F (sqV-sV I F p1) ‣
                       emb- I F p1 (pj1 (prj1 (eqV-expand' (sup A f) (emb I F p1) p2) x))
           lm3 = refV _
           lm3b : emb I F (sqV-sV I F p1) ‣
                       emb- I F p1 (pj1 (prj1 (eqV-expand' (sup A f) (emb I F p1) p2) x))
                 ≐ emb I F (zero-sV I F)
           lm3b = refV _
           lm3c : emb I F (zero-sV I F) ≐  zeroV
           lm3c = emb-zero I F
-- emb-zero : (I : Set) -> (F : I -> Set) -> emb I F (zero-sV I F) ≐ zeroV
-- sqV-sV I F u =  sup (isV I F u) (\x -> zero-sV I F)
-- emb I F (sup A f) = sup (To {I} {F} A) (\x -> emb I F (f x))
           lm2 : sqV (sup A f) ‣ x ≐
                      uV I F ‣ sqV-sV I F p1 ‣
                       emb- I F p1 (pj1 (prj1 (eqV-expand' (sup A f) (emb I F p1) p2) x))
           lm2 = traV lm4 (traV (symV lm3c) (traV (symV lm3b) (symV lm3)))
      in  lm , lm2


sqV-reflection-lm-half2 : (I : Set) -> (F : I -> Set) 
              -> (a : V) 
              -> (p : a ∈ uV I F) 
              -> sqV a ≥ uV I F ‣ sqV-sV I F (pj1 p)
sqV-reflection-lm-half2 I F (sup A f) (p1 , p2) x = 
     let lm6 = prj2 (eqV-expand' _ _ p2)
         u : To {I} {F} (isV I F p1)
         u = x
         x' :  # (emb I F p1)
         x' = emb+ I F p1 u

-- emb+ : (I : Set) -> (F : I -> Set) -> (u : sV I F) -> To {I} {F} (isV I F u) -> iV (emb I F u)
--    # (uV I F ‣ sqV-sV I F p1) 
--  = # ( (emb I F) (sqV-sV I F p1))
--  = # ((emb I F) (sup (isV I F p1) (\x -> zero-sV I F))
--  = (To {I} {F} (isV I F p1))
-- uV I F = sup (sV I F) (emb I F)
         y : # (sqV (sup A f))
         y = pj1 (lm6 x')
         lm3 : emb I F (zero-sV I F) ≐  zeroV
         lm3 = emb-zero I F
         lm2 : sqV (sup A f) ‣ y ≐ uV I F ‣ sqV-sV I F p1 ‣ x
         lm2 = symV lm3
     in y , lm2


sqV-reflection-lm : (I : Set) -> (F : I -> Set) 
              -> (a : V) 
              -> (p : a ∈ uV I F) 
              -> sqV a ≐ uV I F ‣ sqV-sV I F (pj1 p)
sqV-reflection-lm I F a p =
      pair  (sqV-reflection-lm-half1 I F a p) (sqV-reflection-lm-half2 I F a p)


sqV-reflection :  (I : Set) -> (F : I -> Set) 
              -> (a : V) 
              -> (a ∈ uV I F) 
              -> sqV a ∈ uV I F
sqV-reflection I F a p = 
  let p1 : # (uV I F)
      p1 = pj1 p
      p2 : a ≐ (uV I F) ‣ pj1 p
      p2 = pj2 p
      lm : sqV a ≐ uV I F ‣ sqV-sV I F (pj1 p)
      lm = sqV-reflection-lm I F a p
  in (sqV-sV I F (pj1 p)) , lm 


-- Squashing a set of sets

-- map-sqV : V -> V
-- map-sqV (sup A f) = sup A (\x -> sqV (f x))

ImV : (h : V -> V) -> V -> V
ImV  h (sup A f) = sup A (\x -> h (f x))

ImV-sV : (I : Set) -> (F : I -> Set) -> (h : sV I F -> sV I F) -> sV I F -> sV I F
ImV-sV I F  h (sup A f) = sup A (\x -> h (f x))

map-sqV : V -> V
map-sqV a = ImV sqV a

map-sqV-sV : (I : Set) -> (F : I -> Set) ->  sV I F -> sV I F
map-sqV-sV I F a = ImV-sV I F (sqV-sV I F) a

-- sqV-sV : (I : Set) -> (F : I -> Set)  -> (u : sV I F) -> sV I F


-- sV : (I : Set) -> (F : I -> Set)  -> Set
-- sV I F = W (Uo I F) (To {I} {F})

-- emb :   (I : Set) -> (F : I -> Set) -> sV I F -> V 
-- emb I F (sup A f) = sup (To {I} {F} A) (\x -> emb I F (f x))

-- uV : (I : Set) -> (F : I -> Set) -> V
-- uV I F = sup (sV I F) (emb I F)

