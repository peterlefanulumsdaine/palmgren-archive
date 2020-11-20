-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt4 where

open import basic-types
open import basic-setoids
open import dependent-setoids
open import subsetoids
open import iterative-sets
open import iterative-sets-pt2
open import iterative-sets-pt3
open import V-model-pt0
open import V-model-pt1
open import V-model-pt2
open import V-model-pt3
--

-- towards the more general congruence for Pi-formation

-- 



mk-Par-eq-right :  {Γ : ctx} 
    -> (A : ty Γ)   -> (B C : ty (Γ ▷ A))
    ->  Γ ▷ A ==>  B ==  C 
    -> (x : || κ Γ ||)
    -> (y : || κ-Fam §§ Ixx (ap1 (mk-Par A B) x) ||)
    -> Fxx (ap1 (mk-Par A C) x) •  ap (κ-Fam ±± (<<>> (refV (apt A x)))) y
      ≐ apt C (x , y)
mk-Par-eq-right  {Γ} A B C p x y  = 
  let lm : << VV >> apt C (x , ap (κ-Fam ±± (<<>> (refV (apt A x)))) y) 
            ~
           apt C (x , y)
      lm = extensionality1 (ty.type C) 
                    (x , ap (κ-Fam ±± (<<>> (refV (apt A x)))) y) 
                    (x , y)
              (<> (pairV-ext (refV (Γ ‣ x)) (symV (e+prop (refV (apt A x)) y)))) 
  in >><< lm
  


mk-Par-eq :  {Γ : ctx} 
    -> (A : ty Γ)   -> (B C : ty (Γ ▷ A))
    ->  Γ ▷ A ==>  B ==  C 
    -> (x : || κ Γ ||)
    ->  << Par VV κ-Fam >> (ap1 (mk-Par A B) x) ~ (ap1 (mk-Par A C) x)
mk-Par-eq  A B C p x  =
   <<>> (( <<>> (refV _) ) , ((λ y → <<>> (traV (>><< (ape p (x , y))) (symV (mk-Par-eq-right  A B C p x y )))))) 



Π-cong-lm2 :  {Γ : ctx} 
    -> (A : ty Γ)   -> (B C : ty (Γ ▷ A))
    ->  Γ ▷ A ==>  B ==  C 
    -> (x : || κ Γ ||)
    ->  << VV >> piV-op (ap1 (mk-Par A B) x) ~ piV-op (ap1 (mk-Par A C) x)
Π-cong-lm2  A B C p x  = 
     let lm : << Par VV κ-Fam >> (ap1 (mk-Par A B) x) ~ (ap1 (mk-Par A C) x)
         lm = (mk-Par-eq A B C p x)
         main : << VV >> piV-op (ap1 (mk-Par A B) x) ~ piV-op (ap1 (mk-Par A C) x)
         main = piV-ext (ap1 (mk-Par A B) x) (ap1 (mk-Par A C) x) lm
     in main


Π-cong-lm :  {Γ : ctx} 
    -> (A : ty Γ) -> (B C : ty (Γ ▷ A))
    ->  Γ ▷ A ==>  B ==  C 
    -> (x : || κ Γ ||)
    ->  << VV >> apt (Π-f A B) x ~ (apt (Π-f A C) x)
Π-cong-lm A B C p x = Π-cong-lm2 A B C p x



Π-cong :  {Γ : ctx} 
    -> (A : ty Γ)   -> (B C : ty (Γ ▷ A))
     ->  Γ ▷ A ==>  B ==  C 
-- ------------------------------------
    ->  Γ ==>  Π-f A B ==  Π-f A C 
-- 
Π-cong A B C p  = mk-eqty (λ x → Π-cong-lm A B C p x)






-- towards substitution rules for Pi


mk-Par-sub-lm :  {Δ Γ : ctx} 
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))  -> (h : subst Δ Γ) 
       -> (u : || κ Δ ||)
       -> (x : || κ-Fam §§ Ixx (ap1 (mk-Par A B) (aps h u)) ||)
       -> << VV >> Fxx (ap1 (mk-Par A B) (aps h u)) • x ~
           (Fxx (ap1 (mk-Par (A [[ h ]]) (B [[ ↑ A h ]])) u) •
            ap (κ-Fam ±± (<<>> (refV (apt A (aps h u))))) x)      
mk-Par-sub-lm {Δ} {Γ} A B h u x 
        = let 
              lm4 :  Γ ‣ (aps h u) ≐
                   Γ ‣  aps (h ⌢ ↓ (A [[ h ]]))
                           (u , ap (κ-Fam ±± (<<>> (refV (apt A (aps h u))))) x)
              lm4 = refV  (Γ ‣ aps h u)
              lm3-5 : (apt A  (aps h u)) ≐
                      (apt A (pj1
                           (aps (↑ A h)
                            (u ,
                             ap (κ-Fam ±± (<<>> (refV (apt A  (aps h u))))) x))))
              lm3-5 = refV (apt A  (aps h u))

              lm3-6 = elttyeq-lm  (asm (A [[ h ]]))
                                  (tyeq-from-eq 
                                    ((A [[ h ]]) [[ pp (A [[ h ]]) ]])
                                    (A [[ h ⌢ pp (A [[ h ]]) ]])
                                    (Sub-comp-prop-sym {(Δ ▷ (A [[ h ]]))} {Δ} {Γ} A h ( ↓ (A [[ h ]]))) 
                                    )
                                  (u , ap (κ-Fam ±± (<<>> (refV (apt A (aps h u))))) x)
             

              lm3-7 :  (apt A  (pj1 (aps (↑ A h)
                              (u ,  ap (κ-Fam ±± (<<>> (refV (apt A (aps h u))))) x))))
                                          ‣
                            (e+ (refV (apt A (aps h u))) x)
                       ≐
                       (apt A  (pj1 (aps (↑ A h)
                              (u ,  ap (κ-Fam ±± (<<>> (refV (apt A (aps h u))))) x))))
                                          ‣
                                            (pj2
                                          (aps
                                            (↑ A 
                                             h)
                                           (u , ap (κ-Fam ±± (<<>> (refV (apt A (aps h u))))) x)))
              lm3-7 = traV (refV _) lm3-6 

                       
              lm3 : (apt A (aps h u)) ‣ x
                 ≐ (apt A  (pj1 (aps (↑ A h)
                              (u ,  ap (κ-Fam ±± (<<>> (refV (apt A (aps h u))))) x))))
                                          ‣
                            pj2
                            (aps (↑ A h)
                             (u , ap (κ-Fam ±± (<<>> (refV (apt A (aps h u))))) x))


              lm3 = traV 
                   (e+prop
                   {apt A (aps h u)}
                   {apt A  (pj1 (aps (↑ A h)
                              (u ,  ap (κ-Fam ±± (<<>> (refV (apt A (aps h u))))) x)))}
                   lm3-5 x)
                    lm3-7
                    



              lm2 :  < κ (Γ ▷ A) > aps h u , x ~
                               aps (↑ A h)
                                    (u , ap (κ-Fam ±± (<<>> (refV (apt A (aps h u))))) x)

              lm2 = <> (pairV-ext lm4 lm3)
              lm : << VV >> apt B ((aps h u) , x) 
                          ~ apt (B [[ ↑ A h ]]) (u ,  (ap (κ-Fam ±± (<<>> (refV (apt A (aps h u))))) x))
              lm = extensionality1 (ty.type B) 
                                   (aps h u , x) 
                                   (aps (↑ A h)  (u , ap (κ-Fam ±± (<<>> (refV (apt A (aps h u))))) x)) 
                                   lm2
          in lm




mk-Par-sub :  {Δ Γ : ctx} 
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))  -> (h : subst Δ Γ) 
       -> (u : || κ Δ ||)
       -> << Par VV κ-Fam >> (ap1 (mk-Par A B) (aps h u)) ~ (ap1 (mk-Par (A [[ h ]]) (B [[ ↑ A h ]]) ) u)
mk-Par-sub {Δ} {Γ} A B h u = <<>> ( (<<>> (refV (apt A (aps h u)))) , (λ x → mk-Par-sub-lm {Δ} {Γ} A B h u x))



-- substituting into a Pi-type


Π-f-sub :  {Δ Γ : ctx} 
--
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))  -> (h : subst Δ Γ) 
--     ---------------------------------------
       -> Δ ==>  (Π-f A B) [[ h ]] ==  Π-f (A [[ h ]]) (B [[ ↑ A h ]]) 
Π-f-sub {Δ} {Γ} A B h = mk-eqty (\u ->
    let lm :  << VV >> ap11 piVV (ap1 (mk-Par A B) (aps h u)) ~ 
                      ap11 piVV (ap1 (mk-Par (A [[ h ]]) (B [[ ↑ A h ]]) ) u) 
        lm = extensionality11 piVV 
                              (ap1 (mk-Par A B) (aps h u)) 
                              (ap1 (mk-Par (A [[ h ]]) (B [[ ↑ A h ]])) u) 
                              (mk-Par-sub {Δ} {Γ} A B h u)
    in lm)




-- towards substitution rules for lambda

lambda-sub-raw  :  {Δ Γ : ctx} 
       -> (A : ty Γ)   -> {B : ty (Γ ▷ A)}
       -> {b : raw (Γ ▷ A)}
       -> (h : subst Δ Γ)
       -> Γ ▷ A ==> b :: B
       -> (x : || κ Δ ||) 
       -> apr (lambda A B b [ h ]) x ≐ apr (lambda (A [[ h ]]) (B [[ ↑ A h ]]) (b [ ↑ A h ])) x
lambda-sub-raw {Δ} {Γ} A {B} {b} h p x = 
    easy-eqV _ _ _ (\y -> pairV-ext (refV _) (symV (traV (sub-apply b ( ↑ A h ) (x , y)) 
                 (>><< (extensionality1 (raw.rawterm b) _ _ (qq-eq A h x y))))))
 


lambda-sub  :  {Δ Γ : ctx} 
       -> (A : ty Γ)   -> {B : ty (Γ ▷ A)}
       -> {b : raw (Γ ▷ A)}
       -> (h : subst Δ Γ)
       -> Γ ▷ A ==> b :: B
--  -----------------------------------------
       -> Δ ==> (lambda A B b) [ h ] == (lambda (A [[ h ]]) (B [[ ↑ A h ]]) (b [ ↑ A h ]))  :: (Π-f A B) [[ h ]]
lambda-sub {Δ} {Γ} A {B} {b} h p = pair (lambda-sub-raw {Δ} {Γ} A {B} {b} h p)
                                        (pair (elt-subst {Δ} {Γ} {lambda A B b} {Π-f A B} h (Π-i {Γ} A {B} {b} p))
                                             (elttyeq {Δ} (Π-i (A [[ h ]]) {B [[ ↑ A h ]]} {(b [ ↑ A h ])}  
                                                               (elt-subst  (↑ A h) p)) (tysym (Π-f-sub A B h)) ))
