-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt6 where

open import basic-types
open import basic-setoids       -- 525 lines
open import dependent-setoids   -- 559 lines
open import subsetoids          -- 341 lines
open import iterative-sets      -- 869 lines
open import iterative-sets-pt2  -- 326 lines
open import iterative-sets-pt3  -- 439 lines
open import V-model-pt0
open import V-model-pt1         -- 685 lines
open import V-model-pt2         -- 511 lines
open import V-model-pt3         -- 522 lines
open import V-model-pt4         -- 283 lines
open import V-model-pt5         -- 225 lines
                                -- 853 lines

-- towards the eta equality rule for Pi

Π-e-sub-raw-lm :
    {Δ Γ : ctx}  -> (h : subst Δ Γ)
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (q : Γ ==> a :: A)
    -> (x  : || κ Δ ||)
    -> (q1  : << VV >>   (Fxx (ap1 (mk-Par A B) (aps h x)) •
                         ap (κ-Fam ±± (<<>> (symV (refV (apt A (aps h x))))))
                          (pj1 (apel q (aps h x))))
                        ~
                       ((Fxx (ap1 (mk-Par (A [[ h ]]) (B [[ ↑ A h ]])) x) •
                        pj1 (apel q (aps h x)))))
    ->
            (apt B ((aps h x) , pj1 (apel q (aps h x))))
                  ‣ (pj1 (pj1 (apel p (aps h x))) (pj1 (apel q (aps h x))))
             ≐
            (apt (B [[ ↑ A h ]]) (x , pj1 (apel q (aps h x)))) ‣
               (ap (κ-Fam ±± q1)  ((pj1 (pj1 (apel (elt-subst h p) x)))
                     (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B h x))))) (pj1 (apel q (aps h x))))))

Π-e-sub-raw-lm {Δ} {Γ} h A B c p a q x q1 =
    let eq : << VV >> apt A (aps h x) ~ apt (A [[ h ]]) x
        eq = <<>> (refV (apt A (aps h x))) -- (pj1 (mk-Par-sub A B h x))
        eq2 :  apt A (aps h x) ‣  (pj1 (apel q (aps h x))) ≐
               apt A (aps h x) ‣  (ap (κ-Fam ±±  (<<>> (symV (refV (apt A (aps h x)))))) (pj1 (apel q (aps h x))))
        eq2 = e+prop ((symV (refV (apt A (aps h x))))) ((pj1 (apel q (aps h x))))
        eq3 : apt B (aps h x , pj1 (apel q (aps h x))) ‣
                pj1 (pj1 (apel p (aps h x))) (pj1 (apel q (aps h x)))
              ≐
               apt B  (aps h x ,
                      ap (κ-Fam ±± (<<>> (symV (refV (apt A (aps h x))))))
                       (pj1 (apel q (aps h x))))
               ‣
               pj1 (pj1 (apel p (aps h x)))
               (ap (κ-Fam ±± (<<>> (symV (refV (apt A (aps h x))))))
                (pj1 (apel q (aps h x))))
        eq3 = Π-f-exp3b {Γ} A B (aps h x) (pj1 (apel p (aps h x))) (pj1 (apel q (aps h x)))
               (ap (κ-Fam ±±  (<<>> (symV (refV (apt A (aps h x)))))) (pj1 (apel q (aps h x)))) eq2
        lm2 :  apt B  (aps h x ,
                       ap (κ-Fam ±± (<<>> (symV (refV (apt A (aps h x))))))
                       (pj1 (apel q (aps h x))))
               ‣
               pj1 (pj1 (apel p (aps h x)))
               (ap (κ-Fam ±± (<<>> (symV (refV (apt A (aps h x)))))) (pj1 (apel q (aps h x))))
                 ≐
            (apt (B [[ ↑ A h ]]) (x , pj1 (apel q (aps h x)))) ‣
               (ap (κ-Fam ±± q1)
               ((pj1 (pj1 (apel p (aps h x))))
                     (ap (κ-Fam ±±  (<<>> (symV (refV (apt A (aps h x)))))) (pj1 (apel q (aps h x))))))

        lm2 = e+prop (>><< q1) ( pj1 (pj1 (apel p (aps h x)))
               (ap (κ-Fam ±± (<<>> (symV (refV (apt A (aps h x)))))) (pj1 (apel q (aps h x)))))
        lm : (apt B ((aps h x) , pj1 (apel q (aps h x))))
                  ‣ (pj1 (pj1 (apel p (aps h x))) (pj1 (apel q (aps h x))))
             ≐
            (apt (B [[ ↑ A h ]]) (x , pj1 (apel q (aps h x)))) ‣
               (ap (κ-Fam ±± q1)  ((pj1 (pj1 (apel p (aps h x))))  -- elt-subst f p = mk-elt (λ x → apel p (aps f x))
                     (ap (κ-Fam ±±  (<<>> (symV (refV (apt A (aps h x)))) -- (pj1 (mk-Par-sub A B h x))
                              )) (pj1 (apel q (aps h x))))))
        lm = traV eq3 lm2
     in lm





Π-e-sub-raw :  {Δ Γ : ctx}  -> (h : subst Δ Γ)
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (q : Γ ==> a :: A)
    -> << Raw Δ >> (app {Γ} A B c p a q) [ h ]
         ~ (app {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ]) (elttyeq (elt-subst h p) (Π-f-sub A B h)) (a [ h ]) (elt-subst h q))
Π-e-sub-raw {Δ} {Γ} h A B c p a q
  = <<>> (<<>> (λ x →

  let  ph : Δ ==> c [ h ] :: Π-f (A [[ h ]]) (B [[ ↑ A h ]])
       ph = (elttyeq (elt-subst h p) (Π-f-sub A B h))
       qh : Δ ==> a [ h ] :: A [[ h ]]
       qh = (elt-subst h q)

       q1  : << VV >>   Fxx (ap1 (mk-Par A B) (aps h x)) •
                         ap (κ-Fam ±± (<<>> (symV (refV (apt A (aps h x))))))
                          (pj1 (apel q (aps h x)))
                        ~
                       (Fxx (ap1 (mk-Par (A [[ h ]]) (B [[ ↑ A h ]])) x) •
                        pj1 (apel q (aps h x)))
       q1 = (Fxx-lm' (ap1 (mk-Par A B) (aps h x))
                      (ap1 (mk-Par (A [[ h ]]) (B [[ ↑ A h ]])) x)
                           (mk-Par-sub A B h x) (pj1 (apel q (aps h x))))
       lm2 : (apt B ((aps h x) , pj1 (apel q (aps h x))))
                  ‣ (pj1 (pj1 (apel p (aps h x))) (pj1 (apel q (aps h x))))
             ≐
            (apt (B [[ ↑ A h ]]) (x , pj1 (apel q (aps h x)))) ‣
               (ap (κ-Fam ±± q1)  ((pj1 (pj1 (apel (elt-subst h p) x)))
                   (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B h x))))) (pj1 (apel q (aps h x))))))
       lm2 = Π-e-sub-raw-lm {Δ} {Γ} h A B c p a q x q1

       lm : (apt B ((aps h x) , pj1 (apel q (aps h x))))
                  ‣ (pj1 (pj1 (apel p (aps h x))) (pj1 (apel q (aps h x))))
             ≐
            (apt (B [[ ↑ A (h) ]]) (x , pj1 (apel qh x)))
                 ‣ (pj1 (pj1 (apel ph x)) (pj1 (apel qh x)))
       lm = lm2 -- works, but very slow

       main : app-op {Γ} A B c p a q (aps h x) ≐
              app-op {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ]) (elttyeq (elt-subst h p) (Π-f-sub A B h)) (a [ h ]) (elt-subst h q) x
       main = lm
  in (<<>> main)))

-- alternate formulation of the above

Π-e-sub-raw-mod :  {Δ Γ : ctx}  -> (h : subst Δ Γ)
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (q : Γ ==> a :: A)
    -> (x : || κ Δ ||)
    ->  app-op {Γ} A B c p a q (aps h x) ≐
              app-op {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ]) (elttyeq (elt-subst h p) (Π-f-sub A B h)) (a [ h ]) (elt-subst h q) x
Π-e-sub-raw-mod {Δ} {Γ} h A B c p a q x
  =

  let  ph : Δ ==> c [ h ] :: Π-f (A [[ h ]]) (B [[ ↑ A h ]])
       ph = (elttyeq (elt-subst h p) (Π-f-sub A B h))
       qh : Δ ==> a [ h ] :: A [[ h ]]
       qh = (elt-subst h q)

       q1  : << VV >>   Fxx (ap1 (mk-Par A B) (aps h x)) •
                         ap (κ-Fam ±± (<<>> (symV (refV (apt A (aps h x))))))
                          (pj1 (apel q (aps h x)))
                        ~
                       (Fxx (ap1 (mk-Par (A [[ h ]]) (B [[ ↑ A h ]])) x) •
                        pj1 (apel q (aps h x)))
       q1 = (Fxx-lm' (ap1 (mk-Par A B) (aps h x))
                      (ap1 (mk-Par (A [[ h ]]) (B [[ ↑ A h ]])) x)
                           (mk-Par-sub A B h x) (pj1 (apel q (aps h x))))
       lm2 : (apt B ((aps h x) , pj1 (apel q (aps h x))))
                  ‣ (pj1 (pj1 (apel p (aps h x))) (pj1 (apel q (aps h x))))
             ≐
            (apt (B [[ ↑ A h ]]) (x , pj1 (apel q (aps h x)))) ‣
               (ap (κ-Fam ±± q1)  ((pj1 (pj1 (apel (elt-subst h p) x)))
                   (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B h x))))) (pj1 (apel q (aps h x))))))
       lm2 = Π-e-sub-raw-lm {Δ} {Γ} h A B c p a q x q1

       lm : (apt B ((aps h x) , pj1 (apel q (aps h x))))
                  ‣ (pj1 (pj1 (apel p (aps h x))) (pj1 (apel q (aps h x))))
             ≐
            (apt (B [[ ↑ A (h) ]]) (x , pj1 (apel qh x)))
                 ‣ (pj1 (pj1 (apel ph x)) (pj1 (apel qh x)))
       lm = lm2 -- works, but very slow

       main : app-op {Γ} A B c p a q (aps h x) ≐
              app-op {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ]) (elttyeq (elt-subst h p) (Π-f-sub A B h)) (a [ h ]) (elt-subst h q) x
       main = lm
  in main







Π-e-sub :  {Δ Γ : ctx}  -> (h : subst Δ Γ)
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (q : Γ ==> a :: A)

--  -----------------------------------------
    ->  Δ ==> (app {Γ} A B c p a q) [ h ]
          ==  (app {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ]) (elttyeq (elt-subst h p) (Π-f-sub A B h)) (a [ h ]) (elt-subst h q))
          :: B [[ els q ]] [[ h ]]
Π-e-sub {Δ} {Γ} h A B c p a q  =
   let main : << Raw Δ >> (app {Γ} A B c p a q) [ h ]
               ~ (app {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ]) (elttyeq (elt-subst h p) (Π-f-sub A B h)) (a [ h ]) (elt-subst h q))
       main =  Raw-lm2 (Π-e-sub-raw-mod {Δ} {Γ} h A B c p a q) -- Π-e-sub-raw {Δ} {Γ} h A B c p a q     -- **** stuck here 2.6.0.1
       lm1 : Δ ==> (app {Γ} A B c p a q) [ h ]  :: B [[ els q ]] [[ h ]]
       lm1 = (elt-subst {Δ} {Γ} {(app {Γ} A B c p a q)} {B [[ els q ]]} h (Π-e  {Γ} A B c p a q))
   in  pair (Π-e-sub-raw-mod {Δ} {Γ} h A B c p a q) -- (Raw-lm main) -- (λ x → >><< ((>><< (>><< main)) x))
            (pair lm1 (subj-red {Δ} {B [[ els q ]] [[ h ]]} ((app {Γ} A B c p a q) [ h ]) (app {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ]) (elttyeq (elt-subst h p) (Π-f-sub A B h)) (a [ h ]) (elt-subst h q)) lm1 main))

-- ** TO DO: general version of the above: Π-e-sub-gen



Π-e-sub-gen-raw :  {Δ Γ : ctx}  -> (h : subst Δ Γ)
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (q : Γ ==> a :: A)
    -> (r1 : Δ ==> (c [ h ]) ::  Π-f {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) )
    -> (r2 : Δ ==> (a [ h ]) :: A [[ h ]])
    -> << Raw Δ >> (app A B c p a q) [ h ]
         ~ (app {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ]) r1 (a [ h ]) r2)
Π-e-sub-gen-raw {Δ} {Γ} h A B c p a q r1 r2 =
    let eq1 : << Raw Δ >> (app A B c p a q) [ h ]
         ~ (app {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ]) (elttyeq (elt-subst h p) (Π-f-sub A B h)) (a [ h ]) (elt-subst h q))
        eq1 = Π-e-sub-raw {Δ} {Γ} h A B c p a q -- **** stuck here 2.6.0.1
        eq2 : << Raw Δ >> (app {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ])
                      (elttyeq (elt-subst h p) (Π-f-sub A B h)) (a [ h ]) (elt-subst h q))
             ~ (app {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ]) r1 (a [ h ]) r2)
        eq2 = app-cong-raw {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]])
                      (c [ h ]) (c [ h ]) (elttyeq (elt-subst h p) (Π-f-sub A B h)) r1 (tmrefl r1)
                      (a [ h ]) (a [ h ]) (elt-subst h q) r2 (tmrefl r2)

    in tra' eq1 eq2 -- tra eq1 eq2


{--  --}



Π-e-sub-gen :  {Δ Γ : ctx}  -> (h : subst Δ Γ)
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (q : Γ ==> a :: A)
    -> (r1 : Δ ==> (c [ h ]) ::  Π-f {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) )
    -> (r2 : Δ ==> (a [ h ]) :: A [[ h ]])

--  -----------------------------------------
    ->  Δ ==> (app A B c p a q) [ h ]
          ==  (app {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ]) r1 (a [ h ]) r2)
          :: B [[ els q ]] [[ h ]]
Π-e-sub-gen {Δ} {Γ} h A B c p a q r1 r2  =
   let main : << Raw Δ >> (app A B c p a q) [ h ]
               ~ (app {Δ} (A [[ h ]]) (B [[ ↑ A (h) ]]) (c [ h ]) r1 (a [ h ]) r2)
       main = Π-e-sub-gen-raw {Δ} {Γ} h A B c p a q r1 r2
       lm1 = (elt-subst {Δ} {Γ} {(app A B c p a q)} {B [[ els q ]]} h (Π-e  {Γ} A B c p a q))
   in   pair (λ x → >><< ((>><< (>><< main)) x)) -- main
             (pair lm1
                   (subj-red _ _ lm1 main))





Π-i-sub-raw  :  {Δ Γ : ctx}  -> (h : subst Δ Γ)
       -> (A : ty Γ)   -> {B : ty (Γ ▷ A)}
       -> {b : raw (Γ ▷ A)}
       -> (Γ ▷ A ==> b :: B)
       -> << Raw Δ >>  (lambda A B b) [ h ] ~ (lambda (A [[ h ]]) (B [[ ↑ A (h) ]]) (b [ ↑ A (h) ]))
Π-i-sub-raw  {Δ} {Γ} h A {B} {b} p
  = <<>> (<<>> (λ x →

  let lm1 : (z : # (apr ((lambda A B b) [ h ]) x))
               -> Σ (# (apr (lambda (A [[ h ]]) (B [[ ↑ A (h) ]]) (b [ ↑ A (h) ])) x))
                   (\y ->  (apr ((lambda A B b) [ h ]) x) ‣ z ≐ (apr (lambda (A [[ h ]]) (B [[ ↑ A (h) ]]) (b [ ↑ A (h) ])) x) ‣ y)
      lm1 = \z -> (z , pairV-ext (refV _)
                                (>><< (extensionality1 (raw.rawterm b)
                                    _ _
                                    (<> (pairV-ext (refV _) (e+prop (>><< (ape
                                 (tyeq-from-eq ((A [[ h ]]) [[ ↓ (A [[ h ]]) ]])
                                         (A [[ h ⌢ ↓ (A [[ h ]]) ]])
                                        (Sub-comp-prop-sym A h (↓ (A [[ h ]]))))
                                (x , z))) z )))

                                 )))
      lm2 : (y : # (apr (lambda (A [[ h ]]) (B [[ ↑ A (h) ]]) (b [ ↑ A (h) ])) x))
               -> Σ (# (apr ((lambda A B b) [ h ]) x)) (\z ->  (apr ((lambda A B b) [ h ]) x) ‣ z ≐ (apr (lambda (A [[ h ]]) (B [[ ↑ A (h) ]]) (b [ ↑ A (h) ])) x) ‣ y)
      lm2 = \y -> (y , pairV-ext (refV _) (>><< (extensionality1 (raw.rawterm b)
                                              _ _
                                             (<> (pairV-ext (refV _) (e+prop (>><< (ape
                                        (tyeq-from-eq ((A [[ h ]]) [[ ↓ (A [[ h ]]) ]])
                                            (A [[ h ⌢ ↓ (A [[ h ]]) ]])
                                         (Sub-comp-prop-sym A h (↓ (A [[ h ]]))))
                                         (x , y))) y )))

                                      )))
      lm : apr ((lambda A B b) [ h ]) x ≐ apr (lambda (A [[ h ]]) (B [[ ↑ A (h) ]]) (b [ ↑ A (h) ])) x
      lm = eqV-unexpand (apr ((lambda A B b) [ h ]) x)
                 (apr (lambda (A [[ h ]]) (B [[ ↑ A (h) ]]) (b [ ↑ A (h) ])) x) lm1 lm2
  in <<>> lm

  ))





Π-i-sub  :  {Δ Γ : ctx}  -> (h : subst Δ Γ)
       -> (A : ty Γ)   -> {B : ty (Γ ▷ A)}
       -> {b : raw (Γ ▷ A)}
       -> Γ ▷ A ==> b :: B
--  -----------------------------------------
        -> Δ ==> (lambda A B b) [ h ] == (lambda (A [[ h ]]) (B [[ ↑ A (h) ]]) (b [ ↑ A (h) ])) :: (Π-f A B) [[ h ]]
Π-i-sub  {Δ} {Γ} h A {B} {b} p =
   let main : << Raw Δ >>  (lambda A B b) [ h ] ~ (lambda (A [[ h ]]) (B [[ ↑ A (h) ]]) (b [ ↑ A (h) ]))
       main = Π-i-sub-raw  {Δ} {Γ} h A {B} {b} p
       lm1 =  (elt-subst {Δ} {Γ} {lambda A B b} { Π-f A B} h (Π-i {Γ} A {B} {b} p))
   in   pair (λ x → >><< (>><< (>><< main) x)) -- main
             (pair lm1
                   (subj-red _ _ lm1 main))


Π-eta-left1 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (Γ ▷ A) ==> (c [ ↓ A ]) ::  ((Π-f {Γ} A B) [[ ↓ A ]])
Π-eta-left1 {Γ} A B c p = elt-subst (↓ A) p



Π-eta-left2 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (Γ ▷ A) ==> vv A ::  A [[ ↓ A ]]
Π-eta-left2 {Γ} A B c p  = asm A

Π-eta-left3 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (Γ ▷ A) ==> (c [ ↓ A ]) ::   (Π-f {Γ ▷ A} (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]))    -- ((Π-f {Γ} A B) [[ ↓ A ]])
Π-eta-left3 {Γ} A B c p = elttyeq (Π-eta-left1 {Γ} A B c p) (Π-f-sub A B (↓ A))

Π-eta-left4 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (Γ ▷ A) ==> app (A [[ ↓ A ]])
                       (B [[ ↑ A (↓ A) ]])
                       (c [ ↓ A ])
                       (Π-eta-left3 {Γ} A B c p)
                       (vv A)
                       (Π-eta-left2 {Γ} A B c p)
               :: (B [[ ↑ A (↓ A) ]]) [[ els (Π-eta-left2 {Γ} A B c p) ]]
Π-eta-left4 {Γ} A B c p =
    Π-e {Γ ▷ A} (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ]) (Π-eta-left3 {Γ} A B c p) (vv A) (Π-eta-left2 {Γ} A B c p)

 -- **** stuck here 2.6.0.1


Π-eta-left5-lm2 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (x : || κ Γ ||)
    -> (y : || κ (apt A x) ||)
    ->  (apt ((B [[ ↑ A (↓ A) ]]) [[ els (asm A) ]])  (x , y)) ≐
        (apt B  (x , y))
Π-eta-left5-lm2 {Γ} A B x y =  >><<
     (extensionality1 (ty.type B) _ (( x , y )) (<> (pairV-ext (refV _) (symV (e+prop (>><< (ape
        (tyeq-from-eq ((A [[ ↓ A ]]) [[ ↓ (A [[ ↓ A ]]) ]])
         (A [[ ↓ A ⌢ ↓ (A [[ ↓ A ]]) ]])
         (Sub-comp-prop-sym A (↓ A) (↓ (A [[ ↓ A ]]))))
        (ap (subst.cmap (els (asm A))) (x , y)))) y)))) )





Π-eta-left5-lm :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (u : || κ (Γ ▷ A) ||)
    -> (apt ((B [[ ↑ A (↓ A) ]]) [[ els (asm A) ]]) u)  ≐
       (apt B  u)
Π-eta-left5-lm {Γ} A B  ( x , y )  = Π-eta-left5-lm2 A B x y

Π-eta-left5 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (Γ ▷ A) ==> (B [[ ↑ A (↓ A) ]]) [[ els (Π-eta-left2 {Γ} A B c p) ]]  == B
Π-eta-left5 {Γ} A B c p = mk-eqty (λ u → <<>> (Π-eta-left5-lm A B u))



Π-eta-left6 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (Γ ▷ A) ==> app (A [[ ↓ A ]])
                       (B [[ ↑ A (↓ A) ]])
                       (c [ ↓ A ])
                       (Π-eta-left3 {Γ} A B c p)
                       (vv A)
                       (Π-eta-left2 {Γ} A B c p)
               :: B
Π-eta-left6 {Γ} A B c p =  elttyeq (Π-eta-left4 {Γ} A B c p) (Π-eta-left5 {Γ} A B c p)

Π-eta-left7 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> Γ ==> lambda A B (app (A [[ ↓ A ]])
                       (B [[ ↑ A (↓ A) ]])
                       (c [ ↓ A ])
                       (Π-eta-left3 {Γ} A B c p)
                       (vv A)
                       (Π-eta-left2 {Γ} A B c p))  ::  Π-f {Γ} A B
Π-eta-left7 {Γ} A B c p =  Π-i A (Π-eta-left6 {Γ} A B c p)

-- **** stuck here 2.6.0.1

Π-eta-left8 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (Γ ▷ A) ==> app (A [[ ↓ A ]])
                       (B [[ ↑ A (↓ A) ]])
                       (c [ ↓ A ])
                       (Π-eta-aux-lm A B c p)
                       (vv A)
                       (asm A)
               ::  (B [[ ↑ A (↓ A) ]]) [[ els (asm A) ]]
Π-eta-left8 {Γ} A B c p = Π-e {Γ ▷ A}
                               (A [[ ↓ A ]])
                               (B [[ ↑ A (↓ A) ]])
                               (c [ ↓ A ])
                               (Π-eta-aux-lm A B c p)
                               (vv A)
                               (asm A)

-- **** stuck here 2.6.0.1

{-- moved to pt0

subst-cong : {Θ Δ Γ : ctx} -> (f f' : subst Δ Γ) -> (g  g' : subst Θ Δ)
      -> < Subst Δ Γ > f ~ f'
      -> < Subst Θ Δ > g ~ g'
      -> < Subst Θ Γ > (f ⌢ g) ~ (f' ⌢ g')
subst-cong {Θ} {Δ} {Γ} f f' g g' p q =
    <> (<> (λ x →
   let eq1 : < κ Γ > setoidmap.op (subst.cmap f ° subst.cmap g) x ~
                     setoidmap.op (subst.cmap f ° subst.cmap g' ) x
       eq1 = extensionality (subst.cmap f) _ _ ((>< (>< q) x))
       eq2 : < κ Γ > setoidmap.op (subst.cmap f ° subst.cmap g' ) x ~
                    setoidmap.op (subst.cmap (f') ° subst.cmap (g')) x
       eq2 = >< (>< p) ( aps g' x)
       eq : < κ Γ > setoidmap.op (subst.cmap f ° subst.cmap g) x ~
                    setoidmap.op (subst.cmap (f') ° subst.cmap (g')) x
       eq = tra eq1 eq2
   in eq))
--}



-- to be moved: pt4

qq-ext-el-lm-gen :  {Γ : ctx}
    -> (A : ty Γ)
    -> (p : Γ ▷ A ==> vv A :: A [[ ↓ A ]])
    -> < Subst (Γ ▷ A) (Γ ▷ A) >  ((↑ A (↓ A))  ⌢  (els p))
                                         ~ (ids {Γ ▷ A})
qq-ext-el-lm-gen {Γ} A p =
    let lm : < Subst (Γ ▷ A) (Γ ▷ A ▷ (A [[ ↓ A ]])) >  (els p) ~ (els (asm A))
        lm = els-irr p (asm A)
        lm2 : < Subst (Γ ▷ A) (Γ ▷ A) >  ((↑ A (↓ A))  ⌢  (els p)) ~ ((↑ A (↓ A))  ⌢  (els (asm A)))
        lm2 = subst-cong (↑ A (↓ A)) (↑ A (↓ A)) (els p)  (els (asm A)) (refl (Subst (Γ ▷ A ▷ (A [[ ↓ A ]])) (Γ ▷ A)) (↑ A (↓ A))) lm
    in (tra {Subst (Γ ▷ A) (Γ ▷ A)}
            {((↑ A (↓ A))  ⌢  (els p))} {((↑ A (↓ A))  ⌢  (els (asm A)))} {(ids {Γ ▷ A})}
            lm2 (qq-ext-el-lm {Γ} A) )

-- **** stuck here 2.6.0.1



Π-eta-beta-spec2-lm : {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    ->  Γ ▷ A ==>
      lambda (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])
      (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
       (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)
       [ ↑ A (↓ A) ])
      :: Π-f (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])
Π-eta-beta-spec2-lm {Γ} A B c p =
  let  lm1 : (Γ ▷ A) ==> app (A [[ ↓ A ]])
                       (B [[ ↑ A (↓ A) ]])
                       (c [ ↓ A ])
                       (Π-eta-left3 {Γ} A B c p)
                       (vv A)
                       (Π-eta-left2 {Γ} A B c p)
               :: (B [[ ↑ A (↓ A) ]]) [[ els (Π-eta-left2 {Γ} A B c p) ]]
       lm1 = Π-eta-left4 {Γ} A B c p  -- **** stuck here 2.6.0.1
       lm2 = elt-subst (↑ A (↓ A)) lm1
       lm3a : < Subst (Γ ▷ A) (Γ ▷ A) >  ((↑ A (↓ A))  ⌢  (els (Π-eta-left2 A B c p)))  ~ (ids {Γ ▷ A})
       lm3a = qq-ext-el-lm-gen A (Π-eta-left2 A B c p)
       lm3b :  Γ ▷ A ==> (B [[ ((↑ A (↓ A))  ⌢  (els (Π-eta-left2 A B c p))) ]])
                      == (B [[ ↑ A (↓ A) ]]) [[ els (Π-eta-left2 A B c p) ]]
       lm3b = tysubst-com B (↑ A (↓ A)) (els (Π-eta-left2 A B c p))
       lm3c :   Γ ▷ A ==> (B [[ ((↑ A (↓ A))  ⌢  (els (Π-eta-left2 A B c p))) ]]) == B [[ ids {Γ ▷ A} ]]
       lm3c = tyeq-subst2 B _ _ lm3a
       lm3d :  Γ ▷ A ==>  B [[ ids {Γ ▷ A} ]] == B
       lm3d = tysubst-id B
       lm3 : Γ ▷ A ==> (B [[ ↑ A (↓ A) ]]) [[ els (Π-eta-left2 A B c p) ]] ==  B
       lm3 = tytra (tysym lm3b) (tytra lm3c lm3d)
       lm4 :  Γ ▷ A ▷ (A [[ ↓ A ]]) ==>
               ((B [[ ↑ A (↓ A) ]]) [[ els (Π-eta-left2 A B c p) ]]) [[ ↑ A (↓ A) ]]
               ==  B [[ ↑ A (↓ A) ]]
       lm4 = tyeq-subst (↑ A (↓ A)) lm3

       lm5 : Γ ▷ A ▷ (A [[ ↓ A ]]) ==>
           app (A [[ ↓ A ]])
               (B [[ ↑ A (↓ A) ]])
               (c [ ↓ A ])
               (Π-eta-left3 A B c p)
               (vv A)
               (Π-eta-left2 A B c p)
            [ ↑ A (↓ A) ]
           :: B [[ ↑ A (↓ A) ]]
       lm5 = elttyeq lm2 lm4
       lm6 =  Π-i {Γ ▷ A}
                  (A [[ ↓ A ]])
                  {B [[ ↑ A (↓ A) ]]}
                  {(app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                    (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)
                   [ ↑ A (↓ A) ])}
                  lm5
  in lm6



-- move to earlier part :


sub-ext : {Δ Γ : ctx} -> {a a' : raw Γ} -> {f f' : subst Δ Γ}
      -> << Raw Γ >> a ~ a' -> < Subst Δ Γ > f ~ f'
      -> << Raw Δ >> (a [ f ]) ~ (a' [ f' ])
sub-ext {Δ} {Γ} {a} {a'} {f} {f'} p q
  = <<>> (<<>> (λ x →
     (let  eq2 = >< (>< q) x
           eq1 : < κ Γ > aps f x ~  aps f' x
           eq1 = <> (>< eq2)
           eq : apr a (aps f x) ≐  apr a' (aps f' x)
           eq =  traV (>><< (>><< (>><< p) (aps f x))) (>><< (extensionality1 (raw.rawterm a') _ _ eq1))
     in <<>> eq)))



term-els-lm5 : {Γ : ctx}
            -> (A : ty Γ)
            -> < Subst (Γ ▷ A) (Γ ▷ A) > ((↑ A (↓ A)) ⌢ (els (asm A))) ~ (ids {Γ ▷ A})
term-els-lm5 {Γ} A  =
 <> (<> (λ z → <> (
  pairV-ext (refV _) (symV (e+prop (>><< (ape
       (tyeq-from-eq ((A [[ ↓ A ]]) [[ ↓ (A [[ ↓ A ]]) ]])
        (A [[ ↓ A ⌢ ↓ (A [[ ↓ A ]]) ]])
        (Sub-comp-prop-sym A (↓ A) (↓ (A [[ ↓ A ]]))))
       (ap (subst.cmap (els (asm A))) z)))  (pj2 z))))))



term-els-lm4 : {Γ : ctx}
            -> (A : ty Γ)
            -> (c : raw (Γ ▷ A))
            -> << Raw (Γ ▷ A) >> (c [ (( ↑ A (↓ A)) ⌢ (els (asm A))) ]) ~  (c [ ids {Γ ▷ A}])
term-els-lm4 {Γ} A c =  sub-ext {Γ ▷ A} {Γ ▷ A} {c} {c} {(( ↑ A (↓ A)) ⌢ (els (asm A)))} {ids {Γ ▷ A}} (refl' (Raw (Γ ▷ A)) c) (term-els-lm5 A)

-- **** stuck here 2.6.0.1


term-els-lm3 : {Γ : ctx}
            -> (A : ty Γ)
            -> (c : raw (Γ ▷ A))
            ->  << Raw (Γ ▷ A) >> (c [ ids {Γ ▷ A} ]) ~ c
term-els-lm3 {Γ} A c = sub-id-prop {Γ ▷ A} c




term-els-lm2 : {Γ : ctx}
            -> (A : ty Γ)
            -> (c : raw (Γ ▷ A))
            ->  << Raw (Γ ▷ A) >> (c [ (↑ A (↓ A)) ⌢ (els (asm A)) ]) ~ c
term-els-lm2 {Γ} A c  =
    tra' (term-els-lm4  A c) (term-els-lm3  A c)



term-els-lm : {Γ : ctx}
            -> (A : ty Γ)
            -> (c : raw (Γ ▷ A))
            ->  << Raw (Γ ▷ A) >> (c [ ↑ A (↓ A) ]) [ els (asm A) ] ~ c
term-els-lm {Γ} A c =  tra' (sub-comp-prop c ( ↑ A (↓ A))  (els (asm A))) (term-els-lm2 {Γ} A c)

-- **** stuck here 2.6.0.1

Π-eta-beta-spec3 : {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    ->  Γ ▷ A ==>
          ((app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
           (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)
            [ ↑ A (↓ A) ])
           [ els (asm A) ])
           ==
          app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
             (Π-eta-aux-lm A B c p) (vv A) (asm A)
           :: (B [[ ↑ A (↓ A) ]]) [[ els (asm A) ]]
Π-eta-beta-spec3 {Γ} A B c p =
    let lm1 :  << Raw (Γ ▷ A) >> ((app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
               (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)
               [ ↑ A (↓ A) ])
               [ els (asm A) ])
              ~ (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
               (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))
        lm1 = term-els-lm A (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])     -- **** stuck here 2.6.0.1
               (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))  -- make from general theorem  see also below
        lm2 :  << Raw (Γ ▷ A) >>   (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                                        (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)) ~
                                   (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                                        (Π-eta-aux-lm A B c p) (vv A) (asm A))
        lm2 =  app-irr {Γ ▷ A} (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ]) (Π-eta-left3 A B c p) (Π-eta-aux-lm A B c p) (vv A) (Π-eta-left2 A B c p) (asm A)
        main = (tra'
                  lm1
                  lm2)
        smain = sym' main

    in pair (λ x → >><< (>><< (>><< main) x)) -- main
            (pair (subj-red {Γ ▷ A} {(B [[ ↑ A (↓ A) ]]) [[ els (asm A) ]]} _ _  (Π-eta-left8 {Γ} A B c p) smain )
                  (Π-eta-left8 {Γ} A B c p))


Π-eta-beta-spec2 : {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> Γ ▷ A ==>
              app (A [[ ↓ A ]])
                  (B [[ ↑ A (↓ A) ]])
                  (lambda {Γ ▷ A}
                          (A [[ ↓ A ]])
                          (B [[ ↑ A (↓ A) ]])
                          ((app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                             (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))
                            [ ↑ A (↓ A) ]))
                  (Π-eta-beta-spec2-lm {Γ} A B c p)
                  (vv A)
                  (asm A)
                  ==
              app (A [[ ↓ A ]])
                  (B [[ ↑ A (↓ A) ]])
                  (c [ ↓ A ])
                  (Π-eta-aux-lm A B c p)
                  (vv A)
                  (asm A)
               :: (B [[ ↑ A (↓ A) ]]) [[ els (asm A) ]]
Π-eta-beta-spec2 {Γ} A B c p =
  let  {-- lm1 - lm5 make separate lemma --}
       lm1 = Π-eta-left4 {Γ} A B c p   -- **** stuck here 2.6.0.1
       lm2 = elt-subst (↑ A (↓ A)) lm1
       lm3a : < Subst (Γ ▷ A) (Γ ▷ A) >  ((↑ A (↓ A))  ⌢  (els (Π-eta-left2 A B c p)))  ~ (ids {Γ ▷ A})
       lm3a = qq-ext-el-lm-gen A (Π-eta-left2 A B c p)
       lm3b :  Γ ▷ A ==> (B [[ ((↑ A (↓ A))  ⌢  (els (Π-eta-left2 A B c p))) ]])
                      == (B [[ ↑ A (↓ A) ]]) [[ els (Π-eta-left2 A B c p) ]]
       lm3b = tysubst-com B (↑ A (↓ A)) (els (Π-eta-left2 A B c p))
       lm3c :   Γ ▷ A ==> (B [[ ((↑ A (↓ A))  ⌢  (els (Π-eta-left2 A B c p))) ]]) == B [[ ids {Γ ▷ A} ]]
       lm3c = tyeq-subst2 B _ _ lm3a
       lm3d :  Γ ▷ A ==>  B [[ ids {Γ ▷ A} ]] == B
       lm3d = tysubst-id B
       lm3 : Γ ▷ A ==> (B [[ ↑ A (↓ A) ]]) [[ els (Π-eta-left2 A B c p) ]] ==  B
       lm3 = tytra (tysym lm3b) (tytra lm3c lm3d)
       lm4 :  Γ ▷ A ▷ (A [[ ↓ A ]]) ==>
               ((B [[ ↑ A (↓ A) ]]) [[ els (Π-eta-left2 A B c p) ]]) [[ ↑ A (↓ A) ]]
               ==  B [[ ↑ A (↓ A) ]]
       lm4 = tyeq-subst (↑ A (↓ A)) lm3

       lm5 : Γ ▷ A ▷ (A [[ ↓ A ]]) ==>
           app (A [[ ↓ A ]])
               (B [[ ↑ A (↓ A) ]])
               (c [ ↓ A ])
               (Π-eta-left3 A B c p)
               (vv A)
               (Π-eta-left2 A B c p)
            [ ↑ A (↓ A) ]
           :: B [[ ↑ A (↓ A) ]]
       lm5 = elttyeq lm2 lm4
       lm = Π-beta-gen {Γ ▷ A}
                       (A [[ ↓ A ]])
                       (B [[ ↑ A (↓ A) ]])
                       ((app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                             (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))
                            [ ↑ A (↓ A) ])
                       lm5
                       (Π-eta-beta-spec2-lm {Γ} A B c p)
                       (vv A) -- (vv A)
                       (asm A) -- (asm A)

  in (tmtra { Γ ▷ A }
            ((B [[ ↑ A (↓ A) ]]) [[ els (asm A) ]])
            (app (A [[ ↓ A ]])
                  (B [[ ↑ A (↓ A) ]])
                  (lambda {Γ ▷ A}
                          (A [[ ↓ A ]])
                          (B [[ ↑ A (↓ A) ]])
                          ((app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                             (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))
                            [ ↑ A (↓ A) ]))
                  (Π-eta-beta-spec2-lm {Γ} A B c p)
                  (vv A)
                  (asm A))
             ((app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
               (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)
                [ ↑ A (↓ A) ]) [ els (asm A) ])
             (app (A [[ ↓ A ]])
                  (B [[ ↑ A (↓ A) ]])
                  (c [ ↓ A ])
                  (Π-eta-aux-lm A B c p)
                  (vv A)
                  (asm A))
             lm
             (Π-eta-beta-spec3 {Γ} A B c p)
     )




Π-eta-beta-spec-cong2 : {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> Γ ▷ A ==>
      lambda A B
      (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
       (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))
      [ ↓ A ]
      ==
      lambda (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])
      (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
       (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)
       [ ↑ A (↓ A) ])
      :: Π-f (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])
Π-eta-beta-spec-cong2 {Γ} A B c p =
   let  lm = Π-i-sub {Γ ▷ A} {Γ} (↓ A) A {B}    -- **** stuck here 2.6.0.1
         {(app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
          (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))} (Π-eta-left6 {Γ} A B c p)


        lm2 :  Γ ▷ A ==> Π-f A B [[ ↓ A ]] == Π-f (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])
        lm2 = Π-f-sub A B ( ↓ A )
   in (elteqtyeq {Γ ▷ A}
                 (lambda A B
                      (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                       (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))
                      [ ↓ A ])
                 (lambda (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])
                                      (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                       (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)
                       [ ↑ A (↓ A) ]))
                 (Π-f A B [[ ↓ A ]])
                 (Π-f (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]))
                 lm
                 lm2)


Π-eta-beta-spec-cong : {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> Γ ▷ A ==>
              app (A [[ ↓ A ]])
                  (B [[ ↑ A (↓ A) ]])
                  ((lambda A B
                        (app (A [[ ↓ A ]])
                             (B [[ ↑ A (↓ A) ]])
                             (c [ ↓ A ])
                             (Π-eta-left3 A B c p)
                             (vv A)
                             (Π-eta-left2 A B c p)))
                    [ ↓ A ])
                  (Π-eta-aux-lm A B
                      (lambda A B
                        (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                       (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)))
                        (Π-eta-left7 A B c p))
                  (vv A)
                  (asm A)
                  ==
              app (A [[ ↓ A ]])
                  (B [[ ↑ A (↓ A) ]])
                  (lambda {Γ ▷ A}
                          (A [[ ↓ A ]])
                          (B [[ ↑ A (↓ A) ]])
                          ((app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                             (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))
                            [ ↑ A (↓ A) ]))
                  (Π-eta-beta-spec2-lm {Γ} A B c p)
                  (vv A)
                  (asm A)
               :: (B [[ ↑ A (↓ A) ]]) [[ els (asm A) ]]
Π-eta-beta-spec-cong {Γ} A B c p =
--  << Raw Γ >>  app A B c p a q ~ app A B c' p' a' q'
    pair (Raw-lm (app-cong-raw {Γ ▷ A} (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])   -- **** stuck here 2.6.0.1
                  ((lambda A B
                        (app (A [[ ↓ A ]])
                             (B [[ ↑ A (↓ A) ]])
                             (c [ ↓ A ])
                             (Π-eta-left3 A B c p)
                             (vv A)
                             (Π-eta-left2 A B c p)))
                    [ ↓ A ])
                  (lambda {Γ ▷ A}
                          (A [[ ↓ A ]])
                          (B [[ ↑ A (↓ A) ]])
                          ((app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                             (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))
                            [ ↑ A (↓ A) ]))
                    (Π-eta-aux-lm A B
                      (lambda A B
                        (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                       (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)))
                        (Π-eta-left7 A B c p))
                     (Π-eta-beta-spec2-lm {Γ} A B c p)
                      (Π-eta-beta-spec-cong2 {Γ} A B c p) (vv A) (vv A) (asm A) (asm A) (tmrefl (asm A))))
                                        (pair (Π-e {Γ ▷ A}
                                                   (A [[ ↓ A ]])
                                                   (B [[ ↑ A (↓ A) ]])
                                                   (lambda A B
                                                     (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                                                        (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))
                                                      [ ↓ A ])
                                                   (Π-eta-aux-lm A B
                                                   (lambda A B
                                                    (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                                                     (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)))
                                                     (Π-eta-left7 A B c p))
                                                   (vv A)
                                                   (asm A))
                                               (Π-e {Γ ▷ A}
                                                   (A [[ ↓ A ]])
                                                   (B [[ ↑ A (↓ A) ]])
                                                   (lambda (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])
                                                       (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                                                        (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)
                                                        [ ↑ A (↓ A) ]))
                                                   (Π-eta-beta-spec2-lm A B c p)
                                                   (vv A)
                                                   (asm A)))




Π-eta-beta-spec : {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> Γ ▷ A ==>
              app (A [[ ↓ A ]])
                  (B [[ ↑ A (↓ A) ]])
                  ((lambda A B
                        (app (A [[ ↓ A ]])
                             (B [[ ↑ A (↓ A) ]])
                             (c [ ↓ A ])
                             (Π-eta-left3 A B c p)
                             (vv A)
                             (Π-eta-left2 A B c p)))
                    [ ↓ A ])
                  (Π-eta-aux-lm A B
                      (lambda A B
                        (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                       (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)))
                        (Π-eta-left7 A B c p))
                  (vv A)
                  (asm A)
                  ==
              app (A [[ ↓ A ]])
                  (B [[ ↑ A (↓ A) ]])
                  (c [ ↓ A ])
                  (Π-eta-aux-lm A B c p)
                  (vv A)
                  (asm A)
               :: (B [[ ↑ A (↓ A) ]]) [[ els (asm A) ]]
Π-eta-beta-spec {Γ} A B c p =
         tmtra {Γ ▷ A} ((B [[ ↑ A (↓ A) ]]) [[ els (asm A) ]])
                   _ _
                   (app (A [[ ↓ A ]])
                     (B [[ ↑ A (↓ A) ]])
                     (c [ ↓ A ])
                     (Π-eta-aux-lm A B c p)
                     (vv A)
                     (asm A))
                   (Π-eta-beta-spec-cong {Γ} A B c p)
                   (Π-eta-beta-spec2 {Γ} A B c p)

-- **** stuck here 2.6.0.1


-- ... and now the eta equality

Π-eta-eq :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> Γ ==> lambda A B (app (A [[ ↓ A ]])
                             (B [[ ↑ A (↓ A) ]])
                             (c [ ↓ A ])
                             (Π-eta-left3 {Γ} A B c p)
                             (vv A)
                             (Π-eta-left2 {Γ} A B c p))
             == c ::  Π-f {Γ} A B
Π-eta-eq {Γ} A B c p =
    let   eq : Γ ▷ A ==>
              app (A [[ ↓ A ]])
                  (B [[ ↑ A (↓ A) ]])
                  (lambda A B
                        (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                        (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))
                     [ ↓ A ])
                  (Π-eta-aux-lm A B    -- **** stuck here 2.6.0.1
                      (lambda A B
                        (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                       (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)))
                        (Π-eta-left7 A B c p))
                  (vv A)
                  (asm A)
                  ==
               app (A [[ ↓ A ]])
                   (B [[ ↑ A (↓ A) ]])
                   (c [ ↓ A ])
                   (Π-eta-aux-lm A B c p)
                   (vv A)
                   (asm A)
               :: (B [[ ↑ A (↓ A) ]]) [[ els (asm A) ]]
          eq = Π-eta-beta-spec {Γ} A B c p

    in Π-ext {Γ} A B
           (lambda A B (app (A [[ ↓ A ]])
                       (B [[ ↑ A (↓ A) ]])
                       (c [ ↓ A ])
                       (Π-eta-left3 {Γ} A B c p)
                       (vv A)
                       (Π-eta-left2 {Γ} A B c p)))
           c
           (Π-eta-left7 {Γ} A B c p)
           p
           eq


Π-eta-eq-gen-lm2 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)

    -> (q1 : (Γ ▷ A) ==> vv A ::  A [[ ↓ A ]])
    -> (q2 : (Γ ▷ A) ==> (c [ ↓ A ]) ::   (Π-f {Γ ▷ A} (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])))

    -> << Raw (Γ ▷ A) >>
      app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ]) q2 (vv A) q1 ~
      app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
         (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)
Π-eta-eq-gen-lm2 {Γ} A B c p q1 q2 =
    app-irr {Γ ▷ A} (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])  (c [ ↓ A ]) q2  (Π-eta-left3 A B c p) (vv A) q1  (Π-eta-left2 A B c p)

-- **** stuck here 2.6.0.1


Π-eta-eq-gen-lm :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)

    -> (q1 : (Γ ▷ A) ==> vv A ::  A [[ ↓ A ]])
    -> (q2 : (Γ ▷ A) ==> (c [ ↓ A ]) ::   (Π-f {Γ ▷ A} (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])))
    -> << Raw Γ >> (lambda A B (app (A [[ ↓ A ]])
                             (B [[ ↑ A (↓ A) ]])
                             (c [ ↓ A ])
                             q2
                             (vv A)
                             q1))
                ~
                 lambda A B (app (A [[ ↓ A ]])
                             (B [[ ↑ A (↓ A) ]])
                             (c [ ↓ A ])
                             (Π-eta-left3 {Γ} A B c p)
                             (vv A)
                             (Π-eta-left2 {Γ} A B c p))
Π-eta-eq-gen-lm {Γ} A B c p q1 q2 =
         Raw-lm2              -- **** stuck here 2.6.0.1
            ( λ x →
             Π-xi-raw {Γ} A {B}
                      (app (A [[ ↓ A ]])
                             (B [[ ↑ A (↓ A) ]])
                             (c [ ↓ A ])
                             q2
                             (vv A)
                             q1)
                      (app (A [[ ↓ A ]])
                             (B [[ ↑ A (↓ A) ]])
                             (c [ ↓ A ])
                             (Π-eta-left3 {Γ} A B c p)
                             (vv A)
                             (Π-eta-left2 {Γ} A B c p)) (Π-eta-eq-gen-lm2 {Γ} A B c p q1 q2) x)


Π-eta-eq-gen :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)

    -> (q1 : (Γ ▷ A) ==> vv A ::  A [[ ↓ A ]])
    -> (q2 : (Γ ▷ A) ==> (c [ ↓ A ]) ::   (Π-f {Γ ▷ A} (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])))
    -> Γ ==> lambda A B (app (A [[ ↓ A ]])
                             (B [[ ↑ A (↓ A) ]])
                             (c [ ↓ A ])
                             q2
                             (vv A)
                             q1)
             == c ::  Π-f {Γ} A B
Π-eta-eq-gen {Γ} A B c p q1 q2 =
-- **** stuck here 2.6.0.1
   let eq = Π-eta-eq-gen-lm {Γ} A B c p q1 q2
       eq2 : << Raw Γ >>  (lambda A B
                  (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                   (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))) ~ c
       eq2 =  Raw-lm2 (prj1 (Π-eta-eq {Γ} A B c p))
       eq3 : << Raw Γ >>
                 lambda A B
              (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ]) q2 (vv A) q1)
                 ~ c
       eq3 = tra' { Raw Γ } {lambda A B
            (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ]) q2 (vv A) q1)} { (lambda A B
                  (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                   (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)))} {c} eq eq2
   in pair (Raw-lm eq3) (pair (subj-red {Γ} { Π-f A B }
                 (lambda A B
                  (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                   (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p)))
                  (lambda A B
                      (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ]) q2 (vv A) q1)) (prj1 (prj2 (Π-eta-eq {Γ} A B c p)))
                      (sym' { Raw Γ } {lambda A B
                                       (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ]) q2 (vv A) q1)}
                                      {lambda A B
                                       (app (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ])
                                         (Π-eta-left3 A B c p) (vv A) (Π-eta-left2 A B c p))} eq)) p)


{-- ***

 *** --}


{--   --}
