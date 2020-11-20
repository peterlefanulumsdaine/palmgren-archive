-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt5 where

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
open import V-model-pt4
--

-- towards verifying extensional Pi-axioms

Π-extensionality-prop :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (x : || κ Γ ||)
    -> (u y :  # (apt A  x))
    -> (q : < κ (apt A x) > u ~ y)
    ->  < κ (apt B (x , y)) >
           ap (κ-Fam ±±  (extensionality1 (ty.type B) (x , u) (x , y) (<> (pairV-ext (refV _) (>< q)))))
              (pj1 (pj1 (apel p x)) u)
              ~
              pj1 (pj1 (apel p x)) y
Π-extensionality-prop {Γ} A B c p x u y q =  pj2 (pj1 (apel p x)) u y q





Π-eta-aux-lm :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
-- ---------------------------------------------
    -> Γ ▷ A ==> c [ ↓ A ] :: Π-f  (A [[ ↓ A ]]) (B [[ ↑ A ( ↓ A) ]])
Π-eta-aux-lm {Γ} A B c p = elttyeq (elt-subst (↓ A) p) (Π-f-sub A B (↓ A))




Π-eta-aux-lm2 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (x  : || κ Γ ||)
    -> (y  : # (apt A x) )
    -> (apr (c [ ↓ A ]) (x , y)) ∈ (apt (Π-f  (A [[ ↓ A ]]) (B [[ ↑ A ( ↓ A) ]])) (x , y))
Π-eta-aux-lm2 {Γ} A B c p x y = apel (Π-eta-aux-lm {Γ} A B c p) (x , y)




Π-ext3 : {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (x : || κ Γ ||)
    -> (y : || κ (apt A x) ||)
    ->  || κ (apt B (x , y)) ||
Π-ext3 {Γ} A B c p x y = pj1 (pj1 (apel p x)) y


Π-ext2b : {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c d : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (q : Γ ==> d :: Π-f A B)
    -> ((x : || κ Γ ||) -> (y : || κ (apt A x) ||) -> < κ (apt B (x , y)) > pj1 (pj1 (apel p x)) y ~ pj1 (pj1 (apel q x)) y)
    -> (x : || κ Γ ||)
    -> apr c x ≐ apr d x
Π-ext2b {Γ} A B c d p q r x =
    let lm1 : apr c x ≐ apt (Π-f A B) x ‣ pj1 (apel p x)
        lm1 = pj2 (apel p x)
        lm2 : apr d x ≐ apt (Π-f A B) x ‣ pj1 (apel q x)
        lm2 = pj2 (apel q x)
        lm3 : apt (Π-f A B) x ‣ pj1 (apel p x) ≐ apt (Π-f A B) x ‣ pj1 (apel q x)
        lm3 = Π-f-exp6 A B x (pj1 (apel p x)) (pj1 (apel q x)) (\ y -> (>< (r x y)))
    in traV lm1 (traV lm3 (symV lm2))




Π-ext2 : {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c d : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (q : Γ ==> d :: Π-f A B)
    -> ((x : || κ Γ ||) -> (y : || κ (apt A x) ||) -> < κ (apt B (x , y)) > pj1 (pj1 (apel p x)) y ~ pj1 (pj1 (apel q x)) y)
    -> (Γ ==> c == d :: Π-f A B)
Π-ext2 A B c d p q r = pair (λ x → Π-ext2b A B c d p q r x) (pair p q)



Π-ext-eq3-lm :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (x : || κ Γ ||)
    -> (y : || κ (apt A x) ||)
   ->  (apt B (x , (ap (κ-Fam ±± (<<>> (symV (refV (apt A (aps (↓ A) (x , y))))))) y))) ‣
                ((pj1 (pj1 (apel p x))) (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y))))))
                                             y))
       ≐  (apt B (x , y)) ‣ (pj1 (pj1 (apel p x)) y)
Π-ext-eq3-lm {Γ} A B c p x y =
   let eq : < κ (apt A x) > (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y)))))) y) ~ y
       eq = κ-trp-id (>><< (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y)))))) y

       eq3 = Π-f-exp3b A B x (pj1 (apel p x)) y (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y))))))
                                             y) (symV (>< eq))

   in symV eq3



Π-ext-eq4 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (x : || κ Γ ||)
    -> (y : || κ (apt A x) ||)
    ->  (apt (B [[ ↑ A (↓ A) ]]) ((x , y) , y)) ‣
                                      (ap (κ-Fam ±± (Fxx-lm' (ap1 (mk-Par A B) (aps (↓ A) (x , y)))
                                                             (ap1 (mk-Par (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])) (x , y))
                                                             (mk-Par-sub A B (↓ A) (x , y))
                                                            y))
                                        ((pj1 (pj1 (apel p x)))
                                         (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y))))))
                                             y)))

               ≐
             (apt B (x , (ap (κ-Fam ±± (<<>> (symV (refV (apt A (aps (↓ A) (x , y))))))) y))) ‣
                ((pj1 (pj1 (apel p x))) (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y))))))
                                             y))

Π-ext-eq4 {Γ} A B c p x y = symV (e+prop (>><< (Fxx-lm' (ap1 (mk-Par A B) (aps (↓ A) (x , y)))
                                                             (ap1 (mk-Par (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])) (x , y))
                                                             (mk-Par-sub A B (↓ A) (x , y))
                                                            y)) ((pj1 (pj1 (apel p x)))
                                         (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y))))))
                                             y)) )




Π-ext-eq3 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (x : || κ Γ ||)
    -> (y : || κ (apt A x) ||)
    -> (apt (B [[ ↑ A (↓ A) ]]) ((x , y) , pj1 (apel (asm A) (x , y)))) ‣
                                      (ap (κ-Fam ±± (Fxx-lm' (ap1 (mk-Par A B) (aps (↓ A) (x , y)))
                                                             (ap1 (mk-Par (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])) (x , y))
                                                             (mk-Par-sub A B (↓ A) (x , y))
                                                            y))
                                        ((pj1 (pj1 (apel p x)))
                                         (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y))))))
                                             y)))

               ≐  (apt B (x , y)) ‣ (pj1 (pj1 (apel p x)) y)
Π-ext-eq3 {Γ} A B c p x y =
  let lm1  :  (apt B (x , (ap (κ-Fam ±± (<<>> (symV (refV (apt A (aps (↓ A) (x , y))))))) y))) ‣
                ((pj1 (pj1 (apel p x))) (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y))))))
                                             y))
             ≐  (apt B (x , y)) ‣ (pj1 (pj1 (apel p x)) y)
      lm1 = Π-ext-eq3-lm {Γ} A B c p x y

      lm2 : (apt (B [[ ↑ A (↓ A) ]]) ((x , y) , y)) ‣
                                      (ap (κ-Fam ±± (Fxx-lm' (ap1 (mk-Par A B) (aps (↓ A) (x , y)))
                                                             (ap1 (mk-Par (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])) (x , y))
                                                             (mk-Par-sub A B (↓ A) (x , y))
                                                            y))
                                        ((pj1 (pj1 (apel p x)))
                                         (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y))))))
                                             y)))

               ≐
             (apt B (x , (ap (κ-Fam ±± (<<>> (symV (refV (apt A (aps (↓ A) (x , y))))))) y))) ‣
                ((pj1 (pj1 (apel p x))) (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y))))))
                                             y))
      lm2 = Π-ext-eq4 {Γ} A B c p x y

      main : (apt (B [[ ↑ A (↓ A) ]]) ((x , y) , y)) ‣
                                      (ap (κ-Fam ±± (Fxx-lm' (ap1 (mk-Par A B) (aps (↓ A) (x , y)))
                                                             (ap1 (mk-Par (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])) (x , y))
                                                             (mk-Par-sub A B (↓ A) (x , y))
                                                            y))
                                        ((pj1 (pj1 (apel p x)))
                                         (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y))))))
                                             y)))

               ≐  (apt B (x , y)) ‣ (pj1 (pj1 (apel p x)) y)
      main = traV lm2 lm1
  in main



Π-ext-eq2 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (x : || κ Γ ||)
    -> (y : || κ (apt A x) ||)
    ->  (apt (B [[ ↑ A (↓ A) ]]) ((x , y) , pj1 (apel (asm A) (x , y)))) ‣
                      (pj1
                         (e+ (>><< (ape (Π-f-sub A B (↓ A)) (x , y))) (pj1 (apel p x)))
                         y)
        ≐ (apt B (x , y)) ‣ (pj1 (pj1 (apel p x)) y)
Π-ext-eq2 {Γ} A B c p x y = Π-ext-eq3 {Γ} A B c p x y

-- Here is a detour we take to try solve some performance issues of Agda regarding unification

Π-ext-eq1b :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (x : || κ Γ ||)
    -> (y : || κ (apt A x) ||)
    ->         (apt  (B [[ ↑ A (↓ A) ]]) ((x , y),  y) ‣
              (pj1 (pj1 (apel (elttyeq (elt-subst (↓ A) p) (Π-f-sub A B (↓ A)))
                             (x , y))) (pj1 (apel (asm A) (x , y)))))
               ≐
              apt (B [[ ↑ A (↓ A) ]]) ((x , y) , y) ‣
                ap (κ-Fam ±± (Fxx-lm' (ap1 (mk-Par A B) (aps (↓ A) (x , y)))
                      (ap1 (mk-Par (A [[ (↓ A) ]]) (B [[ ↑ A (↓ A) ]]) ) (x , y)) (mk-Par-sub A B (↓ A) (x , y)) y))
                    ((pj1 (pj1 (apel (elt-subst (↓ A) p) (x , y))))
                      (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y)))))) y))
Π-ext-eq1b {Γ} A B c p x y  =
   let lm = pj2 (apel (elttyeq (elt-subst (↓ A) p) (Π-f-sub A B (↓ A)))
                             (x , y))
       lm1 :  (apt  (B [[ ↑ A (↓ A) ]]) ((x , y),  y) ‣
              (pj1 (pj1 (apel (elttyeq (elt-subst (↓ A) p) (Π-f-sub A B (↓ A)))
                             (x , y))) (pj1 (apel (asm A) (x , y)))))
               ≐
              (apt  (B [[ ↑ A (↓ A) ]]) ((x , y),  y) ‣
              (pj1 (e+ (>><< (ape (Π-f-sub A B (↓ A)) (x , y)))
                 (pj1 (apel (elt-subst (↓ A) p) (x , y)))) (pj1 (apel (asm A) (x , y)))))
       lm1 = refV _

       tst : apt (Π-f A B [[ ↓ A ]]) (x , y) ≐ apt (Π-f (A [[ ↓ A ]]) (B [[ ↑ A (↓ A) ]])) (x , y)
        --  tst = (>><< (ape (Π-f-sub A B (↓ A)) (x , y)))
       {-- tst =     >><<    (extensionality11 piVV
                              (ap1 (mk-Par A B) (aps ( ↓ A) (x , y)))
                              (ap1 (mk-Par (A [[  ↓ A ]]) (B [[ ↑ A ( ↓ A) ]])) (x , y))
                              (mk-Par-sub {Γ ▷ A} {Γ} A B ( ↓ A) (x , y))) --}
   {--    tst =     >><<    (piV-ext
                              (ap1 (mk-Par A B) (aps ( ↓ A) (x , y)))
                              (ap1 (mk-Par (A [[  ↓ A ]]) (B [[ ↑ A ( ↓ A) ]])) (x , y))
                              (mk-Par-sub {Γ ▷ A} {Γ} A B ( ↓ A) (x , y)))
   --}
       tst =     (extensional-eqV (piV-op (ap1 (mk-Par A B) (aps ( ↓ A) (x , y))))
                                  (piV-op (ap1 (mk-Par (A [[  ↓ A ]]) (B [[ ↑ A ( ↓ A) ]])) (x , y)))
                                  (piV-half-ext (ap1 (mk-Par A B) (aps ( ↓ A) (x , y)))
                                             (ap1 (mk-Par (A [[  ↓ A ]]) (B [[ ↑ A ( ↓ A) ]])) (x , y))
                                               (mk-Par-sub {Γ ▷ A} {Γ} A B ( ↓ A) (x , y)))
                                  (piV-half-ext (ap1 (mk-Par (A [[  ↓ A ]]) (B [[ ↑ A ( ↓ A) ]])) (x , y))
                                              (ap1 (mk-Par A B) (aps ( ↓ A) (x , y)))
                                              (sym' {Par VV κ-Fam}
                                                   {(ap1 (mk-Par A B) (aps ( ↓ A) (x , y)))}
                                                   {(ap1 (mk-Par (A [[  ↓ A ]]) (B [[ ↑ A ( ↓ A) ]])) (x , y))}
                                              (mk-Par-sub {Γ ▷ A} {Γ} A B ( ↓ A) (x , y)))))


       lm2 : (apt  (B [[ ↑ A (↓ A) ]]) ((x , y),  y) ‣
              (pj1 (e+ (>><< (ape (Π-f-sub A B (↓ A)) (x , y)))
                 (pj1 (apel (elt-subst (↓ A) p) (x , y)))) (pj1 (apel (asm A) (x , y)))))
              ≐
             (apt  (B [[ ↑ A (↓ A) ]]) ((x , y),  y) ‣
              (pj1 (e+ tst
                 (pj1 (apel (elt-subst (↓ A) p) (x , y)))) (pj1 (apel (asm A) (x , y)))))
       lm2 = refV _

       lm3 : (apt  (B [[ ↑ A (↓ A) ]]) ((x , y),  y) ‣
              (pj1 (e+ (>><< (ape (Π-f-sub A B (↓ A)) (x , y)))
                 (pj1 (apel (elt-subst (↓ A) p) (x , y)))) (pj1 (apel (asm A) (x , y)))))
              ≐
              apt (B [[ ↑ A (↓ A) ]]) ((x , y) , y) ‣
                ap (κ-Fam ±± (Fxx-lm' (ap1 (mk-Par A B) (aps (↓ A) (x , y)))
                      (ap1 (mk-Par (A [[ (↓ A) ]]) (B [[ ↑ A (↓ A) ]]) ) (x , y)) (mk-Par-sub A B (↓ A) (x , y)) y))
                    ((pj1 (pj1 (apel (elt-subst (↓ A) p) (x , y))))
                      (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y)))))) y))
       lm3 = refV _

   in (traV lm1 lm3)

Π-ext-eq1 :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (x : || κ Γ ||)
    -> (y : || κ (apt A x) ||)
    -> apr (app (A [[ ↓ A ]])  (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ]) (Π-eta-aux-lm A B c p) (vv A) (asm A)) (x , y) ≐
       (apt (B [[ ↑ A (↓ A) ]]) ((x , y) , pj1 (apel (asm A) (x , y)))) ‣
                      (pj1
                         (e+ (>><< (ape (Π-f-sub A B (↓ A)) (x , y))) (pj1 (apel p x)))
                         y)
Π-ext-eq1 {Γ} A B c p x y  =
  let lm : apr (app (A [[ ↓ A ]])  (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ]) (Π-eta-aux-lm A B c p) (vv A) (asm A)) (x , y) ≐
           (apt  (B [[ ↑ A (↓ A) ]]) ((x , y) ,
            (pj1 (apel (asm A) (x , y)))) ‣
              (pj1 (pj1 (apel (Π-eta-aux-lm A B c p) (x , y))) (pj1 (apel (asm A) (x , y)))))
      lm = refV _
      lm0 : (apt  (B [[ ↑ A (↓ A) ]]) ((x , y),  y) ‣
              (pj1 (pj1 (apel (Π-eta-aux-lm {Γ} A B c p) (x , y))) (pj1 (apel (asm A) (x , y)))))  ≐
            (apt  (B [[ ↑ A (↓ A) ]]) ((x , y),  y) ‣
              (pj1 (pj1 (apel (elttyeq (elt-subst (↓ A) p) (Π-f-sub A B (↓ A)))
                             (x , y))) (pj1 (apel (asm A) (x , y)))))
      lm0 = refV _
      lm05 : apt (B [[ ↑ A (↓ A) ]]) ((x , y) , y) ‣
                ap (κ-Fam ±± (Fxx-lm' (ap1 (mk-Par A B) (aps (↓ A) (x , y)))
                      (ap1 (mk-Par (A [[ (↓ A) ]]) (B [[ ↑ A (↓ A) ]]) ) (x , y)) (mk-Par-sub A B (↓ A) (x , y)) y))
                    ((pj1 (pj1 (apel (elt-subst (↓ A) p) (x , y))))
                      (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y)))))) y))
               ≐
             apt (B [[ ↑ A (↓ A) ]]) ((x , y) , y) ‣
              piV-ext00 {(ap1 (mk-Par A B) (aps (↓ A) (x , y)))}
                        {(ap1 (mk-Par (A [[ (↓ A) ]]) (B [[ ↑ A (↓ A) ]]) ) (x , y))}  (mk-Par-sub A B (↓ A) (x , y))
              (pj1 (pj1 (apel (elt-subst (↓ A) p) (x , y)))) y
      lm05 = refV _


      lm08 : (apt  (B [[ ↑ A (↓ A) ]]) ((x , y),  y) ‣
              (pj1 (pj1 (apel (elttyeq (elt-subst (↓ A) p) (Π-f-sub A B (↓ A)))
                             (x , y))) (pj1 (apel (asm A) (x , y)))))
               ≐
              apt (B [[ ↑ A (↓ A) ]]) ((x , y) , y) ‣
                ap (κ-Fam ±± (Fxx-lm' (ap1 (mk-Par A B) (aps (↓ A) (x , y)))
                      (ap1 (mk-Par (A [[ (↓ A) ]]) (B [[ ↑ A (↓ A) ]]) ) (x , y)) (mk-Par-sub A B (↓ A) (x , y)) y))
                    ((pj1 (pj1 (apel (elt-subst (↓ A) p) (x , y))))
                      (ap (κ-Fam ±± (sym' (pj1 (>><< (mk-Par-sub A B (↓ A) (x , y)))))) y))
      lm08 =  Π-ext-eq1b {Γ} A B c p x y



      lm1 : (apt  (B [[ ↑ A (↓ A) ]]) ((x , y),  y) ‣
              (pj1 (pj1 (apel (Π-eta-aux-lm {Γ} A B c p) (x , y))) (pj1 (apel (asm A) (x , y)))))  ≐
             apt (B [[ ↑ A (↓ A) ]]) ((x , y) , y) ‣
              piV-ext00 {(ap1 (mk-Par A B) (aps (↓ A) (x , y)))}
                        {(ap1 (mk-Par (A [[ (↓ A) ]]) (B [[ ↑ A (↓ A) ]]) ) (x , y))}  (mk-Par-sub A B (↓ A) (x , y))
              (pj1 (pj1 (apel (elt-subst (↓ A) p) (x , y)))) y
      lm1 = traV lm0  (traV lm08 lm05) -- refV _  works too, but also unifies very slowly


      lm2 : apt (B [[ ↑ A (↓ A) ]]) ((x , y) , y) ‣
              piV-ext00 (mk-Par-sub A B (↓ A) (x , y))
              (pj1 (pj1 (apel (elt-subst (↓ A) p) (x , y)))) y
                  ≐
            apt (B [[ ↑ A (↓ A) ]]) ((x , y) , y) ‣
               piV-ext00 (mk-Par-sub A B (↓ A) (x , y)) (pj1 (pj1 (apel p x))) y
      lm2 = refV _
      lm3 :  apt (B [[ ↑ A (↓ A) ]]) ((x , y) , y) ‣
               piV-ext00 (mk-Par-sub A B (↓ A) (x , y)) (pj1 (pj1 (apel p x))) y  ≐
            (apt (B [[ ↑ A (↓ A) ]]) ((x , y) , pj1 (apel (asm A) (x , y)))) ‣
                      (pj1
                         (e+ (>><< (ape (Π-f-sub A B (↓ A)) (x , y))) (pj1 (apel p x)))
                         y)
      lm3 = refV _


  in traV lm (traV (traV lm1 lm2) lm3)

--  refV _ -- works too, but also unifies very slowly


Π-ext-eq :  {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (x : || κ Γ ||)
    -> (y : || κ (apt A x) ||)
    -> apr (app (A [[ ↓ A ]])  (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ]) (Π-eta-aux-lm A B c p) (vv A) (asm A)) (x , y) ≐
             ((apt B (x , y)) ‣ (pj1 (pj1 (apel p x)) y))

Π-ext-eq {Γ} A B c p x y =  traV (Π-ext-eq1 {Γ} A B c p x y) (Π-ext-eq2 {Γ} A B c p x y)

 --  Π-ext-eq2 {Γ} A B c p x y -- works as well, but is slower




Π-ext : {Γ : ctx}
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c d : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (q : Γ ==> d :: Π-f A B)
    ->  (Γ ▷ A ==> app (A [[ ↓ A ]])  (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ]) (Π-eta-aux-lm A B c p) (vv A) (asm A) ==
                   app (A [[ ↓ A ]])  (B [[ ↑ A (↓ A) ]]) (d [ ↓ A ]) (Π-eta-aux-lm A B d q) (vv A) (asm A)
              :: (B [[ ↑ A (↓ A) ]])  [[ els (asm A) ]])
    -> (Γ ==> c == d :: Π-f A B)
Π-ext {Γ} A B c d p q r =
 let lm : (x : || κ Γ ||) -> (y : || κ (apt A x) ||) ->
            < κ (apt B (x , y)) > pj1 (pj1 (apel p x)) y ~
                                  pj1 (pj1 (apel q x)) y

     lm = λ x y →
        let  lm2 : apr (app (A [[ ↓ A ]])  (B [[ ↑ A (↓ A) ]]) (c [ ↓ A ]) (Π-eta-aux-lm A B c p) (vv A) (asm A)) (x , y) ≐
                   apr (app (A [[ ↓ A ]])  (B [[ ↑ A (↓ A) ]]) (d [ ↓ A ]) (Π-eta-aux-lm A B d q) (vv A) (asm A)) (x , y)
             lm2 = (prj1 r) (x , y)
             main : < κ (apt B (x , y)) > pj1 (pj1 (apel p x)) y ~  pj1 (pj1 (apel q x)) y
             main = <> (traV (symV (Π-ext-eq A B c p x y)) (traV lm2 (Π-ext-eq A B d q x y)))
        in main
 in Π-ext2 A B c d p q lm

