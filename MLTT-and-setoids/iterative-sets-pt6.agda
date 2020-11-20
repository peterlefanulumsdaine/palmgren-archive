-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module iterative-sets-pt6 where

open import basic-types
open import basic-setoids
open import dependent-setoids
open import subsetoids
open import iterative-sets
open import iterative-sets-pt2
open import iterative-sets-pt3
open import iterative-sets-pt4
open import iterative-sets-pt5


-- to do :



-- uV : V
-- uV = sup sV emb

-- emb is onto uV

-- emb-surj-uV : (u : V) -> (u ∈ uV) -> Σ sV (\v -> emb v ≐ u)
-- emb-surj-uV u p = (pj1 p) , (symV (pj2 p))

reflect-set :  (I : Set) -> (F : I -> Set) -> (a : V) -> (a ∈ uV I F) -> sV I F
reflect-set I F a p = pj1 (emb-surj-uV I F a p)

reflect-set-prop :  (I : Set) -> (F : I -> Set) -> (a : V) -> (p : a ∈ uV I F) 
                    -> emb I F (reflect-set I F a p) ≐ a
reflect-set-prop I F a p = pj2 (emb-surj-uV I F a p)

reflect-set-map :  (I : Set) -> (F : I -> Set) -> (a : V) -> (p : a ∈ uV I F) ->
   setoidmap (κ (emb I F (reflect-set I F a p))) (κ a)
reflect-set-map I F a p = κ-trp (reflect-set-prop I F a p)

-- κ-trp : {a b : V} -> (p : a ≐ b) -> || κ a  => κ b ||

reflect-family-op : (I : Set) -> (F : I -> Set) 
            -> (a : sV I F) -> (g :  setoidmap1 (κ (emb I F a)) VV)
            -> ((x : || κ (emb I F a)||) -> ap1 g x ∈ uV I F)
            ->  || (κ (emb I F a)) || -> || sVV I F ||
reflect-family-op I F a g p x = pj1 (p x)


reflect-family :  (I : Set) -> (F : I -> Set) 
            -> (a : sV I F) -> (g :  setoidmap1 (κ (emb I F a)) VV)
            -> ((x : || κ (emb I F a)||) -> ap1 g x ∈ uV I F)
            ->  setoidmap (κ (emb I F a)) (sVV I F)
reflect-family I F a g p = 
  record { op = reflect-family-op I F a g p 
         ; ext = λ x y q → (
              let px = pj2 (p x)
                  py = pj2 (p y)
                  lm : emb I F (pj1 (p x))  ≐ emb I F (pj1 (p y))
                  lm = traV (symV px) (traV (>><< (extensionality1 g x y q)) py)
                  main : < sVV I F >  pj1 (p x) ~  pj1 (p y)
                  main = <> (emb-inj I F _ _ lm) 
               in main)
          }

sigmaV-refl-code :  (I : Set) -> (F : I -> Set) 
    -> (a : V) -> (g :  setoidmap1 (κ a) VV) 
    -> (a ∈ uV I F) 
    -> ((x : || κ a ||) -> ap1 g x ∈ uV I F)
    -> # (uV I F)
sigmaV-refl-code I F a g p q = 
     let  g' :  setoidmap1 (κ (emb I F (reflect-set I F a p))) VV
          g' = comp1 g (reflect-set-map I F a p)
          lm : ((x : || κ (emb I F (reflect-set I F a p))||) -> ap1 g' x ∈ uV I F)
          lm = λ x → (pj1 (q (ap (reflect-set-map I F a p) x))) ,
                     (pj2 (q (ap (reflect-set-map I F a p) x))) 
          main : # (uV I F)
          main = sigma-sV I F (reflect-set I F a p) (reflect-family I F (reflect-set I F a p) g' lm)
     in main 

-- emb-sigma-sV : (a : sV) -> (g : setoidmap (κ (emb a)) sVV)
--      -> emb (sigma-sV a g) ≐ sigmaV (emb a) (comp1 embVV g)


-- sigmaV-op : ||| Par VV κ-Fam ||| ->  ||| VV |||
-- sigmaV-op u = sigmaV (Ixx u) (Fxx u)

-- sigmaV-ext : (u v : ||| Par VV κ-Fam |||) -> << Par VV κ-Fam >> u ~ v -> << VV >>  sigmaV-op u ~ sigmaV-op v

mk-Par-V-κ-Fam : (a : V) -> (g :  setoidmap1 (κ a) VV) ->  ||| Par VV κ-Fam |||
mk-Par-V-κ-Fam a g = record { Ix = a ; 
                              Fx = g }

mk-Par-V-κ-Fam-ext :  (a b : V) -> (p : a ≐ b) 
    ->  (g :  setoidmap1 (κ a) VV) ->  (h :  setoidmap1 (κ b) VV) 
    -> << setoidmaps1 (κ a) VV >> g  ~ comp1 h (κ-trp p)             
    ->   << Par VV κ-Fam >> (mk-Par-V-κ-Fam a g)  ~ (mk-Par-V-κ-Fam b h)
mk-Par-V-κ-Fam-ext a b p g h r = <<>> ((<<>> p) , (λ t → <<>> (traV (>><< (>><< r t)) (refV _))))


mk-Par-V-κ-Fam-sigmaV : (a : V) -> (g :  setoidmap1 (κ a) VV) 
            -> sigmaV-op (mk-Par-V-κ-Fam a g) ≐  sigmaV a g
mk-Par-V-κ-Fam-sigmaV a g = refV _


sigmaV-ext2 :  (a b : V) -> (p : a ≐ b) 
    ->  (g :  setoidmap1 (κ a) VV) ->  (h :  setoidmap1 (κ b) VV) 
    -> << setoidmaps1 (κ a) VV >> g  ~ comp1 h (κ-trp p)
    ->  sigmaV a g ≐  sigmaV b h
sigmaV-ext2 a b p g h q = 
    >><< (sigmaV-ext (mk-Par-V-κ-Fam a g) (mk-Par-V-κ-Fam b h) 
                     (mk-Par-V-κ-Fam-ext a b p g h q))    


-- κ-trp-irr : {a b : V} -> (p q : a ≐ b) ->  (x : || κ a ||)
--      ->  < κ b > κ-trp-op p x ~ κ-trp-op q x
-- κ-trp-irr {a} {b} p q x = <> (traV (symV (e+prop p x)) (e+prop q x))

e+irr :  {a b : V} -> (p q : a ≐ b) ->  (x : # a) ->
                 b ‣ (e+ p x) ≐ b ‣ (e+ q x)
e+irr {a} {b} p q x = (traV (symV (e+prop p x)) (e+prop q x))





g-lm2 :  (I : Set) -> (F : I -> Set) 
    -> (a : V) -> (g :  setoidmap1 (κ a) VV) 
    -> (p : a ∈ uV I F) 
    -> (q : (x : || κ a ||) -> ap1 g x ∈ uV I F)
    -> (x : || κ (emb I F (reflect-set I F a p)) ||)
    -> emb I F (pj1 (q (ap (κ-trp (reflect-set-prop I F a p)) x))) ≐
        ap1 g (ap (κ-trp (reflect-set-prop I F a p)) x)
g-lm2 I F a g p q x = 
   let  lmq1 = pj1 (q (ap (κ-trp (reflect-set-prop I F a p)) x))
        lmq2 = pj2 (q (ap (κ-trp (reflect-set-prop I F a p)) x))
        main : emb I F (pj1 (q (ap (κ-trp (reflect-set-prop I F a p)) x))) ≐
             ap1 g (ap (κ-trp (reflect-set-prop I F a p)) x)
        main = traV (refV _) (symV lmq2)
   in main



-- reflect-set-map a p = κ-trp (reflect-set-prop a p)

g-lm :  (I : Set) -> (F : I -> Set) 
    -> (a : V) -> (g :  setoidmap1 (κ a) VV) 
    -> (p : a ∈ uV I F) 
    -> (q : (x : || κ a ||) -> ap1 g x ∈ uV I F)
    -> (x : || κ (emb I F (reflect-set I F a p)) ||)
    ->
      emb I F
      (ap
       (reflect-family I F (reflect-set I F a p) (comp1 g (reflect-set-map I F a p))
        (λ x₁ →
           pj1 (q (ap (reflect-set-map I F a p) x₁)) ,
           pj2 (q (ap (reflect-set-map I F a p) x₁))))
       x)
      ≐ ap1 g (ap (κ-trp (reflect-set-prop I F a p)) x)
g-lm I F a g p q x = 
   let lm : emb  I F (pj1 (q (ap (reflect-set-map I F a p) x)))
            ≐ ap1 g (ap (κ-trp (reflect-set-prop I F a p)) x)
       lm = g-lm2 I F a g p q x
       main : emb I F
           (ap
            (reflect-family I F (reflect-set I F a p) (comp1 g (reflect-set-map I F a p))
             (λ x₁ →
                pj1 (q (ap (reflect-set-map I F a p) x₁)) ,
                pj2 (q (ap (reflect-set-map I F a p) x₁))))
            x)
           ≐ ap1 g (ap (κ-trp (reflect-set-prop I F a p)) x)
       main = lm
   in main



-- reflect-family-op a g p x = pj1 (p x)

emb-sigma-refl-code :  (I : Set) -> (F : I -> Set) 
    -> (a : V) -> (g :  setoidmap1 (κ a) VV) 
    -> (p : a ∈ uV I F) 
    -> (q : (x : || κ a ||) -> ap1 g x ∈ uV I F)
    -> sigmaV a g ≐ emb I F (sigmaV-refl-code I F a g p q)
emb-sigma-refl-code I F a g p q = 
   let  g' :  setoidmap1 (κ (emb I F (reflect-set I F a p))) VV
        g' = comp1 g (reflect-set-map I F a p)
        lm : ((x : || κ (emb I F (reflect-set I F a p))||) -> ap1 g' x ∈ uV I F)
        lm = λ x → (pj1 (q (ap (reflect-set-map I F a p) x))) ,
                     (pj2 (q (ap (reflect-set-map I F a p) x)))  
        lm2 : emb I F (sigma-sV I F (reflect-set I F a p) (reflect-family I F (reflect-set I F a p) g' lm)) 
               ≐ 
              sigmaV (emb I F (reflect-set I F a p)) 
                     (comp1 (embVV I F) (reflect-family I F (reflect-set I F a p) g' lm))
        lm2 = emb-sigma-sV I F (reflect-set I F a p) (reflect-family I F (reflect-set I F a p) g' lm)

        geq : << setoidmaps1 (κ (emb I F (reflect-set I F a p))) VV >> 
               (comp1 (embVV I F) (reflect-family I F (reflect-set I F a p) g' lm)) ~ 
                comp1 g (κ-trp (reflect-set-prop I F a p))
        geq = <<>> (λ x → <<>>  (
                                let  
                                    lm :   emb I F (ap 
                                              (reflect-family I F (reflect-set I F a p) 
                                                             (comp1 g (reflect-set-map I F a p))
                                               (λ x₁ →
                                                  pj1 (q (ap (reflect-set-map I F a p) x₁)) ,
                                                  pj2 (q (ap (reflect-set-map I F a p) x₁))))
                                               x) ≐
                                             (ap1 g (ap (κ-trp (reflect-set-prop I F a p)) x))
                                    lm = g-lm I F a g p q x

                                    main :   (comp1 (embVV I F)
                                              (reflect-family I F (reflect-set I F a p) 
                                                          (comp1 g (reflect-set-map I F a p))
                                               (λ x₁ →
                                                  pj1 (q (ap (reflect-set-map I F a p) x₁)) ,
                                                  pj2 (q (ap (reflect-set-map I F a p) x₁))))
                                              • x) ≐
                                             (comp1 g (κ-trp (reflect-set-prop I F a p)) • x)
                                    main = lm
                                in main
                                 )
                   )
        lm3 : sigmaV a g 
                 ≐ 
              sigmaV (emb I F (reflect-set I F a p)) 
                     (comp1 (embVV I F) (reflect-family I F (reflect-set I F a p) g' lm))
        lm3 = symV (sigmaV-ext2 (emb I F (reflect-set I F a p)) a (reflect-set-prop I F a p) 
                  ((comp1 (embVV I F) (reflect-family I F (reflect-set I F a p) g' lm))) g geq ) 
        main :  sigmaV a g ≐ emb I F (sigmaV-refl-code I F a g p q)
        main =  traV lm3 (symV lm2)
   in main 



sigmaV-reflection :  (I : Set) -> (F : I -> Set) 
    -> (a : V) -> (g :  setoidmap1 (κ a) VV) 
    -> (a ∈ uV I F) 
    -> ((x : || κ a ||) -> ap1 g x ∈ uV I F)
    -> sigmaV a g ∈ uV I F
sigmaV-reflection I F a g p q = 
         sigmaV-refl-code I F a g p q , emb-sigma-refl-code I F a g p q




piV-refl-code :  (I : Set) -> (F : I -> Set) 
    -> (a : V) -> (g :  setoidmap1 (κ a) VV) 
    -> (a ∈ uV I F) 
    -> ((x : || κ a ||) -> ap1 g x ∈ uV I F)
    -> # (uV I F)
piV-refl-code I F a g p q = 
     let  g' :  setoidmap1 (κ (emb I F (reflect-set I F a p))) VV
          g' = comp1 g (reflect-set-map I F a p)
          lm : ((x : || κ (emb I F (reflect-set I F a p))||) -> ap1 g' x ∈ uV I F)
          lm = λ x → (pj1 (q (ap (reflect-set-map I F a p) x))) ,
                     (pj2 (q (ap (reflect-set-map I F a p) x))) 
          main : # (uV I F)
          main = pi-sV I F (reflect-set I F a p) (reflect-family I F (reflect-set I F a p) g' lm)
     in main




piV-ext2 : (a b : V) -> (p : a ≐ b) 
    ->  (g :  setoidmap1 (κ a) VV) ->  (h :  setoidmap1 (κ b) VV) 
    -> << setoidmaps1 (κ a) VV >> g  ~ comp1 h (κ-trp p)
    ->  piV a g ≐  piV b h
piV-ext2 a b p g h q = 
    >><< (piV-ext (mk-Par-V-κ-Fam a g) (mk-Par-V-κ-Fam b h) 
                     (mk-Par-V-κ-Fam-ext a b p g h q))    



emb-pi-refl-code :  (I : Set) -> (F : I -> Set) 
    -> (a : V) -> (g :  setoidmap1 (κ a) VV) 
    -> (p : a ∈ uV I F) 
    -> (q : (x : || κ a ||) -> ap1 g x ∈ uV I F)
    -> piV a g ≐ emb I F (piV-refl-code I F a g p q)
emb-pi-refl-code I F a g p q = 
   let  g' :  setoidmap1 (κ (emb I F (reflect-set I F a p))) VV
        g' = comp1 g (reflect-set-map I F a p)
        lm : ((x : || κ (emb I F (reflect-set I F a p))||) -> ap1 g' x ∈ uV I F)
        lm = λ x → (pj1 (q (ap (reflect-set-map I F a p) x))) ,
                     (pj2 (q (ap (reflect-set-map I F a p) x)))  
        lm2 : emb I F (pi-sV I F (reflect-set I F a p) (reflect-family I F (reflect-set I F a p) g' lm)) 
               ≐ 
              piV (emb I F (reflect-set I F a p)) (comp1 (embVV I F) (reflect-family I F (reflect-set I F a p) g' lm))
        lm2 = emb-pi-sV I F (reflect-set I F a p) (reflect-family I F (reflect-set I F a p) g' lm)

        geq : << setoidmaps1 (κ (emb I F (reflect-set I F a p))) VV >> 
               (comp1 (embVV I F) (reflect-family I F (reflect-set I F a p) g' lm)) ~ 
                comp1 g (κ-trp (reflect-set-prop I F a p))
        geq = <<>> (λ x → <<>>  (
                                let  
                                    lm :   emb I F (ap 
                                              (reflect-family I F (reflect-set I F a p) 
                                                              (comp1 g (reflect-set-map I F a p))
                                               (λ x₁ →
                                                  pj1 (q (ap (reflect-set-map I F a p) x₁)) ,
                                                  pj2 (q (ap (reflect-set-map I F a p) x₁))))
                                               x) ≐
                                             (ap1 g (ap (κ-trp (reflect-set-prop I F a p)) x))
                                    lm = g-lm I F a g p q x

                                    main :   (comp1 (embVV I F)
                                              (reflect-family I F (reflect-set I F a p) 
                                                               (comp1 g (reflect-set-map I F a p))
                                               (λ x₁ →
                                                  pj1 (q (ap (reflect-set-map I F a p) x₁)) ,
                                                  pj2 (q (ap (reflect-set-map I F a p) x₁))))
                                              • x) ≐
                                             (comp1 g (κ-trp (reflect-set-prop I F a p)) • x)
                                    main = lm
                                in main
                                 )
                   )
        lm3 : piV a g 
                 ≐ 
              piV (emb I F (reflect-set I F a p)) 
                  (comp1 (embVV I F) (reflect-family I F (reflect-set I F a p) g' lm))
        lm3 = symV (piV-ext2 (emb I F (reflect-set I F a p)) a (reflect-set-prop I F a p) 
                  ((comp1 (embVV I F) (reflect-family I F (reflect-set I F a p) g' lm))) g geq ) 
        main :  piV a g ≐ emb I F (piV-refl-code I F a g p q)
        main =  traV lm3 (symV lm2)
   in main 



piV-reflection :  (I : Set) -> (F : I -> Set) 
    -> (a : V) -> (g :  setoidmap1 (κ a) VV) 
    -> (a ∈ uV I F) 
    -> ((x : || κ a ||) -> ap1 g x ∈ uV I F)
    -> piV a g ∈ uV I F
piV-reflection I F a g p q = piV-refl-code I F a g p q , emb-pi-refl-code I F a g p q



-- Extensional identity types


idV : (a : V) -> (x y : || κ a ||) -> V
idV a x y = sup (a ‣ x ≐ a ‣ y) (\u -> a ‣ x)



id-sV :  (I : Set) -> (F : I -> Set) 
    -> (a : sV I F) -> (x y : || κ (emb I F a) ||) -> sV I F
id-sV I F a x y = sup (eq-sV I F (bsV I F a (emb- I F a x)) (bsV I F a (emb- I F a y))) 
                   (\u ->  (bsV I F a (emb- I F a x))) 

emb-idV :  (I : Set) -> (F : I -> Set) 
    -> (a : sV I F) -> (x y : || κ (emb I F a) ||) 
     -> emb I F (id-sV I F a x y) ≐ idV (emb I F a) x y
emb-idV I F (sup A f) x y = 
    let main : sup (To {I} {F} (eq-sV I F (f x) (f y))) (λ x₁ → emb I F (f x)) 
                ≐ sup (emb I F (f x) ≐ emb I F (f y)) (\u -> emb I F (f x))
        main = pair (λ p → (emb-ext I F (f x) (f y) p) , (refV _)) 
                    (λ p → (emb-inj I F (f x) (f y) p) , (refV _))
    in main




idV-reflection-lm0 :  (I : Set) -> (F : I -> Set) 
           -> (a : V) -> (x : || κ a ||) 
           -> (p : a ∈ uV I F)
           -> a ‣ x ≐ emb I F (bsV I F (pj1 p) (emb- I F (pj1 p) (κ-trp-op (pj2 p) x)))
idV-reflection-lm0 I F a x p =
  let lm :  a ‣ x ≐ (emb I F (pj1 p)) ‣ (κ-trp-op (pj2 p) x)
      lm = e+prop (pj2 p) x
  in  symV (traV (emb-bsV I F (pj1 p) (emb- I F (pj1 p) (κ-trp-op (pj2 p) x))) 
                         (symV (traV lm (>< (emb+- I F (pj1 p) (κ-trp-op (pj2 p) x))))))



idV-reflection-lm1 :  (I : Set) -> (F : I -> Set) 
           -> (a : V) -> (x y : || κ a ||) 
           -> (p : a ∈ uV I F)
           -> a ‣ x ≐ a ‣ y
           ->  To {I} {F} (eq-sV I F (bsV I F (pj1 p) (emb- I F (pj1 p) (κ-trp-op (pj2 p) x)))
                        (bsV I F (pj1 p) (emb- I F (pj1 p) (κ-trp-op (pj2 p) y))))
idV-reflection-lm1 I F a x y p q = emb-inj I F (bsV I F (pj1 p) (emb- I F (pj1 p) (κ-trp-op (pj2 p) x)))
                                    (bsV I F (pj1 p) (emb- I F (pj1 p) (κ-trp-op (pj2 p) y)))
                                    (traV (symV (idV-reflection-lm0 I F a x p))
                                          (traV q (idV-reflection-lm0 I F a y p)))



idV-reflection-lm2 :  (I : Set) -> (F : I -> Set) 
           -> (a : V) -> (x y : || κ a ||) 
           -> (p : a ∈ uV I F)
           ->  To {I} {F} (eq-sV I F (bsV I F (pj1 p) (emb- I F (pj1 p) (κ-trp-op (pj2 p) x)))
                        (bsV I F (pj1 p) (emb- I F (pj1 p) (κ-trp-op (pj2 p) y))))
           -> a ‣ x ≐ a ‣ y
idV-reflection-lm2 I F a x y p q = traV (idV-reflection-lm0 I F a x p) 
                                        (traV (emb-ext I F _ _ q) (symV (idV-reflection-lm0 I F a y p))) 


idV-reflection :   (I : Set) -> (F : I -> Set) 
           -> (a : V) -> (x y : || κ a ||) 
           -> (a ∈ uV I F)
           -> idV a x y ∈ uV I F
idV-reflection I F a x y p =
     (id-sV I F (pj1 p)  (κ-trp-op (pj2 p) x) (κ-trp-op (pj2 p) y)) ,
              pair (λ q → idV-reflection-lm1 I F a x y p q , idV-reflection-lm0 I F a x p) 
                   (λ q → idV-reflection-lm2 I F a x y p q , idV-reflection-lm0 I F a x p)



-- empty set


zeroV-reflection :  (I : Set) -> (F : I -> Set) 
                 -> zeroV ∈ uV I F
zeroV-reflection I F = zeroV-in-uV I F

-- unit set

oneV-refl-lm :  (I : Set) -> (F : I -> Set) 
    -> (x : N₁) ->  (br-singV zeroV x)  ≐ (emb I F (br-sing-sV I F (zero-sV I F) x))
oneV-refl-lm  I F 0₁ = easy-eqV N₀ _ _ (λ x → exfalso _ x)

oneV-reflection :  (I : Set) -> (F : I -> Set) 
              -> oneV ∈ uV I F
oneV-reflection I F = (succ-sV I F (zero-sV I F) , 
                  (pair (λ x → x , oneV-refl-lm I F x)
                        (λ y → y , oneV-refl-lm I F y)))




-- binary disjoint union


bV-sumV : (a b : V) -> (# a + #  b) -> V
bV-sumV a b (inl x) = < zeroV ,  a ‣ x >
bV-sumV a b (inr y) = < oneV , b ‣ y >
 
-- make disjoint by pairing with zeroV and oneV

sumV : (a b : V) -> V
sumV a b = sup (# a + # b) (bV-sumV a b)


inl-ext :  (a b : V) -> (x y : # a) 
         ->  a ‣ x ≐  a ‣ y
         ->  (sumV a b) ‣ inl x ≐  (sumV a b) ‣ inl y 
inl-ext a b x y p = pairV-ext (refV _) p

inl-ext-gen :  (a b  a' b' : V) -> (x : # a) -> (y : # a') 
         ->  a ‣ x ≐  a' ‣ y
         ->  (sumV a b) ‣ inl x ≐  (sumV a' b') ‣ inl y 
inl-ext-gen a b a' b' x y p = pairV-ext (refV _) p 

inl-inj :  (a b : V) -> (x y : # a) 
         ->  (sumV a b) ‣ inl x ≐  (sumV a b) ‣ inl y 
         ->  a ‣ x ≐  a ‣ y
inl-inj a b x y p = 
    let lm = pairV-inv-1 p
    in prj2 lm

inl-inj-gen :  (a b a' b' : V) -> (x : # a) -> (y : # a') 
         ->  (sumV a b) ‣ inl x ≐  (sumV a' b') ‣ inl y 
         ->  a ‣ x ≐  a' ‣ y
inl-inj-gen a b a' b' x y p = 
    let lm = pairV-inv-1 p
    in prj2 lm


inr-ext-gen :  (a b a' b' : V) -> (x : # b) -> (y : # b') 
         ->  b ‣ x ≐  b' ‣ y
         ->  (sumV a b) ‣ inr x ≐  (sumV a' b') ‣ inr y 
inr-ext-gen a b a' b' x y p = pairV-ext (refV _) p

inr-inj :  (a b : V) -> (x y : # b) 
         ->  (sumV a b) ‣ inr x ≐  (sumV a b) ‣ inr y 
         ->  b ‣ x ≐  b ‣ y
inr-inj a b x y p = 
    let lm = pairV-inv-1 p
    in prj2 lm

inr-inj-gen :  (a b a' b' : V) -> (x : # b) -> (y : # b') 
         ->  (sumV a b) ‣ inr x ≐  (sumV a' b') ‣ inr y 
         ->  b ‣ x ≐  b' ‣ y
inr-inj-gen a b a' b' x y p = 
    let lm = pairV-inv-1 p
    in prj2 lm


-- pairV-inv-1 : {x y z u : V} -> < x , y > ≐ < z , u > ->  and (x ≐ z) (y ≐ u)

-- Peano4 : (x : V)
--    -> succV x ≐ zeroV -> N₀


inl-inr-dis :  (a b a' b' : V) -> (x : # a) -> (y : # b') 
         -> not ((sumV a b) ‣ inl x ≐  (sumV a' b') ‣ inr y)
inl-inr-dis a b a' b' x y p = 
   let lm = prj1 (pairV-inv-1 p)
   in Peano4 zeroV (symV lm) 


inr-inl-dis :  (a b a' b' : V) -> (x : # a') -> (y : # b) 
         -> not ((sumV a b) ‣ inr y ≐  (sumV a' b') ‣ inl x)
inr-inl-dis a b a' b' x y p = 
  let lm = prj1 (pairV-inv-1 p)
  in Peano4 zeroV lm


sumV-ext-half1  : (a b a' b' : V) -> a ≐ a' -> b ≐ b' -> sumV a b ≤ sumV a' b'
sumV-ext-half1 a b a' b' p q (inl x) = 
  let lm2 : a ‣ x ≐ a' ‣ (e+ p x)
      lm2 = e+prop p x
      lm : sumV a b ‣ inl x ≐ sumV a' b' ‣ inl (e+ p x)
      lm = inl-ext-gen a b a' b' _ _ lm2
  in (inl (e+ p x)) , lm
 
sumV-ext-half1 a b a' b' p q (inr y) = 
  let lm2 : b ‣ y ≐ b' ‣ (e+ q y)
      lm2 = e+prop q y
      lm : sumV a b ‣ inr y ≐ sumV a' b' ‣ inr (e+ q y)
      lm = inr-ext-gen a b a' b' _ _ lm2
  in (inr (e+ q y)) , lm

-- move  ..

≤-to-≥ : (u v : V)  -> (u ≤ v)  -> (v ≥ u)
≤-to-≥ u v p x = (pj1 (p x)) , (symV (pj2 (p x)))

sumV-ext-half2  : (a b a' b' : V) -> a ≐ a' -> b ≐ b' -> sumV a b ≥ sumV a' b'
sumV-ext-half2 a b a' b' p q = ≤-to-≥ (sumV a' b') (sumV a b) (sumV-ext-half1 a' b' a b (symV p) (symV q)) 
  
sumV-ext : (a b a' b' : V) -> a ≐ a' -> b ≐ b' -> sumV a b ≐ sumV a' b'
sumV-ext a b a' b' p q = pair (sumV-ext-half1 a b a' b' p q) (sumV-ext-half2 a b a' b' p q)



-- zero-sV : sV
-- zero-sV = ssup n₀ br-zero-sV

one-sV :  (I : Set) -> (F : I -> Set) 
           -> sV I F
one-sV I F = succ-sV I F (zero-sV I F)

emb0 : (I : Set) -> (F : I -> Set) 
       -> emb I F (zero-sV I F) ≐ zeroV
emb0 I F = emb-zero I F

emb1 :  (I : Set) -> (F : I -> Set) 
       -> emb I F (one-sV I F) ≐ oneV
emb1 I F =  traV (emb-succ I F (zero-sV I F)) (succV-ext _ _ (emb0 I F))




bsV-sum-sV : (I : Set) -> (F : I -> Set) 
           -> (a b : sV I F) -> To {I} {F} ((isV I F a) ⊕ (isV I F b)) -> sV I F
bsV-sum-sV I F a b (inl x) = pair-sV I F (zero-sV I F) (bsV I F a x)
bsV-sum-sV I F a b (inr y) = pair-sV I F (one-sV I F) (bsV I F b y)


-- bV-sumV : (a b : V) -> (# a + #  b) -> V
-- bV-sumV a b (inl x) = < zeroV ,  a ‣ x >
-- bV-sumV a b (inr y) = < oneV , b ‣ y >

sum-sV : (I : Set) -> (F : I -> Set) 
           -> (a b : sV I F) -> sV I F
sum-sV I F a b = sup ((isV I F a) ⊕ (isV I F b)) (bsV-sum-sV I F a b)





emb-sum-lm1 :  (I : Set) -> (F : I -> Set) 
           -> (a b : sV I F) -> To {I} {F} (isV I F a) + To {I} {F} (isV I F b) -> # (emb I F a) + # (emb I F b)
emb-sum-lm1 I F a b (inl x) = inl (emb+ I F a x)
emb-sum-lm1 I F a b (inr y) = inr (emb+ I F b y)

emb-sum-lm1-eq :  (I : Set) -> (F : I -> Set) 
           -> (a b : sV I F) -> (x : To {I} {F} (isV I F a) + To {I} {F} (isV I F b)) ->
             (emb I F (bsV-sum-sV I F a b x)) ≐  (bV-sumV (emb I F a) (emb I F b) (emb-sum-lm1 I F a b x))
emb-sum-lm1-eq I F a b (inl x) = traV (emb-pair I F _ _) (pairV-ext (emb0 I F) (emb-bsV I F a x)) -- emb-bsV a x
emb-sum-lm1-eq I F a b (inr y) = traV (emb-pair I F _ _) (pairV-ext (emb1 I F) (emb-bsV I F b y))  -- emb-bsV b y

-- emb-pair : (u v : sV) -> emb (pair-sV u v) ≐ pairV (emb u) (emb v)




emb-sum-lm2 :   (I : Set) -> (F : I -> Set) 
           -> (a b : sV I F)  -> # (emb I F a) + # (emb I F b) -> To {I} {F} (isV I F a) + To {I} {F}(isV I F b)
emb-sum-lm2 I F a b (inl x) = inl (emb- I F a x)
emb-sum-lm2 I F a b (inr y) = inr (emb- I F b y)

emb-sum-lm2-eq :   (I : Set) -> (F : I -> Set) 
           -> (a b : sV I F) -> (y : # (emb I F a) + # (emb I F b)) ->
    (emb I F (bsV-sum-sV I F a b (emb-sum-lm2 I F a b y))) ≐ (bV-sumV (emb I F a) (emb I F b) y)
emb-sum-lm2-eq I F a b (inl x) = 
        traV (emb-pair I F _ _) 
             (pairV-ext (emb0 I F) (traV (emb-bsV I F a (emb- I F a x)) (symV (>< (emb+- I F a x)))))
emb-sum-lm2-eq I F a b (inr y) =
        traV (emb-pair I F _ _) 
             (pairV-ext (emb1 I F) (traV (emb-bsV I F b (emb- I F b y)) (symV (>< (emb+- I F b y)))))



emb-sum :  (I : Set) -> (F : I -> Set) 
           -> (a b : sV I F) ->
     emb I F (sum-sV I F a b) ≐ sumV (emb I F a) (emb I F b)
emb-sum I F a b = pair (λ x → (emb-sum-lm1 I F a b x) , emb-sum-lm1-eq I F a b x) 
                       (λ y → (emb-sum-lm2 I F a b y) , emb-sum-lm2-eq I F a b y)




sum-map : {A B C D : Set} -> (f : A -> C) -> (g : B -> D) -> (A + B -> C + D)
sum-map {A} {B} {C} {D} f g (inl x) = inl (f x)
sum-map {A} {B} {C} {D} f g (inr y) = inr (g y)



sumV-refl-lm1 :  (I : Set) -> (F : I -> Set) 
              -> (a  b : V) 
              -> (p : a ∈ uV I F) -> (q : b ∈ uV I F)
              -> (u : # (emb I F (pj1 p)) + # (emb I F (pj1 q)))
              -> (bV-sumV (emb I F (pj1 p)) (emb I F (pj1 q)) u) ≐
                 (bV-sumV a b (sum-map (e+ (symV (pj2 p))) (e+ (symV (pj2 q))) u)) 
sumV-refl-lm1 I F a b p q (inl x) = pairV-ext (refV _) (e+prop (symV (pj2 p)) x) 
sumV-refl-lm1 I F a b p q (inr y) = pairV-ext (refV _) (e+prop (symV (pj2 q)) y) 



sumV-refl-lm2 :  (I : Set) -> (F : I -> Set) 
              -> (a  b : V) 
              -> (p : a ∈ uV I F) -> (q : b ∈ uV I F)
              -> (v : # a + # b)
              ->  (bV-sumV (emb I F (pj1 p)) (emb I F (pj1 q))
                           (sum-map (e+ (pj2 p)) (e+ (pj2 q)) v))
                  ≐  (bV-sumV a b v)
sumV-refl-lm2 I F a b p q (inl x) = pairV-ext (refV _) (symV (e+prop (pj2 p) x)) 
sumV-refl-lm2 I F a b p q (inr y) = pairV-ext (refV _) (symV (e+prop (pj2 q) y)) 



sumV-reflection :  (I : Set) -> (F : I -> Set) 
              -> (a  b : V) 
              -> (a ∈ uV I F) -> (b ∈ uV I F)
              -> sumV a b ∈ uV I F
sumV-reflection I F a b p q = 
  let p2 : a ≐ (uV I F) ‣ pj1 p
      p2 = pj2 p
      q2 : b ≐ (uV I F) ‣ pj1 q
      q2 = pj2 q
  in        (sum-sV I F (pj1 p) (pj1 q)) , 
            symV (traV (emb-sum I F (pj1 p) (pj1 q)) 
             (pair (λ u → (sum-map (e+ (symV p2)) (e+ (symV q2)) u) , sumV-refl-lm1 I F a b p q u) 
                   (λ v → (sum-map (e+ p2) (e+ q2) v) , sumV-refl-lm2 I F a b p q v)))
   
