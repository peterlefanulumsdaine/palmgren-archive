
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- {-# OPTIONS --no-eta-equality #-}

-- Agda version 2.5.2


module iterative-sets-pt2 where

open import basic-types
open import basic-setoids
open import dependent-setoids
open import subsetoids
open import iterative-sets

-- Sigma-set in V

sigmaV : (a : V) -> (g :  setoidmap1 (κ a) VV) -> V
sigmaV a g =  sup (Σ (# a) (\y -> # (g • y))) 
                     (\u -> < a ‣ (pj1 u) , (g • (pj1 u)) ‣ (pj2 u) >)

-- First and second projections

pj1-sigmaV-op : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
            ||  κ (sigmaV a g) || -> V
pj1-sigmaV-op a g u = a ‣ (pj1 u)

pj1-sigmaV-ext : (a : V) -> (g :  setoidmap1 (κ a) VV) 
        -> (u v : ||  κ (sigmaV a g) ||)   
        -> < κ (sigmaV a g) > u ~ v
        -> pj1-sigmaV-op a g u ≐ pj1-sigmaV-op a g v
pj1-sigmaV-ext a g u v p = prj1 (pairV-inv-1 (>< p))



pj1-sigmaV : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
            setoidmap1 (κ (sigmaV a g)) VV
pj1-sigmaV a g = record { op = pj1-sigmaV-op a g 
                        ; ext = λ x y p →  <<>> ( pj1-sigmaV-ext a g x y p) 
                        }




pj1-sigmaV-prop : (a : V) -> (g :  setoidmap1 (κ a) VV)  
            -> (u :  || κ (sigmaV a g) ||)
            -> pj1-sigmaV a g • u ∈ a 
pj1-sigmaV-prop a g u = (pj1 u) , (refV _)

pj2-sigmaV-op : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
            ||  κ (sigmaV a g) || -> V
pj2-sigmaV-op a g u = (g • (pj1 u)) ‣ (pj2 u)

pj2-sigmaV-ext : (a : V) -> (g :  setoidmap1 (κ a) VV) 
        -> (u v : ||  κ (sigmaV a g) ||)   
        -> < κ (sigmaV a g) > u ~ v
        -> pj2-sigmaV-op a g u ≐ pj2-sigmaV-op a g v
pj2-sigmaV-ext a g u v p = prj2 (pairV-inv-1 (>< p))


pj2-sigmaV : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
            setoidmap1 (κ (sigmaV a g)) VV
pj2-sigmaV a g = record { op = pj2-sigmaV-op a g 
                        ; ext = λ x y p → <<>> (pj2-sigmaV-ext a g x y p) 
                        }

pj2-sigmaV-prop : (a : V) -> (g :  setoidmap1 (κ a) VV)  
            -> (u :  || κ (sigmaV a g) ||)
            -> pj2-sigmaV a g • u ∈ g •  (pj1 u)
pj2-sigmaV-prop a g u = (pj2 u) , (refV _)



-- Characterization of equality

sigmaV-eq-lm1 :  (a : V) 
           ->  (g :  setoidmap1 (κ a) VV) 
           ->  (z z' : || κ (sigmaV a g) ||)
           ->  (< κ (sigmaV a g) >  z ~ z')
           ->  and (a ‣ (pj1 z)  ≐  a ‣ (pj1 z')) 
                   ((g • (pj1 z)) ‣ (pj2 z)  ≐  (g • (pj1 z')) ‣ (pj2 z'))
sigmaV-eq-lm1 a g z z' p = pairV-inv-1 (>< p) 

sigmaV-eq-lm2 :  (a : V) 
           ->  (g :  setoidmap1 (κ a) VV) 
           ->  (z z' : || κ (sigmaV a g) ||)
           ->  (a ‣ (pj1 z)  ≐  a ‣ (pj1 z')) 
           ->  ((g • (pj1 z)) ‣ (pj2 z)  ≐  (g • (pj1 z')) ‣ (pj2 z'))
           ->  (< κ (sigmaV a g) >  z ~ z')
sigmaV-eq-lm2 a g z z' p q = <> (pairV-ext p q) 




sigmaV-lm : (a : V) -> (g :  setoidmap1 (κ a) VV)
      -> (x y : V) -> (< x , y > ∈ sigmaV a g) -> 
          Σ (x ∈ a)  (\p -> (y ∈ (g • (pj1 p))))
sigmaV-lm a g x y p = 
    let  
        lm : Σ (# (sigmaV a g)) (\z ->  < x , y > ≐ (sigmaV a g) ‣ z)
        lm = p 
        lm1 : Σ (# a) (λ z → # (ap1 g z))
        lm1 = pj1 p
        lm2 : < x , y > ≐ < (a ‣ (pj1 lm1)) , ((g • (pj1 lm1)) ‣ (pj2 lm1)) >

        lm2 = pj2 p
        lm2a : x ≐ (bV a (pj1 lm1))
        lm2a = prj1 (pairV-inv-1 lm2)
        lm2b : y ≐ (bV (g • (pj1 lm1)) (pj2 lm1))
        lm2b = prj2 (pairV-inv-1 lm2)
     
        lm3 : x ∈ a
        lm3 = (pj1 lm1) , lm2a
        lm4 :  y ∈ g • (pj1 (pj1 p))
        lm4 = _ , lm2b
    in lm3 , lm4




sigmaV-pair-lm : (a : V) -> (g :  setoidmap1 (κ a) VV)
      -> (u : V) -> (u ∈ sigmaV a g) -> is-pairV1 u
sigmaV-pair-lm a g u p = let q = memV-expand u (sigmaV a g) p
                             q1 = pj1 q
                             q2 = pj2 q
                         in record { cp1 =  a ‣ (pj1 (pj1 p)) 
                                   ; cp2 = (g • (pj1 (pj1 p))) ‣ (pj2 (pj1 p)) 
                                   ; eqp = q2 } 


sigmaV-lm-rev : (a : V) -> (g :  setoidmap1 (κ a) VV)
      -> (x y : V) -> (p : x ∈ a) -> (y ∈ (g • (pj1 p))) 
      -> (< x , y > ∈ sigmaV a g)
sigmaV-lm-rev a g x y p q = 
  let p1 : Σ (# a) (\z -> x ≐ (a ‣ z))
      p1 = p
      p2 : Σ (# (g • (pj1 p))) (\z -> y ≐ (g • (pj1 p)) ‣ z)
      p2 = q
      lm3 : < x , y > ≐ ((sigmaV a g) ‣ (pj1 p , pj1 q))
      lm3 = pairV-ext (pj2 p) (pj2 q)
      main : Σ (# (sigmaV a g)) (\z -> < x , y > ≐ (sigmaV a g) ‣ z) 
      main = ((pj1 p) , (pj1 q)) , lm3
  in main





κ-sigmaV-fwd-op : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
       || κ (sigmaV a g) ||  ->  || Σ-std (κ a) (κ° g) ||  
κ-sigmaV-fwd-op a g u = u 

κ-sigmaV-fwd-ext : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
       (x y :  || κ (sigmaV a g) ||) -> (< κ (sigmaV a g) > x ~ y)
       -> < Σ-std (κ a) (κ° g) >
             κ-sigmaV-fwd-op a g x ~ κ-sigmaV-fwd-op a g y
κ-sigmaV-fwd-ext a g (x1 , x2) (y1 , y2) p = 
     let eqp : and (a ‣ x1 ≐ a ‣ y1) ((g • x1) ‣ x2 ≐ (g • y1) ‣ y2)
         eqp = sigmaV-eq-lm1 a g (x1 , x2) (y1 , y2)  p

         pr1 : a ‣ x1 ≐ a ‣ y1
         pr1 = prj1 eqp
         pr2 : (g • x1) ‣ x2 ≐ (g • y1) ‣ y2
         pr2 = prj2 eqp
         lm1 : < κ a > x1 ~ y1
         lm1 = <> pr1

         lm2b : (g • x1) ‣ x2 ≐ (g • y1) ‣ (ap ((κ° g) ± lm1) x2)
         lm2b = κ°-trp-prop g x1 y1 lm1 x2    

         lm2a :  (g • y1) ‣ (ap ((κ° g) ± lm1) x2)  ≐ (g • y1) ‣ y2
         lm2a = traV (symV lm2b) pr2
         lm2 : < (κ° g) § y1 > (ap ((κ° g) ± lm1) x2) ~ y2
         lm2 = <> lm2a 
         main :  < Σ-std (κ a) (κ° g) > (x1 , x2) ~ (y1 , y2)
         main = <> (lm1 , lm2)
     in main



κ-sigmaV-fwd : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
       || κ (sigmaV a g)  =>  Σ-std (κ a) (κ° g) ||
κ-sigmaV-fwd a g = record { op = κ-sigmaV-fwd-op a g 
                          ; ext = κ-sigmaV-fwd-ext a g
                          }




κ-sigmaV-rev-op : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
       || Σ-std (κ a) (κ° g) || -> || κ (sigmaV a g)  ||
κ-sigmaV-rev-op a g u = u

κ-sigmaV-rev-ext :  (a : V) 
        -> (g :  setoidmap1 (κ a) VV) 
        -> (x y : || Σ-std (κ a) (κ° g) ||)
        -> < Σ-std (κ a) (κ° g) > x ~ y 
        -> < κ (sigmaV a g) > κ-sigmaV-rev-op a g x ~ κ-sigmaV-rev-op a g y
κ-sigmaV-rev-ext a g (x1 , x2) (y1 , y2) p =
     let lm0 : < κ a > x1 ~ y1
         lm0 = pj1 (>< p)
         lm1 :  a ‣ x1 ≐ a ‣ y1
         lm1 = >< (pj1 (>< p)) 


         lm2a : (g • y1) ‣ (ap (κ° g ± lm0) x2) ≐ (g • y1) ‣ y2
         lm2a = >< (pj2 (>< p))  
         lm2b : (g • x1) ‣ x2 ≐ (g • y1) ‣ (ap (κ° g ± lm0) x2)
         lm2b =  κ°-trp-prop g x1 y1 lm0 x2   
         lm2 : (g • x1) ‣ x2 ≐ (g • y1) ‣ y2
         lm2 = traV lm2b lm2a 
     in sigmaV-eq-lm2 a g  (x1 , x2) (y1 , y2) lm1 lm2
 


κ-sigmaV-rev : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
       || Σ-std (κ a) (κ° g) => κ (sigmaV a g)  ||
κ-sigmaV-rev a g = record { op = κ-sigmaV-rev-op a g 
                          ; ext = κ-sigmaV-rev-ext a g
                          }





-- Sigma in V is isomorphic to the external Sigma for setoids

κ-sigmaV-iso : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
       κ (sigmaV a g)  ≅  Σ-std (κ a) (κ° g)
κ-sigmaV-iso a g  = (κ-sigmaV-fwd a g) , 
                            ((κ-sigmaV-rev a g) , 
                                  pair (λ x → refl (κ (sigmaV a g)) x) 
                                       (λ y → refl (Σ-std (κ a) (κ° g)) y))




-- Pi in V


piV-iV : (a : V) -> (g :  setoidmap1 (κ a) VV) -> Set
piV-iV a g = Σ ((x : # a) ->  # (g • x))
                 (\f -> (x y : # a) ->
                        (p : < κ a > x ~ y) -> < (κ° g)  § y > (ap (κ° g ± p) (f x))  ~ f y)

piV-bV : (a : V) -> (g :  setoidmap1 (κ a) VV) ->  piV-iV a g -> V
piV-bV a g h =  sup (# a) (\x ->  < a ‣ x , (g • x) ‣ ((pj1 h) x) >)

piV : (a : V) -> (g :  setoidmap1 (κ a) VV) -> V
piV a g = sup (piV-iV a g) (piV-bV a g)




κ-piV-fwd-op : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
       || κ (piV a g) ||  ->  || Π-std (κ a) (κ° g) ||  
κ-piV-fwd-op a g h = (λ x →  (pj1 h) x) , (λ x y p → pj2 h x y p)



κ-piV-fwd-ext : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
       (f h :  || κ (piV a g) ||) -> (< κ (piV a g) > f ~ h)
       -> < Π-std (κ a) (κ° g) >
             κ-piV-fwd-op a g f ~ κ-piV-fwd-op a g h
κ-piV-fwd-ext a g f h p = 
    <> (\ x ->
    let f1 : (x : # a) → # (g • x)
        f1 = pj1 f
        h1 : (x : # a) → # (g • x)
        h1 = pj1 h
        eq :  piV-bV a g f ≐ piV-bV a g h
        eq = >< p
        eqx1 :  ((x : # a) -> Σ (# a) (\y ->  < a ‣ x , (g • x) ‣ ((pj1 f) x) > ≐  < a ‣ y , (g • y) ‣ ((pj1 h) y) >)) 
        eqx1 = prj1 (eqV-expand _ _ (>< p)) 
        eqx2 :  ((y : # a) -> Σ (# a) (\x ->  < a ‣ x , (g • x) ‣ ((pj1 f) x) > ≐  < a ‣ y , (g • y) ‣ ((pj1 h) y) >)) 
        eqx2 = prj2 (eqV-expand _ _ (>< p))
        z = pj1 (eqx1 x)
        eqx1a : < a ‣ x , (g • x) ‣ ((pj1 f) x) > ≐  < a ‣ z , (g • z) ‣ ((pj1 h) z) >
        eqx1a = pj2 (eqx1 x)
        v = pj1 (eqx2 x)
        eqx2a : < a ‣ v , (g • v) ‣ ((pj1 f) v) > ≐  < a ‣ x , (g • x) ‣ ((pj1 h) x) >
        eqx2a = pj2 (eqx2 x)
        eq3 :  a ‣ v  ≐  a ‣ x
        eq3 = prj1 (pairV-inv-1 eqx2a)
        exf :  < κ° g § x > ap (κ° g ±  (<> eq3)) (pj1 f v) ~ pj1 f x
        exf = pj2 f v x (<> eq3)
        exf' :   (g • x) ‣ (ap (κ° g ± (<> eq3)) (pj1 f v)) ≐  (g • x) ‣ ((pj1 f) x)
        exf' = >< exf
        eq4a :  (g • v) ‣ ((pj1 f) v) ≐  (g • x) ‣ (ap (κ° g ± (<> eq3)) (pj1 f v))
        eq4a = κ°-trp-prop g _ _ (<> eq3) _
        eq4 :  (g • v) ‣ ((pj1 f) v) ≐  (g • x) ‣ ((pj1 f) x) 
        eq4 = traV eq4a exf'
        eq5 : < a ‣ v , (g • v) ‣ ((pj1 f) v) > ≐ < a ‣ x , (g • x) ‣ ((pj1 f) x) >
        eq5 = pairV-ext eq3 eq4
        lm :  (g • x) ‣ (pj1 f x)  ≐ (g • x) ‣ (pj1 h x)
        lm = prj2 (pairV-inv-1 (traV (symV eq5) eqx2a))
        main :  < κ° g § x > pj1 f x ~ pj1 h x
        main = <> lm
    in main)

κ-piV-fwd : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
       || κ (piV a g)  =>  Π-std (κ a) (κ° g) ||
κ-piV-fwd a g = record { op = κ-piV-fwd-op a g
                       ; ext = κ-piV-fwd-ext a g }







κ-piV-rev-op : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
       || Π-std (κ a) (κ° g) || -> || κ (piV a g)  ||
κ-piV-rev-op a g k = (pj1 k) , (pj2 k)




κ-piV-rev-ext :  (a : V) 
        -> (g :  setoidmap1 (κ a) VV) 
        -> (f h : || Π-std (κ a) (κ° g) ||)
        -> < Π-std (κ a) (κ° g) > f ~ h 
        -> < κ (piV a g) > κ-piV-rev-op a g f ~ κ-piV-rev-op a g h
κ-piV-rev-ext a g (f1 , f2) (h1 , h2) p = 
      <> (
      let 
          lm0 = >< p
          lm :  (x : || (κ a) ||) ->  (g • x) ‣ f1 x  ≐  (g • x) ‣ h1 x
          lm = λ x → >< (lm0 x) -- >< p
          main :  sup (# a) (\x ->  < a ‣ x , (g • x) ‣ (f1 x) >)   
                  ≐  sup (# a) (\x ->  < a ‣ x , (g • x) ‣ (h1 x) >)    
          main = pair (λ x → x , (pairV-ext (refV _) (lm x))) 
                      (λ y → y , pairV-ext (refV _) (lm y) )
      in main)




κ-piV-rev : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
       || Π-std (κ a) (κ° g) => κ (piV a g)  ||
κ-piV-rev a g = record { op = κ-piV-rev-op a g
                       ; ext = κ-piV-rev-ext a g }

-- Pi in V is isomorphic to external Pi for corresponding setoids

κ-piV-iso : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
       κ (piV a g)  ≅  Π-std (κ a) (κ° g)
κ-piV-iso a g  = (κ-piV-fwd a g) , ((κ-piV-rev a g) ,
                     (pair (λ h → <> (refV _)) 
                           (λ h  → <> (λ x → refl (κ° g § x ) (pj1 h x))) 
                          ))

