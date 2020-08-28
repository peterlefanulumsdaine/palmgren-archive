-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt3 where

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
--

-- towards application operation and Pi-elimination

app-op :  {Γ : ctx} 
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (Γ ==> c :: Π-f A B)
    -> (a : raw Γ)
    -> (Γ ==> a :: A)
    -> (|| κ Γ ||)
    -> V
app-op A B c p a q u =  (apt B (u , pj1 (apel q u))) ‣ (pj1 (pj1 (apel p u)) (pj1 (apel q u)))


app-ext :  {Γ : ctx} 
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f A B)
    -> (a : raw Γ)
    -> (q : Γ ==> a :: A)
    -> (x y : || κ Γ ||)
    -> < κ Γ > x ~ y 
    -> << VV >> app-op A B c p a q x ~ app-op A B c p a q y
app-ext {Γ} A B c p a q x y r = 

   let eqC :  (apt (Π-f A B) x) ≐ (apt (Π-f A B) y)
       eqC = >><< (extensionality1 (ty.type (Π-f A B)) x y r)
       ec : << VV >> (apr c x) ~ (apr c y)
       ec = extensionality1 (raw.rawterm c) x y r
       eqA : (apt A x) ≐ (apt A y) 
       eqA = >><< (extensionality1 (ty.type A) x y r)
       ea  : << VV >> (apr a x) ~ (apr a y)
       ea = extensionality1 (raw.rawterm a) x y r

       px2  : (apr c x) ≐ (apt (Π-f A B) x) ‣ pj1 (apel p x)
       px2 = pj2 (apel p x)
       px11 : (x₁ : # (apt A x)) →
                # (apt B (x , x₁))    
       px11 = pj1 (pj1 (apel p x))

       px12 : (x₁ y₁ : # (apt A x)) ->
             (p₁ : < κ (apt A x) > x₁ ~ y₁) →
              < κ  (apt B (x , y₁)) >
                    (ap (κ-Fam ±± (extensionality1 (Fxx (ap1 (mk-Par A B) x)) x₁ y₁ p₁)) (pj1 (pj1 (apel p x)) x₁)) 
                     ~
                    (pj1 (pj1 (apel p x)) y₁)
       px12 = pj2 (pj1 (apel p x))

       py2  : (apr c  y) ≐ (apt (Π-f A B) y) ‣ pj1 (apel p y)
       py2 = pj2 (apel p y)

       py11 : (x₁ : # (apt A y)) →
                # (apt B (y , x₁))
       py11 = pj1 (pj1 (apel p y))
       py12 : (x₁ y₁ :  # (apt A y)) ->
             (p₁ : < κ (apt A y) > x₁ ~ y₁) →
               < κ (apt B (y , y₁)) >
                 (ap (κ-Fam ±± (extensionality1 (Fxx (ap1 (mk-Par A B) y)) x₁ y₁ p₁)) (pj1 (pj1 (apel p y)) x₁))
                  ~
                 pj1 (pj1 (apel p y)) y₁  
       py12 = pj2 (pj1 (apel p y))
    

       qx2  : (apr a x) ≐ (apt A x) ‣ pj1 (apel q x)
       qx2 = pj2 (apel q x)

       qy2  : (apr a y) ≐ (apt A y) ‣ pj1 (apel q y)
       qy2 = pj2 (apel q y)

       qxy2 : (apt A x) ‣ pj1 (apel q x) ≐ (apt A y) ‣ pj1 (apel q y)
       qxy2 = traV (symV qx2) (traV (>><< ea) qy2)

      
       eqc :  (apt (Π-f A B) x) ‣ pj1 (apel p x) ≐  (apt (Π-f A B) y) ‣ pj1 (apel p y)  -- main c equality
       eqc = traV (symV px2) (traV (>><< ec) py2)
     
       lmC :  (apt (Π-f A B) x) ‣ pj1 (apel p x) ≐ (apt (Π-f A B) y) ‣ (e+ eqC (pj1 (apel p x)))
       lmC = e+prop eqC (pj1 (apel p x)) 
       
       pe : (apt (Π-f  A B) y) ‣ (e+ eqC (pj1 (apel p x))) ≐  (apt (Π-f A B) y) ‣ pj1 (apel p y)
       pe = traV (symV lmC) eqc

       eqa : (apt A x) ‣ pj1 (apel q x) ≐ (apt A  y) ‣ pj1 (apel q y)  -- main a equality
       eqa = traV (symV qx2) (traV (>><< ea) qy2)

       lmA :  (apt A  x) ‣ pj1 (apel q x) ≐ (apt A y) ‣ (e+ eqA (pj1 (apel q x)))
       lmA = e+prop eqA (pj1 (apel q x)) 

       p₁ : < κ (apt A y) >  (e+ eqA (pj1 (apel q x))) ~ (pj1 (apel q y))
       p₁ = <> (traV (symV lmA) eqa)
       py12b : < κ (apt B (y , pj1 (apel q y))) >
              ap (κ-Fam ±±  extensionality1 (Fxx (ap1 (mk-Par A B) y)) (e+ eqA (pj1 (apel q x))) (pj1 (apel q y)) p₁)
                            (pj1 (pj1 (apel p y)) (e+ eqA (pj1 (apel q x))))
              ~ pj1 (pj1 (apel p y)) (pj1 (apel q y))
       py12b = py12 (e+ eqA (pj1 (apel q x))) (pj1 (apel q y)) p₁ 

       exp4a  : 
         Σ (# (apt A  y))
         (λ y₁ →
            < (apt A  x) ‣ (pj1 (apel q x)) , (apt B  (x , (pj1 (apel q x)))) ‣ pj1 (pj1 (apel p x)) (pj1 (apel q x)) > ≐
            < (apt A y) ‣ y₁ , (apt B  (y , y₁)) ‣ pj1 (pj1 (apel p y)) y₁ >)
       exp4a = prj1 (Π-f-exp4  A B x y  (pj1 (apel p x)) (pj1 (apel p y)) eqc) (pj1 (apel q x))
  
       exp4b  :
          Σ (# (apt A x))
         (λ x₁ →
            < (apt A  x) ‣ x₁ , (apt B  (x , x₁)) ‣ pj1 (pj1 (apel p x)) x₁ > ≐
            < (apt A y) ‣ (pj1 (apel q y)) , (apt B  (y , (pj1 (apel q y)))) ‣ pj1 (pj1 (apel p y)) (pj1 (apel q y)) >)
       exp4b = prj2 (Π-f-exp4 A B x y  (pj1 (apel p x)) (pj1 (apel p y)) eqc)  (pj1 (apel q y))
       y1 : # (apt A  y)
       y1 = pj1 exp4a
       exp4a2 :  < (apt A x) ‣ (pj1 (apel q x)) , (apt B (x , (pj1 (apel q x)))) ‣ pj1 (pj1 (apel p x)) (pj1 (apel q x)) > ≐
                 < (apt A y) ‣ y1 , (apt B (y , y1)) ‣ pj1 (pj1 (apel p y)) y1 >
       exp4a2 = pj2 exp4a
       exp4a21 : (apt A x) ‣ (pj1 (apel q x)) ≐ (apt A  y) ‣ y1
       exp4a21 = prj1 (pairV-inv-1 exp4a2)
       exp4a22 :  (apt B (x , (pj1 (apel q x)))) ‣ pj1 (pj1 (apel p x)) (pj1 (apel q x)) ≐ (apt B (y , y1)) ‣ pj1 (pj1 (apel p y)) y1
       exp4a22 =  prj2 (pairV-inv-1 exp4a2)

       try :  (apt A y) ‣ y1 ≐ (apt A y) ‣ (pj1 (apel q y))
       try = traV (symV exp4a21) qxy2
       try2 : < κ (Γ ▷ A) > (y , y1) ~ (y , pj1 (apel q y))
       try2 =  <> (pairV-ext (refV _) try)
       try3 : (apt B (y , y1)) ≐  (apt B  (y , pj1 (apel q y))) 
       try3 = >><< (extensionality1 (ty.type B) (y , y1) (y , pj1 (apel q y)) try2)
       try4 : (apt A y) ‣ y1 ≐ (apt A y) ‣ (e+ eqA (pj1 (apel q x)))
       try4 = traV (symV exp4a21)  lmA
       
       pty12q' = py12 (e+ eqA (pj1 (apel q x)))  y1 (<> (symV try4))

       pty12q : (apt B (y , y1)) ‣ (ap (κ-Fam ±± (extensionality1 (Fxx (ap1 (mk-Par A B) y))
                                                        (e+ eqA (pj1 (apel q x))) 
                                                        y1 
                                                        (<> (symV try4)))) 
                                     (pj1 (pj1 (apel p y)) (e+ eqA (pj1 (apel q x)))))
                   ≐
                (apt B (y , y1)) ‣ (pj1 (pj1 (apel p y)) y1)
       pty12q = >< pty12q' -- py12 (e+ eqA (pj1 (apel q x)))  y1 (symV try4)

{--

--}

       pty12r : (apt B (y ,  pj1 (apel q y))) ‣ (e+ try3  (ap (κ-Fam ±± (extensionality1 (Fxx (ap1 (mk-Par A B) y)) 
                                      (e+ eqA (pj1 (apel q x))) y1 (<> (symV try4)))) (pj1 (pj1 (apel p y)) (e+ eqA (pj1 (apel q x))))))
                   ≐
                (apt B (y ,  pj1 (apel q y))) ‣ (e+ try3 (pj1 (pj1 (apel p y)) y1))
       pty12r = e+ext try3 _ _ pty12q


       llm4 :  (apt B (y ,  pj1 (apel q y))) ‣ (e+ try3  (ap (κ-Fam ±± (extensionality1 (Fxx (ap1 (mk-Par A B) y)) 
                                                        (e+ eqA (pj1 (apel q x))) y1 (<> (symV try4)))) 
                                         (pj1 (pj1 (apel p y)) (e+ eqA (pj1 (apel q x))))
                                             ))                
                  ≐ 
               (apt B (y , pj1 (apel q y))) ‣ (e+ (>><< (extensionality1 (Fxx (ap1 (mk-Par A B) y)) (e+ eqA (pj1 (apel q x))) (pj1 (apel q y)) p₁))
                                         (pj1 (pj1 (apel p y)) (e+ eqA (pj1 (apel q x))))
                                             )
       llm4 = e+fun _ try3 (>><< (extensionality1 (Fxx (ap1 (mk-Par A B) y)) (e+ eqA (pj1 (apel q x))) (pj1 (apel q y)) p₁)) (pj1 (pj1 (apel p y)) (e+ eqA (pj1 (apel q x))))
       llm3 :   (apt B (y , pj1 (apel q y))) ‣ (e+ try3  (pj1 (pj1 (apel p y)) y1))
                 ≐ 
                (apt B (y , pj1 (apel q y))) ‣ (e+ (>><< (extensionality1 (Fxx (ap1 (mk-Par A B) y)) (e+ eqA (pj1 (apel q x))) (pj1 (apel q y)) p₁))
                                              (pj1 (pj1 (apel p y)) (e+ eqA (pj1 (apel q x)))))
       llm3 = traV (symV pty12r) llm4


       llm2' :  (apt B (y , y1)) ‣ pj1 (pj1 (apel p y)) y1 ≐ 
                (apt B (y , pj1 (apel q y))) ‣ (e+ (>><< (extensionality1 (Fxx (ap1 (mk-Par A B) y)) (e+ eqA (pj1 (apel q x))) (pj1 (apel q y)) p₁))
                                             (pj1 (pj1 (apel p y)) (e+ eqA (pj1 (apel q x)))))

       llm2' = traV (e+prop try3 (pj1 (pj1 (apel p y)) y1)) llm3 
      


       llm2 :  (apt B  (y , y1)) ‣ pj1 (pj1 (apel p y)) y1 ≐ 
               (apt B  (y , pj1 (apel q y))) ‣ (ap (κ-Fam ±±  extensionality1 (Fxx (ap1 (mk-Par A B) y)) (e+ eqA (pj1 (apel q x))) (pj1 (apel q y)) p₁)
                             (pj1 (pj1 (apel p y)) (e+ eqA (pj1 (apel q x)))))
       llm2 = llm2'
       llm : (apt B (x , pj1 (apel q x))) ‣ (pj1 (pj1 (apel p x)) (pj1 (apel q x))) ≐
             (apt B (y , pj1 (apel q y))) ‣ (ap (κ-Fam ±±  extensionality1 (Fxx (ap1 (mk-Par A B) y)) (e+ eqA (pj1 (apel q x))) (pj1 (apel q y)) p₁)
                            (pj1 (pj1 (apel p y)) (e+ eqA (pj1 (apel q x)))))
       llm = traV exp4a22 llm2
       main :  (apt B (x , pj1 (apel q x))) ‣ (pj1 (pj1 (apel p x)) (pj1 (apel q x))) ≐
               (apt B (y , pj1 (apel q y))) ‣ (pj1 (pj1 (apel p y)) (pj1 (apel q y)))
       main = traV llm (>< py12b)
   in <<>> main





app :  {Γ : ctx} 
    -> (A : ty Γ)  -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (Γ ==> c :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (Γ ==> a :: A)
    -> raw Γ
app A B c p a q = mkraw (record { op = app-op A B c p a q 
                                ; ext = app-ext A B c p a q })

-- app-op A B c p a q u =  (apt B (u , pj1 (apel q u))) ‣ (pj1 (pj1 (apel p u)) (pj1 (apel q u)))




app-cong1-raw :  {Γ : ctx} 
    -> (A : ty Γ)  -> (B : ty (Γ ▷ A))
    -> (c c' : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (p' : Γ ==> c' :: Π-f {Γ} A B)
    -> (Γ ==> c == c' :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (q : Γ ==> a :: A)
    -> << Raw Γ >>  app A B c p a q ~ app A B c' p' a q
app-cong1-raw {Γ} A B c c' p p' r a q = 
 <<>> (<<>> 

   (\ x -> 
   let lm3 : apr c x ≐ apt (Π-f A B) x ‣ pj1 (apel p x)
       lm3 = pj2 (apel p x)
       lm4 : apr c' x ≐ apt (Π-f A B) x ‣ pj1 (apel p' x)
       lm4 = pj2 (apel p' x)
       lm4b : apr c x ≐ apr c' x
       lm4b = prj1 r x
       lm5 : apt (Π-f A B) x ‣ pj1 (apel p x)  ≐ apt (Π-f A B) x ‣ pj1 (apel p' x)
       lm5 = traV (symV lm3) (traV lm4b lm4)
       lm6 : apr a x ≐ apt A x ‣ pj1 (apel q x)
       lm6 = pj2 (apel q x)

       lm7 =  Π-f-exp4 A B _ _ (pj1 (apel p x)) (pj1 (apel p' x)) lm5
       lm7a = prj1 lm7 (pj1 (apel q x))
       u = pj1 lm7a
       eq1 : < apt A x ‣ pj1 (apel q x) ,
          apt B (x , pj1 (apel q x)) ‣ pj1 (pj1 (apel p x)) (pj1 (apel q x))  >
          ≐ < apt A x ‣ u , apt B (x , u) ‣ pj1 (pj1 (apel p' x)) u >
       eq1 = pj2 lm7a
       lm7b = prj2 lm7 (pj1 (apel q x))
       v = pj1 lm7b
       eq2 : < apt A x ‣ v , apt B (x , v) ‣ pj1 (pj1 (apel p x)) v > ≐
          < apt A x ‣ pj1 (apel q x) ,
          apt B (x , pj1 (apel q x)) ‣ pj1 (pj1 (apel p' x)) (pj1 (apel q x))  >
       eq2 = pj2 lm7b
       

       eq :  (apt B (x , pj1 (apel q x))) ‣ (pj1 (pj1 (apel p  x)) (pj1 (apel q x))) ≐ 
             (apt B (x , pj1 (apel q x))) ‣ (pj1 (pj1 (apel p' x)) (pj1 (apel q x)))
       eq = Π-f-exp3c A B x (pj1 (apel p x)) (pj1 (apel p' x)) lm5 (pj1 (apel q x))     
   in <<>> eq 
   ))


 



app-irr1 :  {Γ : ctx} 
    -> (A : ty Γ)  -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p p' : Γ ==> c :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (q : Γ ==> a :: A)
    -> << Raw Γ >>  app A B c p a q ~ app A B c p' a q
app-irr1 {Γ} A B c p p' a q  = 
  <<>> (<<>> 
   (\ x -> 
   let lm3 : apr c x ≐ apt (Π-f A B) x ‣ pj1 (apel p x)
       lm3 = pj2 (apel p x)
       lm4 : apr c x ≐ apt (Π-f A B) x ‣ pj1 (apel p' x)
       lm4 = pj2 (apel p' x)
       lm5 : apt (Π-f A B) x ‣ pj1 (apel p x)  ≐ apt (Π-f A B) x ‣ pj1 (apel p' x)
       lm5 = traV (symV lm3) lm4
       lm6 : apr a x ≐ apt A x ‣ pj1 (apel q x)
       lm6 = pj2 (apel q x)

       lm7 =  Π-f-exp4 A B _ _ (pj1 (apel p x)) (pj1 (apel p' x)) lm5
       lm7a = prj1 lm7 (pj1 (apel q x))
       u = pj1 lm7a
       eq1 : < apt A x ‣ pj1 (apel q x) ,
          apt B (x , pj1 (apel q x)) ‣ pj1 (pj1 (apel p x)) (pj1 (apel q x))  >
          ≐ < apt A x ‣ u , apt B (x , u) ‣ pj1 (pj1 (apel p' x)) u >
       eq1 = pj2 lm7a
       lm7b = prj2 lm7 (pj1 (apel q x))
       v = pj1 lm7b
       eq2 : < apt A x ‣ v , apt B (x , v) ‣ pj1 (pj1 (apel p x)) v > ≐
          < apt A x ‣ pj1 (apel q x) ,
          apt B (x , pj1 (apel q x)) ‣ pj1 (pj1 (apel p' x)) (pj1 (apel q x))  >
       eq2 = pj2 lm7b
       

       eq :  (apt B (x , pj1 (apel q x))) ‣ (pj1 (pj1 (apel p  x)) (pj1 (apel q x))) ≐ 
             (apt B (x , pj1 (apel q x))) ‣ (pj1 (pj1 (apel p' x)) (pj1 (apel q x)))
       eq = Π-f-exp3c A B x (pj1 (apel p x)) (pj1 (apel p' x)) lm5 (pj1 (apel q x))     
   in (<<>> eq)
   ))



app-cong2-raw :  {Γ : ctx} 
    -> (A : ty Γ)  -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (a a' : raw Γ)
    -> (q : Γ ==> a :: A)
    -> (q' : Γ ==> a' :: A)
    -> (Γ ==> a == a' :: A)
    -> << Raw Γ >>  app A B c p a q ~ app A B c p a' q'
app-cong2-raw {Γ} A B c p a a' q q' r =
 <<>> (<<>> 
   (\ x ->  
  let  lm1 : apr a x ≐ apt A x ‣ pj1 (apel q x)
       lm1 = pj2 (apel q x)
       lm2 : apr a' x ≐ apt A x ‣ pj1 (apel q' x)
       lm2 = pj2 (apel q' x)
       lm2b :  apr a x ≐ apr a' x
       lm2b = prj1 r x
       lm3 : apt A x ‣ pj1 (apel q x) ≐ apt A x ‣ pj1 (apel q' x)
       lm3 = traV (symV lm1) (traV lm2b lm2)
       main : (apt B (x , pj1 (apel q x))) ‣ (pj1 (pj1 (apel p x)) (pj1 (apel q x))) ≐ 
              (apt B (x , pj1 (apel q' x))) ‣ (pj1 (pj1 (apel p x)) (pj1 (apel q' x)))
       main = Π-f-exp3b A B x (pj1 (apel p x)) (pj1 (apel q x)) (pj1 (apel q' x)) lm3
  in <<>> main
  ))




app-irr2 :  {Γ : ctx} 
    -> (A : ty Γ)  -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (q q' : Γ ==> a :: A)
    -> << Raw Γ >>  app A B c p a q ~ app A B c p a q'
app-irr2 {Γ} A B c p a q q'  =
  <<>> (<<>> 
   (\ x ->   
      let lm1 : apr a x ≐ apt A x ‣ pj1 (apel q x)
          lm1 = pj2 (apel q x)
          lm2 : apr a x ≐ apt A x ‣ pj1 (apel q' x)
          lm2 = pj2 (apel q' x)
          lm3 : apt A x ‣ pj1 (apel q x) ≐ apt A x ‣ pj1 (apel q' x)
          lm3 = traV (symV lm1) lm2
          main : (apt B (x , pj1 (apel q x))) ‣ (pj1 (pj1 (apel p x)) (pj1 (apel q x))) ≐ 
                 (apt B (x , pj1 (apel q' x))) ‣ (pj1 (pj1 (apel p x)) (pj1 (apel q' x)))
          main = Π-f-exp3b A B x (pj1 (apel p x)) (pj1 (apel q x)) (pj1 (apel q' x)) lm3
      in <<>> main
  ))



app-cong-raw :  {Γ : ctx} 
    -> (A : ty Γ)  -> (B : ty (Γ ▷ A))
    -> (c c' : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (p' : Γ ==> c' :: Π-f {Γ} A B)
    -> (Γ ==> c == c' :: Π-f {Γ} A B)
    -> (a a' : raw Γ)
    -> (q : Γ ==> a :: A)
    -> (q' : Γ ==> a' :: A)
    -> (Γ ==> a == a' :: A)
    -> << Raw Γ >>  app A B c p a q ~ app A B c' p' a' q'
app-cong-raw {Γ} A B c c' p p' r a a' q q' t =
    let lm1 : << Raw Γ >>  app A B c p a q ~ app A B c' p' a q
        lm1 = app-cong1-raw {Γ} A B c c' p p' r a q
        lm2 : << Raw Γ >>  app A B c' p' a q ~ app A B c' p' a' q'
        lm2 = app-cong2-raw {Γ} A B c' p' a a' q q' t
    in (tra' lm1 lm2)




app-irr :  {Γ : ctx} 
    -> (A : ty Γ)  -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p p' : Γ ==> c :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (q q' : Γ ==> a :: A)
    -> << Raw Γ >>  app A B c p a q ~ app A B c p' a q'
app-irr {Γ} A B c p p' a q q' = 
    let lm1 : << Raw Γ >>  app A B c p a q ~ app A B c p' a q
        lm1 = app-irr1 {Γ} A B c p p' a q
        lm2 : << Raw Γ >>  app A B c p' a q ~ app A B c p' a q'
        lm2 = app-irr2 {Γ} A B c p' a q q'
    in tra' lm1 lm2
  

{--


--}


-- Pi-elimination


Π-e :  {Γ : ctx} 
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (a : raw Γ)
    -> (q : Γ ==> a :: A)
--  -----------------------------------------
    ->  Γ ==> app A B c p a q :: B [[ els q ]]
Π-e A B c p a q  = mk-elt (\u ->
        let lma : (apr a u) ∈ (apt A  u)
            lma = apel q u
            lma1 : (apr a u) ≐ (apt A u) ‣ pj1 (apel q u)
            lma1 = pj2 (apel q u)
            lmc : (apr c u) ∈ (apt (Π-f A B) u)
            lmc = apel p u
            lmc1 : (apr c u) ≐ (apt (Π-f A B) u) ‣ pj1 (apel p u)
            lmc1 = pj2 (apel p u)
            lmd = (pj1 (pj1 (apel p u)) (pj1 (apel q u)))
            main : (apt B (u , pj1 (apel q u))) ‣ (pj1 (pj1 (apel p u)) (pj1 (apel q u))) ∈  (apt (B [[ els q ]])  u)
            main = lmd , (refV _)
        in main)




Π-e-cong :  {Γ : ctx} 
    -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
    -> (c c' : raw Γ)
    -> (p : Γ ==> c :: Π-f {Γ} A B)
    -> (p' : Γ ==> c' :: Π-f {Γ} A B)
    -> (Γ ==> c == c' :: Π-f {Γ} A B)
    -> (a a' : raw Γ)
    -> (q : Γ ==> a :: A)
    -> (q' : Γ ==> a' :: A)
    -> (Γ ==> a == a' :: A)
--  -----------------------------------------
    ->  Γ ==> app A B c p a q == app A B c' p' a' q'  :: B [[ els q ]]
Π-e-cong {Γ} A B c c' p p' p'' a a' q q' q'' = 
   let rm = >><< (app-cong-raw {Γ} A B c c' p p' p'' a a' q q' q'')
   in
       pair (λ x → >><< (>><< rm x))  
            (pair (Π-e A B c p a q) 
                  (elttyeq  (Π-e A B c' p' a' q')  (tyeq-subst2 B (els q') (els q) (els-cong q' q  (tmsym _ _ _ q'')))))



-- towards the beta-rule

Π-beta-raw :  {Γ : ctx} 
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (b : raw (Γ ▷ A))
       -> (p : Γ ▷ A ==> b :: B)
       -> (a : raw Γ)
       -> (q : Γ ==> a :: A)
       -> (x : || κ Γ ||)
       ->  apr (app A B (lambda A B b) (Π-i A {B} {b} p) a q)  x ≐  apr (b [ els q ]) x  
Π-beta-raw {Γ} A B b p a q x = 
      let  lm1 : Γ ==> b [ els q ] :: B [[ els q ]]
           lm1 = elt-subst (els q) p 
           lm1x : apr (b [ ext-el {Γ} A a q ]) x ∈ (apt (B [[ els q ]]) x)
           lm1x = apel lm1 x
           beq = pj2 lm1x
           lm2 : (apt B (x , pj1 (apel q x))) ‣ (pj1 (pj1 (apel (Π-i A p) x)) (pj1 (apel q x)))
                ≐  apr (b [ els q ]) x
           lm2 = symV beq
           main : apr (app A B (lambda A B b) (Π-i A {B} {b} p) a q)  x ≐ apr (b [ els q ]) x
           main = lm2
      in main





Π-beta :  {Γ : ctx} 
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (b : raw (Γ ▷ A))
       -> (p : Γ ▷ A ==> b :: B)
       -> (a : raw Γ)
       -> (q : Γ ==> a :: A)
--  -----------------------------------------
       ->  Γ ==> app A B (lambda A B b) (Π-i A {B} {b} p) a q  
             ==  b [ els q ] :: B [[ els q ]]
Π-beta A B b p a q = pair (Π-beta-raw A B b p a q) 
                            (pair (Π-e A B (lambda A B b) (Π-i A {B} {b} p) a q)
                                  (elt-subst (els q) p ))



Π-beta-gen :  {Γ : ctx} 
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (b : raw (Γ ▷ A))
       -> (p : Γ ▷ A ==> b :: B)
       -> (r : Γ  ==> (lambda A B b) :: Π-f {Γ} A B)
       -> (a : raw Γ)
       -> (q : Γ ==> a :: A)
--  -----------------------------------------
       ->  Γ ==> app A B (lambda A B b) r a q  
             ==  b [ els q ] :: B [[ els q ]]
Π-beta-gen {Γ} A B b p r a q = 
   let lm :  Γ ==> app A B (lambda A B b) (Π-i A {B} {b} p) a q  
             ==  b [ els q ] :: B [[ els q ]]
       lm = Π-beta A B b p a q
       lm2 : << Raw Γ >> (app A B (lambda A B b) r a q)  ~ (app A B (lambda A B b) (Π-i A {B} {b} p) a q) 
       lm2 = app-irr A B (lambda A B b) r (Π-i A {B} {b} p) a q q
   in pair (λ x → traV (>><< (>><< (>><< lm2) x)) ((prj1 lm) x)) 
           (pair (mk-elt (λ x →  memV-left-ext (apr (app A B (lambda A B b) r a q) x) 
                                                (apr (app A B (lambda A B b) (Π-i A {B} {b} p) a q) x) (apt (B [[ els q ]]) x)
                                                 (>><< (>><< (>><< lm2) x)) 
                                                 (apel (prj1 (prj2 lm)) x))) 
                 (prj2 (prj2 lm)))


