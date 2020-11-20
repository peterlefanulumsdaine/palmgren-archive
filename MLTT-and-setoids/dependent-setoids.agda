
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- {-# OPTIONS --no-eta-equality #-}

-- Agda version 2.5.2

module dependent-setoids where

open import basic-types
open import basic-setoids


record Fam (A : setoid) : Set1 where
  field 
     std : || A || -> setoid
     trp : {a b : || A ||} -> (p : < A > a ~ b) -> || std a => std b ||
     id-trp : {a : || A ||} -> (p : < A > a ~ a) -> 
               (x : || std a ||) -> < std a > ap (trp p) x ~ x
     ir-trp : {a b : || A ||} -> (p  q : < A > a ~ b) ->  
               (x : || std a ||) -> < std b > ap (trp p) x ~ ap (trp q) x
     fn-trp : {a b c : || A ||} -> (q : < A > b ~ c) -> (p : < A > a ~ b) ->  (r : < A > a ~ c) ->
               (x : || std a ||) -> < std c >  ap (trp r) x ~ ap (trp q) (ap (trp p) x) 

-- introduce short for :  Fam.std F a    and    ap (Fam.trp F p)

-- ok ?

infix 5 _§_ 

_§_ : {A : setoid} -> (F : Fam A) -> (a : || A ||) -> setoid
_§_ F a = Fam.std F a

infix 5 _±_
_±_ : {A : setoid} -> (F : Fam A) -> {a b : || A ||} -> (p : < A > a ~ b) -> || (F § a)  => (F § b) ||
_±_ F p = Fam.trp F p

Fam-flip : (A : setoid) -> (F : Fam A) -> (a b : || A ||) -> (p : < A >  a ~ b) ->
       (x : || F § a ||) ->  (y : || F § b ||) -> 
       < F § b > ap (F ± p) x ~ y  -> < F § a >  x  ~  ap (F ± (sym p)) y 
Fam-flip A F a b p x y q = let lm1 : < F § a > ap (F ± (sym p)) (ap (F ± p) x) 
                                     ~ ap (F ± (sym p)) y
                               lm1 = extensionality (F ± (sym p)) (ap (F ± p) x) y q
                               lm2 : < F § a >  x  ~ ap (F ± (sym p)) (ap (F ± p) x)
                               lm2 = tra (sym (Fam.id-trp F (refl A a) x)) 
                                                       (Fam.fn-trp F _ _ _ x)
                               main : < F § a >  x  ~  ap (F ± (sym p)) y
                               main = tra lm2 lm1
                           in  main

Fam-inv-eq : (A : setoid) -> (F : Fam A) -> (a b : || A ||) -> (p : < A >  a ~ b) ->
       (x : || F § b ||) ->
       < F § b > ap (F ± p) (ap (F ± (sym p)) x) ~  x
Fam-inv-eq A F a b p x = tra (sym (Fam.fn-trp F _ _ _ x)) (Fam.id-trp F (refl A b) x)

Fam-inv-eq+ : (A : setoid) -> (F : Fam A) -> (a b : || A ||) -> (p : < A >  a ~ b) -> 
       (q : < A >  b ~ a) ->    (x : || F § b ||) ->
       < F § b > ap (F ± p) (ap (F ± q) x) ~  x
Fam-inv-eq+ A F a b p q x = tra (sym (Fam.fn-trp F _ _ _ x)) (Fam.id-trp F (refl A b) x)

Fam-inv-eq2 : (A : setoid) -> (F : Fam A) -> (a b c : || A ||) ->
       (p : < A >  a ~ b) -> (q : < A >  b ~ c) -> (r : < A >  a ~ c) ->
       (x : || F § c ||) ->
       < F § c > ap (F ± r) (ap (F ± sym p) (ap (F ± sym q) x)) ~ x
Fam-inv-eq2 A F a b c p q r x = sym (tra (sym (Fam-inv-eq A F b c q x)) 
                                            (Fam.fn-trp F r (sym p) q (ap (F ± sym {A} q) x)))


Fam-fn2-eq : {A : setoid} -> (F : Fam A) -> {a b c d : || A ||}
    -> (p1 : < A >  a ~ b)  -> (p2 : < A >  b ~ d) 
    -> (q1 : < A >  a ~ c)  -> (q2 : < A >  c ~ d)
    -> (x : || F § a ||) -> < F § d > ap (F ± p2) (ap (F ± p1) x) ~ ap (F ± q2) (ap (F ± q1) x)
Fam-fn2-eq {A} F {a} {b} {c} {d} p1 p2 q1 q2 x 
         = tra {F § d} (sym {F § d} (Fam.fn-trp F _ _ _ x)) 
                       (Fam.fn-trp F q2 q1 (tra {A} q1 q2) x)

 -- fn-trp : {a b c : || A ||} -> (q : < A > b ~ c) -> (p : < A > a ~ b) ->  (r : < A > a ~ c) ->
 --              (x : || std a ||) -> < std c >  ap (trp r) x ~ ap (trp q) (ap (trp p) x) 



infix 5 _⊙_

-- compose family with function

_⊙_ : {A B : setoid} -> (F : Fam B) -> (f : || A => B ||) -> Fam A
_⊙_ {A} {B} F f =  
       record{ std = λ x →  F § (ap f x);
               trp = λ p → record { op =  λ x →  ap (F ± (extensionality f _ _ p)) x ; 
                                    ext = λ x y q → extensionality (F ± (extensionality f _ _ p)) x y q };
               id-trp = λ p x →  Fam.id-trp F (extensionality f _ _ p) x ;
               ir-trp = λ p q x → Fam.ir-trp F (extensionality f _ _ p) (extensionality f _ _ q) x;
               fn-trp = λ q p n x → Fam.fn-trp F (extensionality f _ _ q) (extensionality f _ _ p) (extensionality f _ _ n) x
             }



Σ-std : (A : setoid) -> (F : Fam A) -> setoid
Σ-std A F = record {object =  Σ (|| A ||) (\x -> || F § x ||)
                   ; _∼_  =  λ u v →  Σ (< A > pj1 u ~  pj1 v) (\p -> < F § (pj1 v) >  (ap (F ± p) (pj2 u)) ~ pj2 v)
                   ; eqrel = pair (λ x → ((refl A (pj1 x)) , (Fam.id-trp F (refl A (pj1 x)) (pj2 x))))
                                  (pair (λ x y p → 
                                          (sym (pj1 p) , 
                                           sym (Fam-flip A F (pj1 x) (pj1 y) (pj1 p) (pj2 x) (pj2 y) (pj2 p)))) 
                                        (λ x y z p q → 
                                          (tra (pj1 p) (pj1 q) , 
                                            let p1 : < A > pj1 x ~ pj1 y
                                                p1 = pj1 p
                                                p2 : < F § (pj1 y) > ap (F ± p1) (pj2 x) ~ pj2 y
                                                p2 = pj2 p
                                                q1 : < A > pj1 y ~ pj1 z
                                                q1 = pj1 q
                                                q2 : < F § (pj1 z) > ap (F ± q1) (pj2 y) ~ pj2 z
                                                q2 = pj2 q
                                                lm :  < F § (pj1 z) >  ap (F ± (pj1 q)) (ap (F ± (pj1 p)) (pj2 x)) ~ 
                                                                                  ap (F ± (pj1 q)) (pj2 y)
                                                lm = extensionality (F ± (pj1 q)) _ _ p2
                                                main : < F § (pj1 z) >
                                                       ap (F ± (tra (pj1 p) (pj1 q))) (pj2 x) ~ pj2 z
                                                main = tra {F § (pj1 z)} 
                                                         (tra 
                                                               (Fam.fn-trp F _ _ _ (pj2 x))
                                                               lm) q2
                                            in main)))                         
                   }

Π-std : (A : setoid) -> (F : Fam A) -> setoid
Π-std A F = record {object =  Σ ((x : || A ||) -> || F § x ||)
                                (\f -> (x y : || A ||) -> (p : < A > x ~ y) ->
                                   < F § y >  (ap (F ± p) (f x)) ~ (f y))
                   ; _∼_  =  λ u v →  (x : || A ||) ->  < F § x > (pj1 u) x  ~ (pj1 v) x
                   ; eqrel = pair (λ f x → refl (F § x) (pj1 f x) ) 
                                  (pair (λ f g p x → sym (p x)) 
                                        (λ f g h p q x → tra (p x) (q x)))                         
                   }



-- Σ ((x : || A ||) -> || Fam.std F x ||)
--                                (\f -> (x y : || A ||) -> (p : < A > x ~ y) ->
--                                   < Fam.std F y >  (ap (Fam.trp F p) (f x)) ~ (f y))

-- name ?
comp-Π-std : {A B : setoid} -> {F : Fam B} -> || Π-std B F || -> (f : || A => B ||) ->  || Π-std A (F ⊙ f) ||
comp-Π-std g f = (λ x → pj1 g (ap f x)) , 
                   (λ x y p → pj2 g (ap f x) (ap f y) (setoidmap.ext f x y p))

π1 :  (A : setoid) -> (F : Fam A) -> || (Σ-std A F) => A ||
π1 A F = record { op = λ u → pj1 u 
                ; ext = λ u v p → pj1 (>< p) }

π2 : (A : setoid) -> (F : Fam A) -> || Π-std (Σ-std A F) (F ⊙ (π1 A F))  ||
π2 A F = (λ u → pj2 u) , (λ u v p → pj2 (>< p))



dpair :  (A B : setoid) -> (F : Fam A) 
   -> (f : || B => A ||) -> (g : || Π-std B (F ⊙ f)||) -> || B => Σ-std A F ||
dpair A B F f g = record { op = λ x → (ap f x) , (pj1 g x) 
                         ; ext = λ x y p →   <> ((setoidmap.ext f x y p) , (pj2 g x y p)) 
                         }



dpair-eq1 : (A B : setoid) -> (F : Fam A) 
             -> (f : || B => A ||) -> (g : || Π-std B (F ⊙ f)||)
             ->  <  B => A >  (π1 A F) ° (dpair A B F f g) ~ f
dpair-eq1 A B F f g = <> (λ x → (refl A _))


dpair-eq2 : (A B : setoid) -> (F : Fam A) 
             -> (f : || B => A ||) -> (g : || Π-std B (F ⊙ f)||)
             ->  <   Π-std B (F ⊙ f) > comp-Π-std {_} {_} {(F ⊙ (π1 A F))} (π2 A F) (dpair A B F f g) ~ g
dpair-eq2 A B F f g = <> (λ x → refl ((F ⊙ f) § x) _)

{-- coherence problem  (F ° f) ° h is not definitionally equal to F ° (f ° h)

dpair-eq3 : (A B : setoid) -> (F : Fam A) 
             -> (f : || B => A ||) -> (g : || Π-std B (comp-Fam F f)||)
             -> (C : setoid) -> (h : || C => B ||)
             -> < C => Σ-std A F > comp (dpair A B F f g) h ~ (dpair ? ? ? (comp f h) (comp-Π-std _ _  g h))

dpair-eq3 = ?

--}



-- comparing two families

record Fam-iso (A : setoid) (F G : Fam A) : Set where
   field
      lociso : (x : || A ||) ->  (F § x) ≅  (G § x)
      cohere : (x y : || A ||) -> (p : < A > x ~ y) ->
                (< (F § x) => (G § y) > 
                     (fwd (lociso y)) ° (F ± p)
                  ~  ((G ± p) ° (fwd (lociso x)))) 



comp-Fam-lm-iso : (A B C : setoid) 
     -> (f : || A => B ||) -> (g : || B => C ||) -> (F : Fam C)
     -> Fam-iso A (F ⊙ (g ° f)) ((F ⊙ g) ⊙ f)
comp-Fam-lm-iso A B C f g F 
     = record { lociso = λ x → (record { op = λ y → y 
                                       ; ext = λ x u v → v }) , 
                              ((record { op =  λ y → y 
                                       ; ext = λ x u v → v }) ,
                              (pair (λ z → refl ((F ⊙ (g ° f)) § x) z) 
                                    (λ z → refl (((F ⊙ g) ⊙ f) § x) z))) 
              ; cohere = \ x y p -> <> (\ z -> (refl (((F ⊙ g) ⊙ f) § y) _)) }

comp-Fam-lm2-iso : (A : setoid)  (F : Fam A)
     -> Fam-iso A (F ⊙ (idmap {A})) F
comp-Fam-lm2-iso A F 
     = record { lociso = λ x → (record { op = λ y → y 
                                       ; ext = λ x u v → v }) , 
                              ((record { op =  λ y → y 
                                       ; ext = λ x u v → v }) ,
                              (pair (λ z → refl ((F ⊙ idmap) § x) _) 
                                    (λ z → refl (F § x) _))) 
              ; cohere =  \ x y p -> <> (\ z → refl (F § y) _ )}



-- more useful examples of compositions .. todo

fix1-trp-op-lm : {A : setoid} -> {F : Fam A} ->  (G : Fam (Σ-std A F)) -> (x : || A ||) 
  -> {a b : || F § x ||} 
  -> (p : < F § x > a ~ b) -> < (Σ-std A F) > (x , a) ~ (x , b)
fix1-trp-op-lm {A} {F} G x {a} {b} p = <> ((refl A x) , (tra (Fam.id-trp F (refl A x) a) p ))




fix1-trp-op : {A : setoid} -> {F : Fam A} ->  (G : Fam (Σ-std A F)) -> (x : || A ||) 
  ->  {a b : || F § x ||} 
  -> (p : < F § x > a ~ b) -> || G § (x , a) || -> || G § (x , b) ||
fix1-trp-op {A} {F} G x {a} {b} p z 
     = let q : < (Σ-std A F) >  (x , a) ~ (x , b)
           q = fix1-trp-op-lm {A} {F} G x p
       in ap (G ± q) z 

-- so this is 
-- fix1-trp-op {A} {F} G x {a} {b} p z  = ap (G ± ((refl A x) , (tra {F § x} (Fam.id-trp F (refl A x) a) p))) z
--

-- fix1-trp-fun G x p  is G_x(p)

fix1-trp-fun : {A : setoid} -> {F : Fam A} ->  (G : Fam (Σ-std A F)) -> (x : || A ||) 
  -> {a b : || F § x ||} 
  -> (p : < F § x > a ~ b) -> || (G § (x , a)) => (G § (x , b)) ||
fix1-trp-fun {A} {F} G x {a} {b} p = record { op =  fix1-trp-op {A} {F} G x p 
                                            ; ext = λ u v q → 
                                                  extensionality (G ± (fix1-trp-op-lm {A} {F} G x p)) 
                                                              u v q  
                                            }

-- fix1 G x  is G_x



fix1 : {A : setoid} -> {F : Fam A} ->  (G : Fam (Σ-std A F)) -> (x : || A ||) -> Fam (F § x)
fix1 {A} {F} G x = record { std = λ y → G § (x , y) 
                             ; trp = λ {a} {b} p -> fix1-trp-fun {A} {F} G x p
                             ; id-trp = λ {a} p y →  
                                      Fam.id-trp G (fix1-trp-op-lm {A} {F} G x p) y
                             ; ir-trp = λ {a} {b} p q y → 
                                      Fam.ir-trp G (fix1-trp-op-lm {A} {F} G x p) 
                                                   (fix1-trp-op-lm {A} {F} G x q) y 
                             ; fn-trp = λ {a} {b} {c} q p r y → 
                                      Fam.fn-trp G (fix1-trp-op-lm {A} {F} G x q) 
                                                   (fix1-trp-op-lm {A} {F} G x p)
                                                   (fix1-trp-op-lm {A} {F} G x r) y
                             }


Π-fam-trp-op-op-eq : {A : setoid} -> {F : Fam A} ->  (G : Fam (Σ-std A F)) 
    -> {a b : || A ||} -> (p : < A > a ~ b) 
    -> (z : || F § b ||) -> < Σ-std A F >  (a , (ap (F ± (sym {A} p)) z))  ~ (b , z)
Π-fam-trp-op-op-eq {A} {F} G {a} {b} p z = <> (p , Fam-inv-eq A F a b p z)


Π-fam-trp-op-op : {A : setoid} -> {F : Fam A} ->  (G : Fam (Σ-std A F)) 
    -> {a b : || A ||} -> (p : < A > a ~ b) 
    ->  || Π-std (F § a) (fix1 {A} {F} G a) || 
    ->  (x : || F § b ||) ->  || (fix1 {A} {F} G b) § x ||
Π-fam-trp-op-op {A} {F} G {a} {b} p f z = 
    let -p = sym p
        G1 = fix1 {A} {F} G
        lm : || F § a ||
        lm = ap (F ± -p) z
        lm2 : || (G1 a) § (ap (F ± -p) z) ||
        lm2 = pj1 f lm
        main :  || (G1 b) § z ||
        main = ap (G ± (Π-fam-trp-op-op-eq {A} {F} G p z)) lm2 
    in main



-- main    Π-fam-trp-op-op {A} {F} G {a} {b} p f z =  ap (G ± ( p , Fam-inv-eq A F a b p z)) (pj1 f (ap (F ± -p) z))

Π-fam-trp-op : {A : setoid} -> {F : Fam A} ->  (G : Fam (Σ-std A F)) 
    -> (a b : || A ||) -> (p : < A > a ~ b) 
    ->  || Π-std (F § a) (fix1 {A} {F} G a) || 
    ->  || Π-std (F § b) (fix1 {A} {F} G b) ||
Π-fam-trp-op {A} {F} G a b p f 
  = (Π-fam-trp-op-op {A} {F} G p f) ,
    (λ x y q → let -p = (sym {A} p)
                   G1 = fix1 {A} {F} G
                   ext = extensionality
                   eq1 : < F § a > ap (F ± -p) x ~ ap (F ± -p) y
                   eq1 =  ext (F ± -p) _ _ q
                   lm : < (G1 a) § (ap (F ± -p) y) >
                         ap ((G1 a) ± (ext (F ± -p) _ _ q))
                            (pj1 f (ap (F ± -p) x))  ~ pj1 f (ap (F ± -p) y)
                   lm = pj2 f (ap (F ± -p) x) (ap (F ± -p) y) eq1
                   eq2 : < Σ-std A F >  (a , ap (F ± -p) y) ~ (b , y)
                   eq2 = <> (p , (Fam-inv-eq A F a b p y))
                   lm2 :  < (G1 b) § y > 
                           ap (G ± eq2) (ap ((G1 a) ± (ext (F ± -p) _ _ q))
                             (pj1 f (ap (F ± -p) x)))
                           ~  ap (G ± eq2) (pj1 f (ap (F ± -p) y))
                   lm2 = ext (G ± eq2) _ _ lm
                   eq3 : < Σ-std A F >  (a , ap (F ± -p) x) ~ (b , x)
                   eq3 = <> (p , (Fam-inv-eq A F a b p x))
                   lm3 :  < (G1 b) § y >
                            ap ((G1 b) ± q) 
                                (ap (G ± eq3) (pj1 f (ap (F ± -p) x))) ~ 
                            ap (G ± eq2) (ap ((G1 a) ± (ext (F ± -p) _ _ q))
                                (pj1 f (ap (F ± -p) x)))
                   lm3 = Fam-fn2-eq G _ _ _ _ _
                   main : < (G1 b) § y >
                            ap ((G1 b) ± q) 
                                (ap (G ± eq3) (pj1 f (ap (F ± -p) x))) ~                    
                            ap (G ± eq2) (pj1 f (ap (F ± -p) y))
                   main = tra lm3 lm2
               in main)



Π-fam-std : {A : setoid} -> (F : Fam A) ->  (G : Fam (Σ-std A F)) 
         -> (x : || A ||) -> setoid
Π-fam-std {A} F G x =  Π-std (F § x) (fix1 {A} {F} G x)

Π-fam-trp : {A : setoid} -> (F : Fam A) ->  (G : Fam (Σ-std A F)) ->  
  (a b : || A ||) ->  (p : < A > a ~ b) ->
        || Π-std (F § a) (fix1 {A} {F} G a) => Π-std (F § b) (fix1 {A} {F} G b) ||
Π-fam-trp {A} F G a b p =         record { op = Π-fam-trp-op {A} {F} G a b p 
                                         ; ext = λ f g q ->
                                                        <>  (\ x -> let -p = sym {A} p
                                                                        ext = extensionality
                                                                        q'' = >< q
                 
                                                                        q' : (t : || F § a ||) -> 
                                                                           < (fix1 {A} {F} G a) § t > (pj1 f) t  ~ (pj1 g) t 
                                                                        q' = λ t →  q'' t   
                                                                        --  λ u v →  (x : || A ||) ->  < F § x > (pj1 u) x  ~ (pj1 v) x
                                                                        lm : < (fix1 {A} {F} G a) § (ap (F ± -p) x) > 
                                                                             (pj1 f) (ap (F ± -p) x)  ~ (pj1 g) (ap (F ± -p) x)
                                                                        lm = q' (ap (F ± -p) x)
                                                                        main : < fix1 {A} {F} G b § x > Π-fam-trp-op-op {A} {F} G p f x ~
                                                                                                  Π-fam-trp-op-op {A} {F} G p g x
                                                                        main = ext (G ±  <> (p , (Fam-inv-eq A F a b p x))) _ _ lm -- ext ((G ± ( p , Fam-inv-eq A F a b p x))) _ _ lm
                                                               in main)
                                          } 



Π-fam : {A : setoid} -> (F : Fam A) ->  (G : Fam (Σ-std A F)) ->  Fam A
Π-fam {A} F G = record { std = λ x → Π-std (F § x) (fix1 {A} {F} G x) 
                        ; trp = λ {a} {b} p ->  Π-fam-trp {A} F G a b p
                        ; id-trp = λ {a} p f -> <> (\ x -> 
                              let -p = sym {A} p
                                  lm1 : < F § a > ap (F ± -p) x ~ x
                                  lm1 = Fam.id-trp F -p x
                                  lm2 :  < fix1 {A} {F} G a § x >
                                        ap (fix1 {A} {F} G a ± Fam.id-trp F (sym {A} p) x) (pj1 f (ap (F ± sym {A} p) x)) ~
                                        pj1 f x
                                  lm2 = pj2 f (ap (F ± -p) x) x lm1
                                  lm3 : < fix1 {A} {F} G a § x > 
                                                 ap (G ± (<> ( p , Fam-inv-eq A F a a p x)) ) (pj1 f (ap (F ± -p) x)) 
                                                 ~ ap (fix1 {A} {F} G a ± (Fam.id-trp F (sym {A} p) x)) (pj1 f (ap (F ± (sym {A} p)) x))
                                  lm3 = Fam.ir-trp G _ _ _
                                  lm4 : < fix1 {A} {F} G a § x > ap (G ± (<> (p , Fam-inv-eq A F a a p x))) (pj1 f (ap (F ± -p) x)) 
                                                                 ~ pj1 f x
                                  lm4 = tra lm3 lm2
                                  main : < fix1 {A} {F} G a § x > Π-fam-trp-op-op {A} {F} G p f x ~ pj1 f x
                                  main = lm4
                              in main)
                        ; ir-trp = λ {a} {b} p q f -> <> (\ x ->
                                      let -p = sym p
                                          -q = sym q
                                          lm1 : < Fam.std F a >  ap (F ± -p) x  ~ ap (F ± -q) x 
                                          lm1 = Fam.ir-trp F -p -q _
                                          exf : < fix1 {A} {F} G a § ap (F ± -q) x >
                                                 ap (fix1 {A} {F} G a ± Fam.ir-trp F (-p) (-q) x) (pj1 f (ap (F ± -p) x))
                                                  ~ pj1 f (ap (F ± -q) x)
                                          exf = pj2 f (ap (F ± -p) x) (ap (F ± -q) x) lm1
                                          exf2 : <  Fam.std G (b , x) >
                                                  ap (G ± (<> ( q , Fam-inv-eq A F a b q x))) 
                                                     (ap (fix1 {A} {F} G a ± Fam.ir-trp F (-p) (-q) x) (pj1 f (ap (F ± -p) x)))
                                                  ~  ap (G ± (<> ( q , Fam-inv-eq A F a b q x))) (pj1 f (ap (F ± -q) x))
                                          exf2 = extensionality ((G ± (<> ( q , Fam-inv-eq A F a b q x)))) _ _ exf
                                           
                                          lm2 : < Fam.std G (b , x) > ap (G ± (<> ( p , Fam-inv-eq A F a b p x))) (pj1 f (ap (F ± -p) x)) 
                                                                    ~ ap (G ± (<> ( q , Fam-inv-eq A F a b q x))) (pj1 f (ap (F ± -q) x))
                                          lm2 = tra (Fam.fn-trp G _ _ _ _) exf2
                                          main : < Fam.std G (b , x) > (Π-fam-trp-op-op {A} {F} G p f x) 
                                                                       ~ (Π-fam-trp-op-op {A} {F} G q f x)
                                          main = lm2
                                      in main)

 
                        ; fn-trp = λ {a} {b} {c} q p r f -> <> (\ x →
                                      let -p = sym p
                                          -q = sym q
                                          -r = sym r
                                          lm1 :  < F § a > ap (F ± -r) x ~ ap (F ± -p) (ap (F ± -q) x)
                                          lm1 = Fam.fn-trp F -p -q -r x 
                                          -- lm1' :  < F § a >  ap (F ± -p) (ap (F ± -q) x)  ~ ap (F ± -r) x
                                          -- lm1' = sym { F § a} lm1

                                          exf : < G § (a , ap (F ± -p) (ap (F ± -q) x)) >
                                                 ap (fix1 {A} {F} G a ± Fam.fn-trp F -p -q -r x)
                                                    (pj1 f (ap (F ± -r) x))
                                                 ~ pj1 f (ap (F ± -p) (ap (F ± -q) x))
                                          exf = pj2 f (ap (F ± -r) x) (ap (F ± -p) (ap (F ± -q) x)) lm1
                                          eq : < Σ-std A F > (a , ap (F ± -p) (ap (F ± -q) x)) ~ (c , x)
                                          eq = <> (r ,  Fam-inv-eq2 A F a b c p q r x)

                                          lm1-5 :  < G § (c , x) > 
                                               ap (G ± eq) 
                                                 (ap (fix1 {A} {F} G a ± Fam.fn-trp F -p -q -r x)
                                                    (pj1 f (ap (F ± -r) x)))
                                                 ~ 
                                               ap (G ± eq) (pj1 f (ap (F ± -p) (ap (F ± -q) x)))
                                          lm1-5 = extensionality (G ± eq) _ _ exf
                                          lm1-6 :  < G § (c , x) > 
                                                ap (G ± (<> ( r , Fam-inv-eq A F a c r x))) 
                                                    (pj1 f (ap (F ± -r) x))
                                                 ~ 
                                               ap (G ± eq) 
                                                 (ap (fix1 {A} {F} G a ± Fam.fn-trp F -p -q -r x)
                                                    (pj1 f (ap (F ± -r) x)))
                                          lm1-6 = Fam.fn-trp G _ _ _ _
                                   
                                          lm2 :  < G § (c , x) > 
                                                 ap (G ± (<> ( r , Fam-inv-eq A F a c r x))) 
                                                    (pj1 f (ap (F ± -r) x))
                                                    ~
                                                 ap (Fam.trp G {(b , _ )} {( c , _ )} (<> ( q , (Fam-inv-eq A F b c q x))) ) 
                                                    (ap (G ± (<> ( p , (Fam-inv-eq A F a b p (ap (F ± -q) x))))) 
                                                        (pj1 f (ap (F ± -p) (ap (F ± -q) x))))
                                           
                                                
                                          lm2 = tra lm1-6 (tra lm1-5 ( Fam.fn-trp G _ _ _ _))
 
                                          lm3 :  < G § (c , x) > 
                                                 ap (G ± (<> ( r , Fam-inv-eq A F a c r x))) (pj1 f (ap (F ± -r) x))
                                                    ~
                                                 ap (G ± (<> ( q , Fam-inv-eq A F b c q x))) 
                                                    (pj1 (ap (Π-fam-trp F G a b p) f) (ap (F ± -q) x))

                                                
                                          lm3 = lm2
 
                                          lm4 :  < G § (c , x) > Π-fam-trp-op-op {A} {F} G {a} {c} r f x ~
                                                       Π-fam-trp-op-op {A} {F} G {b} {c} q (ap (Π-fam-trp F G a b p) f) x
                                          lm4 = lm3
                                          lm5 :  < G § (c , x) > (pj1 (ap (Π-fam-trp F G a c r) f)) x 
                                                                    ~ (pj1 (ap (Π-fam-trp F G b c q) (ap (Π-fam-trp F G a b p) f))) x 
                                          lm5 = lm4
                                      in lm5)
                        }





Σ-fam-std : {A : setoid} -> (F : Fam A) ->  (G : Fam (Σ-std A F)) 
         -> (x : || A ||) -> setoid
Σ-fam-std {A} F G x =  Σ-std (F § x) (fix1 {A} {F} G x)

Σ-fam-trp-op : {A : setoid} -> (F : Fam A) ->  (G : Fam (Σ-std A F)) ->  
  (a b : || A ||) ->  (p : < A > a ~ b) ->
        || (Σ-fam-std F G a) || -> || (Σ-fam-std F G b) ||
Σ-fam-trp-op {A} F G a b p ( x , y ) = (ap (F ± p) x) , (ap (G ± (<> ( p , refl (F § b) (ap (F ± p) x)))) y)




Σ-fam-trp-ext : {A : setoid} -> (F : Fam A) ->  (G : Fam (Σ-std A F)) ->  
  (a b : || A ||) ->  (p : < A > a ~ b) -> (u v : || Σ-fam-std F G a ||) ->
  < Σ-fam-std F G a > u ~ v   -> 
  < Σ-fam-std F G b > Σ-fam-trp-op F G a b p u ~ Σ-fam-trp-op F G a b p v
Σ-fam-trp-ext {A} F G a b p ( x , y ) ( x' , y' ) (<> ( q , r )) 
        = <> ( extensionality (F ± p) _ _ q , 
            let eqr : < G § (a , x') > ap (fix1 {A} {F} G a ± q) y ~ y'
                eqr = r
                lm : < G § (b , ap (F ± p) x') > 
                      ap (G ± (<> (p , refl (F § b) (ap (F ± p) x'))))  (ap (fix1 {A} {F} G a ± q) y)
                      ~ ap (G ± (<> (p , refl (F § b) (ap (F ± p) x')))) y'
                lm = extensionality (G ± (<> (p , refl (F § b) (ap (F ± p) x')))) _ _ eqr
            in tra (Fam-fn2-eq G _ _ _ _ _) lm )



Σ-fam-trp : {A : setoid} -> (F : Fam A) ->  (G : Fam (Σ-std A F)) ->  
  (a b : || A ||) ->  (p : < A > a ~ b) ->
        || (Σ-fam-std F G a) => (Σ-fam-std F G b) ||
Σ-fam-trp {A} F G a b p = record { op = Σ-fam-trp-op {A} F G a b p 
                                 ; ext = Σ-fam-trp-ext {A} F G a b p }

Σ-fam-id-trp : {A : setoid} -> (F : Fam A) ->  (G : Fam (Σ-std A F)) ->  
      (a : || A ||) ->  (p : < A > a ~ a) -> (x : || Σ-fam-std F G a ||) ->
      < Σ-fam-std F G a > ap (Σ-fam-trp F G a a p) x ~ x
Σ-fam-id-trp {A} F G a p ( x , y ) = 
    <> ((Fam.id-trp F p x) ,  let main : < G § (a , x) >
                                     ap (G ± <> (((refl A a) , 
                                            (tra (Fam.id-trp F (refl A a) _) (Fam.id-trp F p x)))))
                                        (ap (G ± <> ((p , refl (F § a) (ap (F ± p) x)))) y)
                                      ~ y
                                  main = Fam-inv-eq+ (Σ-std A F) G _ (a , x) _ _ y
                              in main)



Σ-fam-ir-trp : {A : setoid} -> (F : Fam A) ->  (G : Fam (Σ-std A F)) ->  
      (a  b : || A ||) ->  (p q : < A > a ~ b) -> (x : || Σ-fam-std F G a ||) ->
      < Σ-fam-std F G b > ap (Σ-fam-trp F G a b p) x ~ ap (Σ-fam-trp F G a b q) x
Σ-fam-ir-trp {A} F G a b p q ( x , y ) = 
      <> ((Fam.ir-trp F p q x) , (sym (Fam.fn-trp G _ _ _ _)))

Σ-fam-fn-trp : {A : setoid} -> (F : Fam A) ->  (G : Fam (Σ-std A F)) ->  
      (a  b  c : || A ||) ->  (q : < A > b ~ c) ->  (p : < A > a ~ b) -> 
      (r : < A > a ~ c) -> (x : || Σ-fam-std F G a ||) ->
      < Σ-fam-std F G c > ap (Σ-fam-trp F G a c r) x ~ ap (Σ-fam-trp F G b c q) (ap (Σ-fam-trp F G a b p) x)
Σ-fam-fn-trp {A} F G a b c q p r ( x , y ) =
       <> ((Fam.fn-trp F q p r x) , Fam-fn2-eq {Σ-std A F} G _ _ _ _ _)



Σ-fam : {A : setoid} -> (F : Fam A) ->  (G : Fam (Σ-std A F)) ->  Fam A
Σ-fam {A} F G = record { std = λ x → Σ-fam-std F G x 
                        ; trp =  λ {a} {b}  p → Σ-fam-trp {A} F G a b p 
                        ; id-trp = λ {a} p x → Σ-fam-id-trp {A} F G a p x 
                        ; ir-trp = λ {a} {b} p q x →  Σ-fam-ir-trp {A} F G a b p q x 
                        ; fn-trp = λ {a} {b} {c} q p r x →  Σ-fam-fn-trp {A} F G a b c q p r x }


Ex : (A : setoid) -> (a b : || A ||) -> setoid
Ex A a b = triv-setoid (< A > a ~ b) 
               

Ex-fam-std : {A : setoid} -> (F : Fam A) -> (a b : || Π-std A F ||) -> (x : || A ||) -> setoid
Ex-fam-std {A} F a b x = Ex (F § x) (pj1 a x) (pj1 b x)



Ex-fam-trp-op : {A : setoid} -> (F : Fam A) ->  (a b : || Π-std A F ||)  ->  
  (x y : || A ||) ->  (p : < A > x ~ y) ->
        || (Ex-fam-std F a b) x ||  ->  || (Ex-fam-std F a b) y ||
Ex-fam-trp-op {A} F a b x y p q =
      let lm :  < F § x > (pj1 a x) ~ (pj1 b x)
          lm = q
          exa = pj2 a x y p
          exb = pj2 b x y p
          main : < F § y > (pj1 a y) ~ (pj1 b y)
          main = tra (sym exa) (tra (extensionality (F ± p) _ _ lm) exb)
      in main 

Ex-fam-trp : {A : setoid} -> (F : Fam A) ->  (a b : || Π-std A F ||)  ->  
  (x y : || A ||) ->  (p : < A > x ~ y) ->
        || ((Ex-fam-std F a b) x) => ((Ex-fam-std F a b) y) ||
Ex-fam-trp  {A} F a b x y p = record { op = Ex-fam-trp-op {A} F a b x y p 
                                     ; ext = λ u v q -> <> (>< q) }



Ex-fam : {A : setoid} -> (F : Fam A) -> (a b : || Π-std A F ||) -> Fam A
Ex-fam {A} F a b = record { std = Ex-fam-std {A} F a b
                          ; trp = λ {x} {y} p → Ex-fam-trp {A} F a b x y p 
                          ; id-trp = λ {x} p u → <> 0₁ 
                          ; ir-trp = λ {x} {y} p q u ->  <> 0₁ 
                          ; fn-trp = λ {x} {y} {z} q p r u ->  <> 0₁
                          } 

