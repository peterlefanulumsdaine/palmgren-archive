
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.2

module dependent-setoids-pt2 where

open import basic-types
open import basic-setoids
open import dependent-setoids


lambda-op-op : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B))
  -> (f : || Π-std (Σ-std A B) C ||)
  -> ( x : || A ||) ->  ( y : || B § x ||) -> || (fix1 {A} {B} C x) § y ||
lambda-op-op  A B C f x y = pj1 f (x , y)


lambda-op-ext : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B))
  -> (f : || Π-std (Σ-std A B) C ||)
  -> ( x : || A ||)
  -> (z y : || B § x ||) (p : < B § x > z ~ y) →
      < fix1 {A} {B} C x § y > ap (fix1 {A} {B} C x ± p) (lambda-op-op A B C f x z) ~
      lambda-op-op A B C f x y
lambda-op-ext A B C f x z y p =
    let q : < Σ-std A B > (x , z) ~ (x , y)
        q = <> (refl A x , tra {B § x} (Fam.id-trp B (refl A x) z) p)
        exf = pj2 f (x , z) (x , y) q
        main :  < C § (x , y) > ap (fix1 {A} {B} C x ± p) (lambda-op-op A B C f x z)
                     ~ lambda-op-op A B C f x y
        main = exf
    in main

lambda-op : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B))
  -> (f : || Π-std (Σ-std A B) C ||) -> ( x : || A ||) -> || (Π-fam B C) § x ||
lambda-op A B C f x = (lambda-op-op  A B C f x) ,
                      (λ u v p → pj2 f (x , u) (x , v) (<> (refl A x , tra {B § x} (Fam.id-trp B (refl A x) u) p)))

lambda : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B))
  -> (f : || Π-std (Σ-std A B) C ||) -> || Π-std A (Π-fam B C) ||
lambda A B C f = (lambda-op A B C f) ,
    (λ x y p -> <> (\ u → pj2 f ( x , ap (B ± sym {A} p) u) (y , u) (<> ( p , Fam-inv-eq A B x y p u ))))


-- naming ?



curry : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B))
  -> || Π-std (Σ-std A B) C  => Π-std A (Π-fam B C) ||
curry A B C = record { op = lambda A B C
                      ; ext =  λ f g p ->
                                 <> (λ x → <> (λ y →
                                        <> (>< (>< p  (x , y)))))
                       }



uncurry-op-op : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B))
  -> || Π-std A (Π-fam B C) ||  ->  (u : || Σ-std A B ||) -> || C § u ||
uncurry-op-op A B C f ( x , y) =  pj1 (pj1 f x) y



uncurry-op-ext : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B))
  -> (f : || Π-std A (Π-fam B C) ||) ->
 (x y : || Σ-std A B ||) (p : < Σ-std A B > x ~ y) ->
      < C § y > ap (C ± p) (uncurry-op-op A B C f x) ~
      uncurry-op-op A B C f y
uncurry-op-ext A B C f (u , v) (u' , v') p =
        let exf : < Π-fam B C § u' > ap (Π-fam B C ± pj1 (>< p)) (pj1 f u) ~ pj1 f u'
            exf  = pj2 f u u' (pj1 (>< p))
            exf1 = (>< exf) v'
            exf2 : < C § (u' , v') > Π-fam-trp-op-op {A} {B} C (pj1 (>< p)) (pj1 f u) v' ~
                                       pj1 (pj1 f u') v'
            exf2 = <> (>< exf1)
            eq   : < B § u' > ap (B ± pj1 (>< p)) v ~ v'
            eq = pj2 (>< p)
            eq2 : < B § u > v ~ (ap (B ±  (sym (pj1 (>< p)))) v')
            eq2 = Fam-flip A B _ _ _ _ _ eq
            exf3 : < C § ( u , ap (B ± sym (pj1 (>< p))) v') >
                     ap (fix1 {A} {B} C u ± Fam-flip A B u u' (pj1 (>< p)) v v' (pj2 (>< p)))
                             (pj1 (pj1 f u) v)
                     ~ pj1 (pj1 f u) (ap (B ± sym (pj1 (>< p))) v')
            exf3 = pj2 (pj1 f u) v (ap (B ± (sym (pj1 (>< p)))) v') eq2
            exf4 :  < C § (u' , v') >
                      ap (C ± (<> ((pj1 (>< p)) , Fam-inv-eq A B u u' (pj1 (>< p)) v')))
                         (ap (fix1 {A} {B} C u ± Fam-flip A B u u' (pj1 (>< p)) v v' (pj2 (>< p)))
                             (pj1 (pj1 f u) v))
                     ~   ap (C ± (<> ((pj1 (>< p)) , Fam-inv-eq A B u u' (pj1 (>< p)) v')))
                             (pj1 (pj1 f u) (ap (B ± sym (pj1 (>< p))) v'))
            exf4 = extensionality (C ± (<> ((pj1 (>< p)) , Fam-inv-eq A B u u' (pj1 (>< p)) v'))) _ _ exf3
            lm :  < C § (u' , v') >
                    ap (C ± p) (pj1 (pj1 f u) v) ~
                    ap (C ± (<> ((pj1 (>< p)) , Fam-inv-eq A B u u' (pj1 (>< p)) v'))) (pj1 (pj1 f u) (ap (B ±  (sym                          (pj1 (>< p)))) v'))
            lm = tra (Fam.fn-trp C _ _ _ _) exf4
            main :  < C § (u' , v') > ap (C ± p) (pj1 (pj1 f u) v) ~
                                      pj1 (pj1 f u') v'
            main = tra lm exf2
        in  main



uncurry-op : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B))
  -> || Π-std A (Π-fam B C) ||  ->  || Π-std (Σ-std A B) C ||
uncurry-op A B C f = (uncurry-op-op A B C f) ,
                      (uncurry-op-ext A B C f)

uncurry-ext : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B))
  -> (f g : || Π-std A (Π-fam B C) ||)
  -> (< Π-std A (Π-fam B C) > f ~ g)
  -> (u : || Σ-std A B ||)
  -> < C § u > uncurry-op-op A B C f u ~ uncurry-op-op A B C g u
uncurry-ext A B C f g p (x , y) =
   let eq1 = >< (>< p x) y
       main :  < C § (x , y) > pj1 (pj1 f x) y ~ pj1 (pj1 g x) y
       main = <> (>< eq1)
   in main



uncurry : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B))
  -> || Π-std A (Π-fam B C)  =>  Π-std (Σ-std A B) C ||
uncurry A B C = record { op = uncurry-op A B C
                       ; ext = λ f g p → <> (uncurry-ext A B C f g p )
                        }



-- mutual inverses

curry-uncurry-lm : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B)) ->
   (f : || Π-std (Σ-std A B) C ||) -> (u : || Σ-std A B ||) ->
   < C § u > uncurry-op-op A B C (ap (curry A B C) f) u ~
      pj1 f u
curry-uncurry-lm A B C f (x , y) = refl (C § (x , y)) _



curry-uncurry : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B)) ->
    <  (Π-std (Σ-std A B) C)  =>  (Π-std (Σ-std A B) C) >
    (uncurry A B C)  ° (curry A B C)  ~ idmap {Π-std (Σ-std A B) C}
curry-uncurry A B C = <> (λ f → <> (λ u → curry-uncurry-lm A B C f u))

uncurry-curry : (A : setoid) -> (B : Fam A) -> (C : Fam (Σ-std A B)) ->
    <  (Π-std A (Π-fam B C))  =>  (Π-std A (Π-fam B C)) >
    (curry A B C)  ° (uncurry A B C)  ~ idmap {Π-std A (Π-fam B C)}
uncurry-curry A B C = <> (λ f → <> (λ x → <> (λ y →  refl (C § (x , y)) _)))


-- Ex-reflection

Ex-reflection : (A : setoid) -> (F : Fam A) -> (a b : || Π-std A F ||) ->
 (r : || Π-std A (Ex-fam F a b) ||) -> <  Π-std A F > a ~ b
Ex-reflection A F a b r = <> (λ x → pj1 r x)

Ex-intro-op :  (A : setoid) -> (F : Fam A) -> (a : || Π-std A F ||) ->
 (x :  || A ||) -> || (Ex-fam F a a) § x ||
Ex-intro-op A F a x = refl (F § x) (pj1 a x)

Ex-intro :  (A : setoid) -> (F : Fam A) -> (a : || Π-std A F ||) ->
 || Π-std A (Ex-fam F a a) ||
Ex-intro A F a =   (Ex-intro-op A F a) ,  (λ x y p → <> 0₁ )

