-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt16 where

open import basic-types
open import basic-setoids       -- 525 lines
open import dependent-setoids   -- 559 lines
open import subsetoids          -- 341 lines
open import iterative-sets      -- 869 lines
open import iterative-sets-pt2  -- 326 lines
open import iterative-sets-pt3  -- 439 lines
open import iterative-sets-pt4
open import iterative-sets-pt5
open import iterative-sets-pt6
open import iterative-sets-pt8
open import V-model-pt0
open import V-model-pt1         -- 776 lines
open import V-model-pt2         -- 511 lines
open import V-model-pt3         -- 522 lines
open import V-model-pt4         -- 283 lines
open import V-model-pt5         -- 225 lines
open import V-model-pt6         -- 842 lines
open import V-model-pt7         --  66 lines
open import V-model-pt8         -- 134 lines
open import V-model-pt9         -- 441 lines
open import V-model-pt10  
open import V-model-pt13         
open import V-model-pt11
open import V-model-pt15


mk-rel : (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α)) ->
              || κ α || -> || κ α || -> Set
mk-rel ρ α r1 r2 x y = Σ (|| κ ρ ||) (\t ->  and (< κ α > x  ~  ap r1 t)  (< κ α > y  ~  ap r2 t))
              


q-set : (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α)) -> V
q-set ρ α r1 r2 =
      sup (# α)
          (\x -> sup (Σ (|| κ ρ ||) (\t ->  < κ α > x ~ ap r1 t  )) 
                     (\y -> α ‣ (ap r2 (pj1 y))))

q-set' : (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α)) -> V
q-set' ρ α r1 r2 =
      sup (# α)
          (\x -> sup (Σ (|| κ α ||) (\y -> mk-rel ρ α r1 r2 x y))
                     (\u ->  α ‣ (pj1 u)))


le-ge : (u v : V) ->   (u ≤ v) -> (v ≥ u)
le-ge u v p = λ y → pj1 (p y) , symV (pj2 (p y))


q-set-incl-lm : (ρ : V)  -> (α : V) 
                 -> (r1 r2 : setoidmap (κ ρ) (κ α)) 
                 -> (x y :  || κ α ||)   
                 -> ((z : || κ ρ ||) -> ( < κ α > x ~ ap r1 z ) ->
                        (Σ (|| κ ρ ||) (\k ->  
                                   and (< κ α > y ~ ap r1 k)
                                       (α ‣ (ap r2 z) ≐  α ‣ (ap r2 k)))))
                 -> (q-set ρ α r1 r2)  ‣ x ≤ (q-set ρ α r1 r2)  ‣ y
q-set-incl-lm  ρ α r1 r2 x y p1 (u1 , u2) = 
    let lm = p1 u1 u2
    in  ((pj1 lm) , (prj1 (pj2 lm))) , (prj2 (pj2 lm))

q-set-incl-lm2 : (ρ : V)  -> (α : V) 
                 -> (r1 r2 : setoidmap (κ ρ) (κ α)) 
                 -> (x y :  || κ α ||)   
                 -> (q-set ρ α r1 r2)  ‣ x ≤ (q-set ρ α r1 r2)  ‣ y
                 -> ((z : || κ ρ ||) -> ( < κ α > x ~ ap r1 z ) ->
                        (Σ (|| κ ρ ||) (\k ->  
                                   and (< κ α > y ~ ap r1 k)
                                       (α ‣ (ap r2 z) ≐  α ‣ (ap r2 k)))))
q-set-incl-lm2  ρ α r1 r2 x y p1 z q = 
    let lm = p1 (z , q)
        lm1 = pj1 lm
        lm2 = pj2 lm
        lm11 = pj1 lm1
        lm12 : < κ α > y ~ ap r1 (pj1 (pj1 (p1 (z , q))))
        lm12 =  pj2 lm1
    in  ((pj1 (pj1 (p1 (z , q))))) , (pair lm12 lm2)


q-map-op :  (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α))
                             -- -> Eqrel (|| κ α ||) (mk-rel ρ α r1 r2) 
                             -> || κ α || ->  || κ (q-set ρ α r1 r2) ||
q-map-op ρ α r1 r2 x  = x

q-map-op' :  (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α))
                             -- -> Eqrel (|| κ α ||) (mk-rel ρ α r1 r2) 
                             -> || κ α || ->  || κ (q-set' ρ α r1 r2) ||
q-map-op' ρ α r1 r2 x  = x

q-map-ext :  (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α))
                            -- -> (q : Eqrel (|| κ α ||) (mk-rel ρ α r1 r2))
                             -> (x : || κ α ||)
                             -> (y : || κ α ||)
                             -> < κ α > x ~ y
                             -> < κ (q-set ρ α r1 r2) > q-map-op ρ α r1 r2 x ~ q-map-op ρ α r1 r2 y
q-map-ext ρ α r1 r2 x y r = <> (eqV-unexpand' _ _ 
                                       (λ u → (pj1 u , tra (sym r) (pj2 u)) , refV _) 
                                       (λ v → ((pj1 v) , (tra r (pj2 v))) , (refV _)))

q-map-ext' :  (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α))
                            -- -> (q : Eqrel (|| κ α ||) (mk-rel ρ α r1 r2))
                             -> (x : || κ α ||)
                             -> (y : || κ α ||)
                             -> < κ α > x ~ y
                             -> < κ (q-set' ρ α r1 r2) > q-map-op' ρ α r1 r2 x ~ q-map-op' ρ α r1 r2 y
q-map-ext' ρ α r1 r2 x y r = <> (eqV-unexpand' _ _ 
                                (λ u →  let lm = pj2 u
                                        in ((pj1 u) , ((pj1 lm) , 
                                           (pair (tra (sym r) (prj1 (pj2 lm))) (prj2 (pj2 lm))))) , refV _)

                                (λ u →  let lm = pj2 u
                                        in ((pj1 u) , ((pj1 lm) , 
                                           (pair ((tra r (prj1 (pj2 lm)))) (prj2 (pj2 lm))))) , (refV _)))

q-map :  (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α))
                             -- -> Eqrel (|| κ α ||) (mk-rel ρ α r1 r2) 
                             -> setoidmap (κ α) (κ (q-set ρ α r1 r2))
q-map ρ α r1 r2 = record { op = q-map-op ρ α r1 r2 ;
                           ext = q-map-ext ρ α r1 r2 }

q-map' :  (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α))
                             -- -> Eqrel (|| κ α ||) (mk-rel ρ α r1 r2) 
                             -> setoidmap (κ α) (κ (q-set' ρ α r1 r2))
q-map' ρ α r1 r2 = record { op = q-map-op' ρ α r1 r2 ;
                            ext = q-map-ext' ρ α r1 r2 }

q-map-prop1 : (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α))
                             -> Eqrel (|| κ α ||) (mk-rel ρ α r1 r2) 
                             -> (x y :  || κ α ||)
                             -> mk-rel ρ α r1 r2 x y
                             ->  < κ (q-set ρ α r1 r2) > q-map-op ρ α r1 r2 x ~ q-map-op ρ α r1 r2 y
q-map-prop1 ρ α r1 r2 q x y (p , (pair p1 p2)) = 
   let -- p2 : < κ α > y ~ ap r2 p
       -- p1 : < κ α > x ~ ap r1 p
       -- p  : || κ ρ ||
       lm1 : (z : || κ ρ ||) →
              < κ α > x ~ ap r1 z →
              Σ || κ ρ ||
                 (λ k → and (< κ α > y ~ ap r1 k) (α ‣ ap r2 z ≐ α ‣ ap r2 k))
       lm1 = λ z q → {!!} , {!!}
       lm2 : (z : || κ ρ ||) →
               < κ α > y ~ ap r1 z →
               Σ || κ ρ ||
                  (λ k → and (< κ α > x ~ ap r1 k) (α ‣ ap r2 z ≐ α ‣ ap r2 k))
       lm2 = λ z q → p , pair p1 {!!}

       lm : (q-set ρ α r1 r2) ‣ x ≐  (q-set ρ α r1 r2) ‣ y
       lm = eqV-unexpand' ((q-set ρ α r1 r2) ‣ x) ((q-set ρ α r1 r2) ‣ y) (q-set-incl-lm ρ α r1 r2 x y lm1) 
                              (le-ge ((q-set ρ α r1 r2) ‣ y) ((q-set ρ α r1 r2) ‣ x) (q-set-incl-lm ρ α r1 r2 y x lm2))
       main : < κ (q-set ρ α r1 r2) > x ~ y
       main = <> lm
   in main

q-map-prop1' : (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α))
                             -> Eqrel (|| κ α ||) (mk-rel ρ α r1 r2) 
                             -> (x y :  || κ α ||)
                             -> mk-rel ρ α r1 r2 x y
                             ->  < κ (q-set' ρ α r1 r2) > q-map-op' ρ α r1 r2 x ~ q-map-op' ρ α r1 r2 y
q-map-prop1' ρ α r1 r2 r x y p = 
   let -- p2 : < κ α > y ~ ap r2 p
       -- p1 : < κ α > x ~ ap r1 p
       -- p  : || κ ρ ||
       rs = prj1 (prj2 r)
       q : mk-rel ρ α r1 r2 y x 
       q = rs x y p
       qt = pj1 q
       qt1 = prj1 (pj2 q)
       qt2 = prj2 (pj2 q)
    
       lm : (q-set' ρ α r1 r2) ‣ x ≐  (q-set' ρ α r1 r2) ‣ y
       lm = {!!}
           {--
             eqV-unexpand' ((q-set' ρ α r1 r2) ‣ x) ((q-set' ρ α r1 r2) ‣ y) 
                   (λ u → let pt = pj1 u
                              lm = pj2 u
                              lm1 = prj1 (pj2 lm)
                              lm2 = prj2 (pj2 lm)
                          in (x , ((pj1 (prj1 (prj2 r) x y p)) , (pair qt1 qt2))) ,
                             {!!}
                    ) 
                   {!!}
             --}
       main : < κ (q-set' ρ α r1 r2) > x ~ y
       main = <> lm
   in main

q-map-prop2 : (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α))
                             -> Eqrel (|| κ α ||) (mk-rel ρ α r1 r2) 
                             -> (x y :  || κ α ||)
                             -> < κ (q-set ρ α r1 r2) > q-map-op ρ α r1 r2 x ~ q-map-op ρ α r1 r2 y
                             -> mk-rel ρ α r1 r2 x y
q-map-prop2 ρ α r1 r2 q x y p = {!!}

q-map-prop2' : (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α))
                             -> Eqrel (|| κ α ||) (mk-rel ρ α r1 r2) 
                             -> (x y :  || κ α ||)
                             -> < κ (q-set' ρ α r1 r2) > q-map-op' ρ α r1 r2 x ~ q-map-op' ρ α r1 r2 y
                             -> mk-rel ρ α r1 r2 x y
q-map-prop2' ρ α r1 r2 q x y p = {!!} , (pair {!!} {!!})

un-q  : (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α))
                             -> (u :  || κ  (q-set ρ α r1 r2) ||)
                             -> || κ α ||
un-q ρ α r1 r2 u = u


q-map-prop3 : (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α))
                             -> (u :  || κ  (q-set ρ α r1 r2) ||)
                             ->  < κ (q-set ρ α r1 r2) > u ~ (q-map-op ρ α r1 r2 (un-q ρ α r1 r2 u))
q-map-prop3 ρ α r1 r2 u = refl (κ (q-set ρ α r1 r2)) u

q-lift-op :   (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α)) 
                -> (β : V) 
                -> (f : setoidmap (κ α) (κ β)) 
                -> || κ  (q-set ρ α r1 r2) ||
                -> || κ β ||
q-lift-op ρ α r1 r2 β f u = ap f (un-q ρ α r1 r2 u)

q-lift-ext :   (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α)) 
                -> Eqrel (|| κ α ||) (mk-rel ρ α r1 r2)
                -> (β : V) 
                -> (f : setoidmap (κ α) (κ β)) 
                -> ((x y :  || κ α ||) ->  (mk-rel ρ α r1 r2 x y) ->  < κ β > (ap f x) ~ (ap f y))
                -> (u v  : || κ (q-set ρ α r1 r2) ||)
                -> < κ (q-set ρ α r1 r2) > u ~ v
                -> < κ β > q-lift-op ρ α r1 r2 β f u ~ q-lift-op ρ α r1 r2 β f v
q-lift-ext ρ α r1 r2 q β f p u v t =
      let lm1 = prj1 q 
          lmt :  sup (Σ (|| κ ρ ||) (\t ->  < κ α > u ~ ap r1 t  )) 
                     (\y -> α ‣ (ap r2 (pj1 y)))
                     ≐
                 sup (Σ (|| κ ρ ||) (\t ->  < κ α > v ~ ap r1 t  )) 
                     (\y -> α ‣ (ap r2 (pj1 y)))
          lmt = >< t
          lm : mk-rel ρ α r1 r2 u v
          lm = {!!} , {!!}
      in  p u v lm

q-lift :  (ρ : V)  -> (α : V) -> (r1 r2 : setoidmap (κ ρ) (κ α)) 
                -> Eqrel (|| κ α ||) (mk-rel ρ α r1 r2)
                -> (β : V) 
                -> (f : setoidmap (κ α) (κ β)) 
                -> ((x y :  || κ α ||) ->  (mk-rel ρ α r1 r2 x y) ->  < κ β > (ap f x) ~ (ap f y))
                -> setoidmap (κ (q-set ρ α r1 r2)) (κ β)
q-lift ρ α r1 r2 q β f p = record { op = q-lift-op ρ α r1 r2 β f 
                                  ; ext = q-lift-ext ρ α r1 r2 q β f p }



-- quotient types

{--

-- following Maietti 2005, p 1101

isEq : {Γ : ctx}
     -> (A : ty Γ)
     -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
     -> Set
isEq = ?

Quot : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> isEq A R
   -> ty Γ
Quot {Γ} A R = {!!}

quot : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> isEq A R
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> raw Γ
quot {Γ} A R a p = {!!}  

Quot-i : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> isEq A R
   -> (a : raw Γ)
   -> (p : Γ ==> a :: A)
   -> Γ ==> quot {Γ} A R a p :: Quot {Γ} A R
Quot-i {Γ} A R a p = {!!}




omicron : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> (a a' : raw Γ)
   -> (p : Γ ==> a :: A)
   -> (p' : Γ ==> a' :: A)
   -> (r : raw Γ)
   -> (q : Γ ==> r ::  R [[ els2 p p' ]])
   -> raw Γ
omicron {Γ} A R a a' p p' r q = {!!}

Quot-ID-exd : {Γ : ctx}
   -> (A : ty Γ)
   -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
   -> (a a' : raw Γ)
   -> (p : Γ ==> a :: A)
   -> (p' : Γ ==> a' :: A)
   -> (r : raw Γ)
   -> (q : Γ ==> r :: R [[ els2 p p' ]])
   -> Γ ==> omicron {Γ} A R a a' p p' r q 
        :: ID (Quot {Γ} A R) (quot {Γ} A R a p) (Quot-i {Γ} A R a p)
                             (quot {Γ} A R a' p') (Quot-i {Γ} A R a' p')
Quot-ID-exd {Γ} A R a a' p p' r q = {!!}

quot-subst : {Γ : ctx}
       -> (A : ty Γ)
       -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
       -> subst (Γ ▷ A) (Γ ▷ Quot A R)
quot-subst {Γ} A R = {!!}


QE-op : {Γ : ctx}
       -> (A : ty Γ)
       -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
       -> (P : ty (Γ ▷ (Quot {Γ} A R)))
       -> (d : raw (Γ ▷ A))
       -> (p : Γ ▷ A ==> d :: P [[ quot-subst A R ]])
       -> (e : raw (Γ ▷ A ▷ (A [[ ↓ A ]]) ▷ R))
       -- need transport here
       -> (q : Γ ▷ A ▷ (A [[ ↓ A ]]) ▷ R ==> 
                 e :: ID (P [[ quot-subst A R ]] [[ ↓ (A [[ ↓ A ]]) ]] [[ ↓ R ]] )
                        ( d  [ ↓ (A [[ ↓ A ]]) ] [ ↓ R ] ) {!!} {!!} {!!})
       -> (c : raw Γ)
       -> (r : Γ ==> c :: (Quot {Γ} A R))
       -> raw Γ 
QE-op = {!!}

Quot-e  : {Γ : ctx}
       -> (A : ty Γ)
       -> (R : ty (Γ ▷ A ▷ (A [[ ↓ A ]])))
       -> (P : ty (Γ ▷ (Quot {Γ} A R)))
       -> (d : raw (Γ ▷ A))
       -> (p : Γ ▷ A ==> d :: P [[ {!!} ]])
       -> (e : raw (Γ ▷ A ▷ (A [[ ↓ A ]]) ▷ R))
       -> (q : Γ ▷ A ▷ (A [[ ↓ A ]]) ▷ R ==> e :: ID {!!} {!!} {!!} {!!} {!!})
       -> (c : raw Γ)
       -> (r : Γ ==> c :: (Quot {Γ} A R))
       -> Γ ==> QE-op {Γ} A R P d p e q c r :: P [[ els r ]]
Quot-e = {!!}

--}
