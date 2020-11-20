
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- {-# OPTIONS --no-eta-equality #-}

-- Agda version 2.5.2

module iterative-sets where

open import basic-types
open import basic-setoids
open import dependent-setoids
open import subsetoids

-- Aczel's V


data V  : Set1 where
   sup : (A : Set) -> (f : A -> V) -> V

-- index and branching components

iV :  V -> Set
iV (sup A f) = A

bV : (t : V) -> (iV t) ->  V
bV (sup A f) = f

-- notations for index and branching components

# : V -> Set
# u = iV u

infixl 10 _‣_ -- enter as \bu4 

_‣_ : (t : V) -> (iV t) ->  V
_‣_ u a = bV u a

--   u ‣ a1 ‣ ... ‣ an   gives set hereditary in u along the path a1, ..., an.

-- equality of set-trees is defined by bismulation

infix 2 _≐_   --  \doteq

eqV : V -> V -> Set
eqV (sup A f) (sup B g) = and ((x : A) -> Σ B (\y -> eqV (f x) (g y))) 
                              ((y : B) -> Σ A (\x -> eqV (f x) (g y))) 

_≐_ : V -> V -> Set
x ≐ y = eqV x y

-- useful expansion/unexpansion of the definition

eqV-expand : (u v : V) -> (u ≐ v) -> 
          and ((x : # u) -> Σ (# v) (\y ->  u ‣ x ≐ v ‣ y)) 
              ((y : # v) -> Σ (# u) (\x ->  u ‣ x ≐ v ‣ y)) 
eqV-expand (sup A f) (sup B g) p = p


eqV-unexpand : (u v : V) -> 
               ((x : # u) -> Σ (# v) (\y ->  u ‣ x ≐ v ‣ y)) ->
               ((y : # v) -> Σ (# u) (\x ->  u ‣ x ≐ v ‣ y)) -> 
               (u ≐ v)  
eqV-unexpand (sup A f) (sup B g) p q = pair p q

-- version of inclusion statement

infix 2 _≤_ -- \le
_≤_ : V -> V -> Set
u ≤ v = ((x : # u) -> Σ (# v) (\y ->  u ‣ x ≐ v ‣ y)) 

infix 2 _≥_ -- \ge
_≥_ : V -> V -> Set
u ≥ v = ((y : # v) -> Σ (# u) (\x ->  u ‣ x ≐ v ‣ y)) 

eqV-expand' : (u v : V) -> (u ≐ v) ->  and (u ≤ v) (u ≥ v)
eqV-expand' u v p = eqV-expand u v p           

eqV-unexpand' : (u v : V) ->   (u ≤ v) -> (u ≥ v) ->  (u ≐ v) 
eqV-unexpand' u v p q = eqV-unexpand u v p q


easy-eqV :  (A : Set) -> (f g : A -> V) 
             -> ((x : A) -> f x ≐ g x)
              -> (sup A f) ≐ (sup A g)
easy-eqV A f g p = pair (λ x → x , p x) (λ y →  y , p y)
         

eqV-right : {u v : V} -> (u ≐ v) -> # u ->  # v
eqV-right {u} {v} p x = pj1 (prj1 (eqV-expand u v p) x)

e+ : {u v : V} -> (u ≐ v) -> # u ->  # v
e+  {u} {v} p x = eqV-right {u} {v} p x

e+prop : {u v : V} -> (p : u ≐ v)
      -> (x : # u) -> u ‣ x ≐ v ‣ (e+ p x)
e+prop {u} {v} p x = pj2 (prj1 (eqV-expand u v p) x)

eqV-left : {u v : V} -> (u ≐ v) -> # v ->  # u
eqV-left {u} {v} p y = pj1 (prj2 (eqV-expand u v p) y)

e- : {u v : V} -> (u ≐ v) -> # v ->  # u
e-  {u} {v} p y = eqV-left {u} {v} p y

e-prop : {u v : V} -> (p : u ≐ v)
      -> (y : # v) -> u ‣ (e- p y) ≐ v ‣ y
e-prop {u} {v} p y = pj2 (prj2 (eqV-expand u v p) y)

-- basic properties of set equality

refl-eqV : (u : V) -> u ≐ u
refl-eqV (sup A f) = pair (λ x → (x , refl-eqV (f x)))
                          (λ y → (y , refl-eqV (f y)))
refV : (u : V) -> u ≐ u
refV u = refl-eqV u

sym-eqV : (u v : V) -> u ≐ v -> v ≐ u
sym-eqV (sup A f) (sup B g) p = pair (λ x → pj1 (prj2 p x) , sym-eqV (f (pj1 (prj2 p x))) (g x) (pj2 (prj2 p x))) 
                                     (λ y → pj1 (prj1 p y) , sym-eqV (f y) (g (pj1 (prj1 p y))) (pj2 (prj1 p y)))

symV : {u v : V} -> u ≐ v -> v ≐ u
symV {u} {v} p = sym-eqV u v p

tra-eqV : (u v z : V) -> u ≐ v -> v ≐ z -> u ≐ z
tra-eqV (sup A f) (sup B g) (sup C h) p q = pair (λ x → (pj1 (prj1 q (pj1 (prj1 p x)))) ,
                                                        (let lm1 : eqV (f x) (g (pj1 (prj1 p x)))
                                                             lm1 = pj2 (prj1 p x)
                                                             lm2 : eqV (g (pj1 (prj1 p x))) (h (pj1 (prj1 q (pj1 (prj1 p x)))))
                                                             lm2 = pj2 (prj1 q (pj1 (prj1 p x)))
                                                             main : eqV (f x) (h (pj1 (prj1 q (pj1 (prj1 p x)))))
                                                             main = tra-eqV _ _ _ lm1 lm2
                                                         in main)) 
                                                 (λ y → (pj1 (prj2 p (pj1 (prj2 q y)))) , 
                                                        (let lm1 : eqV (f (pj1 (prj2 p (pj1 (prj2 q y))))) (g (pj1 (prj2 q y)))
                                                             lm1 = pj2 (prj2 p (pj1 (prj2 q y)))
                                                             lm2 : eqV (g (pj1 (prj2 q y))) (h y)
                                                             lm2 = pj2 (prj2 q y)
                                                             main : eqV (f (pj1 (prj2 p (pj1 (prj2 q y))))) (h y)
                                                             main = tra-eqV _ _ _ lm1 lm2
                                                         in main))

traV : {u v z : V} -> u ≐ v -> v ≐ z -> u ≐ z
traV {u} {v} {z} p q = tra-eqV u v z p q


sup-expand : (u : V) -> u ≐ sup (# u) (bV u)
sup-expand  (sup A f) = refV (sup A f)


eqV-left-right-prop : {u v : V} -> (p : u ≐ v)
      -> (y : # v) -> u ‣ (e- p y) ≐  u ‣ (e+ (symV p) y)
eqV-left-right-prop {u} {v} p y = traV (e-prop p y) (e+prop (symV p) y)



e+ext : {u v : V} -> (p : u ≐ v)
      -> (x y : # u) -> u ‣ x ≐ u ‣ y ->  v ‣ (e+ p x) ≐ v ‣ (e+ p y)
e+ext {u} {v} p x y q = traV (symV (e+prop p x)) (traV q (e+prop p y)) 

e+fun : {u v z : V} -> (p : u ≐ v) -> (q : v ≐ z) ->  (r : u ≐ z)
      -> (x : # u)  ->  z ‣ (e+ q (e+ p x)) ≐ z ‣ (e+ r x)
e+fun {u} {v} {z} p q r x = traV (symV (traV (e+prop p x) (e+prop q (e+ p x))))  (e+prop r x)

-- membership relation defined in terms of equality

infix 2 _∈_   -- \in


memV : (u v : V) -> Set
memV u v =  Σ (# v) (\y -> u ≐ v ‣ y)

_∈_ : V -> V -> Set
u ∈ v = memV u v

memV-expand : (u v : V) -> (u ∈ v) -> Σ (# v) (\y -> u ≐ v ‣ y)
memV-expand u (sup B g) p =  p

triv-memV : (A : Set) -> (f : A -> V) -> (x : A)
          ->  f x ∈ sup A f
triv-memV A f x = x , refV (f x)

memV-left-ext : (u v x : V) -> u ≐ v -> v ∈ x -> u ∈ x
memV-left-ext u v (sup A f) p q = (pj1 q) , (traV p (pj2 q))

memV-right-ext : (u x y : V)  -> u ∈ x -> x ≐ y -> u ∈ y
memV-right-ext u (sup A f) (sup B g) p q = 
     let p2 : u ≐ (f (pj1 p))
         p2 = pj2 p 
         q1 = prj1 q (pj1 p)
     in (pj1 q1) , (traV p2 (pj2 q1))

memV-right-ext-lm : (u x y : V)  
     -> (p : u ∈ x) -> (q : x ≐ y) -> u ≐ y ‣ (pj1 (memV-right-ext u x y p q))
memV-right-ext-lm u x y p q =  pj2 (memV-right-ext u x y p q)

-- seems useful :


memV-right-ext-lm2 : (u x y : V)  
      -> (p : u ∈ x) -> (q : x ≐ y) -> u ≐ y ‣ (e+ q (pj1 p))
memV-right-ext-lm2 u x y p q = traV (pj2 p) (e+prop q (pj1 p)) 


memV-right-ext2 : (u x y : V)  -> u ∈ x -> x ≐ y -> u ∈ y
memV-right-ext2 u x y p q = (e+ q (pj1 p)) , memV-right-ext-lm2 u x y p q

-- another version of inclusion

infix 2 _⊆_  -- \subseteq

_⊆_ : (u v : V) -> Set1
_⊆_ u v = (x : V) -> x ∈ u -> x ∈ v

extensional-eqV : (u v : V) -> u ⊆ v -> v ⊆ u -> u ≐ v
extensional-eqV (sup A f) (sup B g) p q 
    = pair (λ x → let lm = p (f x) (triv-memV A f x)
                      main :  Σ B (λ y → f x ≐ g y)
                      main = lm
                  in main) 
           (λ y → let lm :  Σ A (λ z → (g y) ≐ (f z))
                      lm = q (g y) (triv-memV B g y)
                      main : Σ A (λ x → f x ≐ g y)
                      main = (pj1 lm) , (symV (pj2 lm))
                  in main)

trivial-incl : (u v : V) -> u ≐ v  -> u ⊆ v 
trivial-incl u v p t q = memV-right-ext _ _ _ q p

half-eqV : V -> V -> Set
half-eqV (sup A f) (sup B g) = (x : A) -> Σ B (\y -> eqV (f x) (g y)) 

-- same as (sup A f) ≤  (sup B g)

half-eqV-to-inclusion : (u v : V) -> half-eqV u v -> u ⊆ v
half-eqV-to-inclusion (sup A f) (sup B g) p = λ x q → pj1 (p (pj1 q)) , traV (pj2 q) (pj2 (p (pj1 q)))
                            
≤-to-inclusion : (u v : V) -> u ≤ v -> u ⊆ v
≤-to-inclusion u v p =  λ x q → pj1 (p (pj1 q)) , traV (pj2 q) (pj2 (p (pj1 q)))

inclusion-to-≤ : (u v : V) -> u ⊆ v -> u ≤ v
inclusion-to-≤ u v p = λ x → p (u ‣ x) (x , (refV (u ‣ x)))



-- e+ : {u v : V} -> (u ≐ v) -> # u ->  # v
-- unordered and ordered pairs

unord-branch :  V -> V -> Bool -> V
unord-branch x y (inr _) = y
unord-branch x y (inl _)  = x

unord : V -> V -> V
unord x y = sup Bool (unord-branch x y)

unord-propR : (x y : V) -> 
       (z : V) -> z ∈ (unord x y) -> (or (z ≐ x) (z ≐ y))
unord-propR x y z (inl u , p) = inl p
unord-propR x y z (inr u , p) = inr p  

unord-propL : (x y : V) -> 
       (z : V) -> (or (z ≐ x) (z ≐ y)) -> z ∈ (unord x y)
unord-propL x y z p = orEweak {z ≐ x} {z ≐ y} {z ∈ (unord x y)} 
                        (\q -> (inl  0₁ ) , q) 
                        (\r -> (inr  0₁ ) , r) p

unord-propL2 :  (x y : V) -> x ∈ (unord x y)
unord-propL2 x y = unord-propL x y x (inl (refV x))

unord-propL3 :  (x y : V) -> y ∈ (unord x y)
unord-propL3 x y = unord-propL x y y (inr (refV y))

unord-prop : (x y : V) -> 
       (z : V) -> (iff (z ∈ (unord x y)) (or (z ≐ x) (z ≐ y)))
unord-prop x y z = pair (unord-propR x y z) (unord-propL x y z)

unord-ext-lm : (x y z u : V) -> x ≐ z -> y ≐ u -> (unord x y) ⊆ (unord z u)
unord-ext-lm x y z u p q t (inl m , p') = (inl  0₁) , (traV p' p) 
unord-ext-lm x y z u p q t (inr m , q') = inr 0₁ , traV q' q 


unord-ext : {x y z u : V} -> x ≐ z -> y ≐ u -> (unord x y) ≐ (unord z u)
unord-ext {x} {y} {z} {u} p q = extensional-eqV (unord x y) (unord z u) 
                                        (unord-ext-lm x y z u p q)
                                        (unord-ext-lm z u x y (symV p) (symV q)) 

unord-inv-lm :  (x y u : V) -> (unord x y ≐ unord x u) -> y ≐ u
unord-inv-lm x y u p = 
   let lm1 : y ∈ (unord x u)
       lm1 = memV-right-ext _ _ _ (unord-propL3 _ _) p
       lm1b : or (y ≐ x) (y ≐ u)
       lm1b = unord-propR _ _ _ lm1
       lm2 : u ∈ (unord x y)
       lm2 = memV-right-ext _ _ _ (unord-propL3 _ _) (symV p)
       lm2b : or (u ≐ x) (u ≐ y)
       lm2b = unord-propR _ _ _ lm2
   in orEweak {y ≐ x} {y ≐ u} {y ≐ u} 
              (λ q → orEweak {u ≐ x} {u ≐ y} {y ≐ u} 
                             (λ r → traV q (symV r)) 
                             (λ r → symV r) 
                             lm2b) 
              (λ q → q) 
              lm1b



record is-unord1 (u : V) : Set1 where
  field
    cp1 : V
    cp2 : V
    eqp : u ≐ unord cp1 cp2

-- small version

is-unord : (u : V) -> Set
is-unord u =   Σ (# u) (\a  -> (Σ (# u) \b -> u ≐ unord (u ‣ a) (u ‣ b)))

is-unord-ext : (u v : V) -> u ≐ v -> is-unord u -> is-unord v
is-unord-ext (sup A f) (sup B g) p q = 
     let lm : Σ A (\a  -> (Σ A \b -> (sup A f) ≐ unord (f a) (f b)))
         lm = q
         a1 = pj1 lm
         a2 = pj1 (pj2 lm)
         lmeq : sup A f ≐ unord (f a1) (f a2)
         lmeq = pj2 (pj2 lm)
         b1 = pj1 (prj1 p a1)
         eq1 : eqV (f a1) (g b1)
         eq1 =  pj2 (prj1 p a1)
         b2 = pj1 (prj1 p a2)
         eq2 : eqV (f a2) (g b2)
         eq2 =  pj2 (prj1 p a2)
         main : Σ B (\a  -> (Σ B \b -> (sup B g) ≐ unord (g a) (g b)))
         main = b1 , (b2 , (traV (symV p)
           (traV lmeq (unord-ext eq1 eq2))))
     in main



is-unord1-0 : (u : V) -> (is-unord1 u) -> (is-unord u)
is-unord1-0 u p = 
     let lm :  u ≐ unord (is-unord1.cp1 p)  (is-unord1.cp2 p)
         lm =  is-unord1.eqp p
         lm2 : is-unord (unord (is-unord1.cp1 p)  (is-unord1.cp2 p))
         lm2 = (inl 0₁) , ((inr 0₁) , (refV _))         
     in is-unord-ext _ _ (symV lm) lm2

is-unord0-1 : (u : V) -> (is-unord u) -> (is-unord1 u)
is-unord0-1 (sup A f) p = record { cp1 = f (pj1 p) 
                                 ; cp2 = f (pj1 (pj2 p)) 
                                 ; eqp = pj2 (pj2 p) }


-- the (ordered) pairing operation

pairV : V -> V -> V
pairV x y = unord (unord x x) (unord x y)


<_,_> : V -> V -> V
<_,_> x y = pairV x y

pairV-ext : {x y z u : V} -> x ≐ z -> y ≐ u -> < x , y > ≐ < z , u >
pairV-ext {x} {y} {z} {u} p q = unord-ext (unord-ext p p) (unord-ext p q)


pairV-lm1 : (x y : V) -> x ∈ (unord y y)  ->  x ≐ y
pairV-lm1 x y  (inl 0₁ , p ) = p
pairV-lm1 x y  (inr 0₁ , q ) = q

pairV-lm2 : (x y z : V) -> (unord x x) ≐ (unord y z) -> (and (x ≐ y) (x ≐ z))
pairV-lm2 x y z p = pair (symV (pairV-lm1 y x 
                                              (let lm : y ∈ unord y z
                                                   lm = unord-propL2 _ _
                                               in memV-right-ext _ _ _ lm (symV p))))
                         (symV (pairV-lm1 z x 
                                              (let lm : z ∈ unord y z
                                                   lm = unord-propL3 _ _
                                               in memV-right-ext _ _ _ lm (symV p))))
     

pairV-inv-1 : {x y z u : V} -> < x , y > ≐ < z , u > ->  and (x ≐ z) (y ≐ u)
pairV-inv-1 {x} {y} {z} {u} p =
                      let lm :  unord (unord x x) (unord x y) ≐ unord (unord z z) (unord z u)
                          lm = p
                          lm2 : (unord x x) ∈ unord (unord z z) (unord z u)
                          lm2 =  memV-right-ext _ _ _ (unord-propL2 _ _) lm
                          lm3 : or ((unord x x) ≐ (unord z z)) ((unord x x) ≐ (unord z u)) 
                          lm3 = unord-propR _ _ _ lm2
                          main1 : x ≐ z
                          main1 = orEweak (λ q → prj1 (pairV-lm2 _ _ _ q))
                                          (λ q → prj1 (pairV-lm2 _ _ _ q)) lm3
                          lm4 :  unord (unord x x) (unord x y) ≐ unord (unord x x) (unord x u)
                          lm4 = traV lm (unord-ext 
                                    (symV (unord-ext main1 main1)) 
                                    (symV (unord-ext main1 (refV _))))
                          lm5 :  (unord x y) ≐  (unord x u)
                          lm5 = unord-inv-lm _ _ _ lm4
                          main2 : y ≐ u
                          main2 = unord-inv-lm _ _ _ lm5
                      in pair main1 main2


-- union of a set of sets

unionV : V -> V
unionV v = sup (Σ (# v) (\x -> # (v ‣ x))) (\u -> v ‣ (pj1 u) ‣ (pj2 u))



unionV-lm1 : (x y : V) -> x ∈ unionV y -> Σ10 V (\u -> and (x ∈ u) (u ∈ y))
unionV-lm1 x y p = 
  let lm2 :  Σ (# y) (λ v → # (y ‣ v))
      lm2 = pj1 p
      lm3 : x  ≐ ((y ‣ (pj1 (pj1 p))) ‣ (pj2 (pj1 p)))
      lm3 = pj2 p
      main :  Σ10 V (\u -> and (x ∈ u) (u ∈ y))
      main = (bV y (pj1 (pj1 p))) , pair ((pj2 (pj1 p)) , lm3) ( (pj1 (pj1 p)) , (refV _))
  in main

unionV-lm2 : (x y : V) ->  Σ10 V (\u -> and (x ∈ u) (u ∈ y)) -> x ∈ unionV y
unionV-lm2 x y ( u , pair p1 p2) =
  let lm11 = pj1 p1
      lm21 = pj2 p1
      lm12 = pj1 p2
      lm22 = pj2 p2
      lm3 = eqV-expand _ _ lm22
  in (lm12 , pj1 (prj1 lm3 lm11)) , traV lm21 (pj2 (prj1 lm3 lm11))

-- to do:
-- pairV-union-lm :  (x y : V) -> unionV (pairV x y) ≐ unord x y
-- pairV-union-lm  x y = ?

record is-pairV1 (u : V) : Set1 where
  field
    cp1 : V
    cp2 : V
    eqp :  u ≐ < cp1 , cp2 >

is-pairV1-ext : (u v : V) -> u ≐ v -> is-pairV1 u -> is-pairV1 v
is-pairV1-ext u v p q = record { cp1 = is-pairV1.cp1 q 
                               ; cp2 = is-pairV1.cp2 q 
                               ; eqp = traV (symV p) (is-pairV1.eqp q) 
                               }

-- small version finding the components inside the tree for u

is-pairV : (u : V) -> Set
is-pairV u =   Σ (# u) (\a  -> (Σ (# u) \b ->  
                Σ (# (u ‣ a)) (\c ->  Σ (# (u ‣ b)) (\d ->
                       u ≐ < u ‣ a ‣ c , u ‣ b ‣ d >))))

-- 

is-pairV-ext : (u v : V) -> u ≐ v -> is-pairV u -> is-pairV v
is-pairV-ext (sup A f) (sup B g) p q = 
    let lm : Σ A (\a  -> (Σ A \b ->  
                Σ (# (f a)) (\c ->  Σ (# (f b)) (\d ->
                       (sup A f) ≐ < (f a) ‣ c , (f b) ‣ d >))))
        lm = q
        a1  : A
        a1 = pj1 lm
        a2  : A
        a2 = pj1 (pj2 lm)
        eq1 :  Σ (# (f a1)) (\c ->  Σ (# (f a2)) (\d ->
                       (sup A f) ≐ < (f a1) ‣ c , (f a2) ‣ d >))
        eq1 = pj2 (pj2 lm)
        c1  : # (f a1)
        c1 = pj1 eq1
        c2  : # (f a2)
        c2 = pj1 (pj2 eq1)
        eq2 : (sup A f) ≐ < (f a1) ‣ c1 , (f a2) ‣ c2 >
        eq2 = pj2 (pj2 eq1)
        eq3 : (sup B g) ≐ < (f a1) ‣ c1 , (f a2) ‣ c2 >
        eq3 = traV (symV p) eq2
        b1  : B
        b1 = pj1 (prj1 p a1)
        b2  : B
        b2 = pj1 (prj1 p a2)
        eq4 : (f a1) ≐ (g b1)
        eq4 = pj2 (prj1 p a1)
        eq5 : (f a2) ≐ (g b2)
        eq5 = pj2 (prj1 p a2)
        ts  : and
           ((x : # (f a1)) →
            Σ (# (g b1))
              (λ y → ((f a1) ‣ x)  ≐ ((g b1) ‣ y)))
           ((y : # (g b1)) →
           Σ (# (f a1))
              (λ x → ((f a1) ‣ x)  ≐ ((g b1) ‣ y)))     
        ts =  eqV-expand _ _ eq4
        ts2 = eqV-expand _ _ eq5
        d1 : # (g b1)
        d1 = pj1 (prj1 ts c1)
        d2 : # (g b2)
        d2 = pj1 (prj1 ts2 c2)

     
        eq6 : (f a1) ‣ c1 ≐ (g b1) ‣ d1
        eq6 = pj2 (prj1 ts c1)
        eq7 : (f a2) ‣ c2 ≐ (g b2) ‣ d2
        eq7 = pj2 (prj1 ts2 c2)

        lm2- :  < ((f a1) ‣ c1) , ((f a2) ‣ c2) >  
                ≐ < ((g (pj1 (prj1 p (pj1 q)))) ‣ d1) ,  ((g (pj1 (prj1 p (pj1 (pj2 q))))) ‣ d2) >
        lm2- = pairV-ext eq6 eq7
        lm2 : sup B g ≐ < ((g (pj1 (prj1 p (pj1 q)))) ‣ d1) ,
                              ((g (pj1 (prj1 p (pj1 (pj2 q))))) ‣ d2) >
        lm2 = traV eq3 lm2-
        main :  Σ (# (g b1))
                  (λ c →
                  Σ (# (g b2))
                    (λ d →  sup B g ≐
                         < (g b1) ‣ c , (g b2) ‣ d >))
        main = d1 , (d2 , lm2)

    in b1 , (b2 , main) 

is-pairV1-0 : (u : V) -> is-pairV1 u -> is-pairV u
is-pairV1-0 u p = 
     let lm :  u ≐ < (is-pairV1.cp1 p) , (is-pairV1.cp2 p) >
         lm =  is-pairV1.eqp p
         lm2 : is-pairV (<  (is-pairV1.cp1 p) , (is-pairV1.cp2 p) > )
         lm2 = (inl 0₁) , ((inr 0₁) , ((inl 0₁) , ((inr 0₁) , (refV _))))        
     in is-pairV-ext _ _ (symV lm) lm2


is-set-of-pairs1 : (u : V) -> Set1
is-set-of-pairs1 u = (z : V) -> z ∈ u -> is-pairV1 z

is-set-of-pairs : (u : V) -> Set
is-set-of-pairs u = (z : # u) -> u ‣ z ∈ u -> is-pairV (u ‣ z)



is-functional : (u : V) -> Set1
is-functional u = (x y z : V) -> < x , y > ∈ u -> < x , z > ∈ u -> y ≐ z

is-total-on : (u a : V) -> Set1
is-total-on u a = (x  : V) -> x ∈ a -> Σ10 V (\y ->  (< x , y > ∈ u)) 

-- Canonical setoids from V
-- construct the canonical setoid  κ u  corresponding to a set u in V

can-std : V -> setoid
can-std a = record { object = # a  
                   ; _∼_ = λ x y → a ‣ x ≐ a ‣ y
                   ; eqrel = pair (λ x → refV (a ‣ x)) 
                                  (pair (λ x y p → symV p) 
                                        (λ x y z p q → traV p q)) }

κ : V -> setoid  -- \kappa for canonical setoid
κ a = can-std a

κ-trp-op : {a b : V} -> (p : a ≐ b) -> || κ a ||  ->  || κ b ||
κ-trp-op {a} {b} p x = e+ p x

κ-trp-ext : {a b : V} -> (p : a ≐ b) ->  (x y : || κ a ||)
      ->  < κ a > x ~ y ->  < κ b > κ-trp-op p x ~ κ-trp-op p y
κ-trp-ext {a} {b} p x y q = <> (traV (traV (symV (e+prop p x)) (>< q)) (e+prop p y)) 
    



κ-trp-id : {a : V} -> (p : a ≐ a) ->  (x : || κ a ||)
      ->   < κ a > κ-trp-op p x ~ x

κ-trp-id {a} p x = <> (symV (e+prop p x))


κ-trp-irr : {a b : V} -> (p q : a ≐ b) ->  (x : || κ a ||)
      ->  < κ b > κ-trp-op p x ~ κ-trp-op q x
κ-trp-irr {a} {b} p q x = <> (traV (symV (e+prop p x)) (e+prop q x))



κ-trp-fn : {a b  c : V} -> (q : b ≐ c) -> (p : a ≐ b)  -> (r : a ≐ c)
      -> (x : || κ a ||)
      ->  < κ c >   κ-trp-op r x ~ κ-trp-op q (κ-trp-op p x)
κ-trp-fn {a} {b} {c} q p r x = <> (symV (traV (symV (traV (e+prop p x) (e+prop q (κ-trp-op p x))))
                                    (e+prop r x)))


κ-trp : {a b : V} -> (p : a ≐ b) -> || κ a  => κ b ||
κ-trp {a} {b} p = record { op = κ-trp-op p
                         ; ext = κ-trp-ext p }



-- V is a "locally small setoid" i.e. a classoid

VV : classoid
VV = record { object = V 
            ; _∼_ = eqV 
            ; eqrel = record { rf' = refl-eqV 
                             ; sy' = sym-eqV 
                             ; tr' = tra-eqV } 
            }


-- General definition of a proof irrelevant setoid-family indexed by
-- a classoid. The operation  κ  form the main example.

record Fam10 (A : classoid) : Set2 where
  field 
     std : ||| A ||| -> setoid
     trp : {a b : ||| A |||} -> (p : << A >> a ~ b) -> || (std a) => (std b) ||
     id-trp : {a : ||| A |||} -> (p : << A >> a ~ a) -> 
               (x : || std a ||) -> < std a > ap (trp p) x ~ x
     ir-trp : {a b : ||| A |||} -> (p  q : << A >> a ~ b) ->  
               (x : || std a ||) -> < std b > ap (trp p) x ~ ap (trp q) x
     fn-trp : {a b c : ||| A |||} -> (q : << A >> b ~ c) -> (p : << A >> a ~ b) ->  (r : << A >> a ~ c) ->
               (x : || std a ||) -> < std c >  ap (trp r) x ~ ap (trp q) (ap (trp p) x) 

infix 5 _§§_ 

_§§_ : {A : classoid} -> (F : Fam10 A) -> (a : ||| A |||) -> setoid
_§§_ F a = Fam10.std F a

infix 5 _±±_
_±±_ : {A : classoid} -> (F : Fam10 A) -> {a b : ||| A |||} -> (p : << A >> a ~ b) -> || (F §§ a)  => (F §§ b) ||
_±±_ F p = Fam10.trp F p



Fam10-flip : (A : classoid) -> (F : Fam10 A) -> (a b : ||| A |||) -> (p : << A >>  a ~ b) ->
       (x : || F §§ a ||) ->  (y : || F §§ b ||) -> 
       < F §§ b > ap (F ±± p) x ~ y  ->  < F §§ a >  x  ~  ap (F ±± (sym' p)) y 
Fam10-flip A F a b p x y q = 
                           let lm1 : < F §§ a > ap (F ±± (sym' p)) (ap (F ±± p) x) 
                                     ~ ap (F ±± (sym' p)) y
                               lm1 = extensionality (F ±± (sym' p)) (ap (F ±± p) x) y q
                               lm2 : < F §§ a > x  ~ ap (F ±± (sym' p)) (ap (F ±± p) x)
                               lm2 = tra  (sym (Fam10.id-trp F (refl' A a) x)) 
                                                       (Fam10.fn-trp F _ _ _ x)
                               main : < F §§ a > x  ~  ap (F ±± (sym' p)) y
                               main = tra lm2 lm1
                           in  main 



Fam10-inv-eq : (A : classoid) -> (F : Fam10 A) -> (a b : ||| A  |||) -> (p : << A >>  a ~ b) ->
       (x : || F §§ b ||) ->
       < F §§ b > ap (F ±± p) (ap (F ±± (sym' p)) x) ~  x
Fam10-inv-eq A F a b p x = tra (sym (Fam10.fn-trp F _ _ _ x)) (Fam10.id-trp F (refl' A b) x)

Fam10-trp-fn2 : (A : classoid) -> (F : Fam10 A) -> (a b c d : ||| A  |||) 
          -> (q : << A >>  b ~ c) -> (p : << A >>  a ~ b) 
          -> (r : << A >>  d ~ c) -> (u : << A >>  a ~ d) 
          -> (x : || F §§ a ||) -> < F §§ c > ap (F ±± q) (ap (F ±± p) x) ~ ap (F ±± r) (ap (F ±± u) x)
Fam10-trp-fn2 A F a b c d q p r u x = tra (sym (Fam10.fn-trp F q p (tra' p q) x)) 
                                                   (Fam10.fn-trp F r u (tra' p q) x)
Fam10-inv-gen : (A : classoid) -> (F : Fam10 A) -> (a b : ||| A  |||) 
       -> (p : << A >>  a ~ b) -> (q : << A >>  b ~ a) 
       ->  (x : || F §§ b ||) ->
       < F §§ b > ap (F ±± p) (ap (F ±±  q) x) ~  x
Fam10-inv-gen A F a b p q x = tra (sym (Fam10.fn-trp F _ _ _ x)) (Fam10.id-trp F (refl' A b) x)



-- here is the canonical example

κ-Fam : Fam10 VV
κ-Fam = record { std = κ
               ; trp = λ p →  κ-trp (>><< p) 
               ; id-trp = λ p x → κ-trp-id (>><< p) x 
               ; ir-trp = λ p q x → κ-trp-irr (>><< p) (>><< q) x 
               ; fn-trp = λ q p r x →  κ-trp-fn (>><< q) (>><< p) (>><< r) x 
               }



infix 5 _⊙⊙_

-- compose 10-family with 01-function

_⊙⊙_ : {A : setoid} -> {B : classoid} -> (F : Fam10 B) -> (f : setoidmap1 A B) -> Fam A
_⊙⊙_ {A} {B} F f = 
       record{ std = λ x →  F §§ (ap1 f x);
               trp = λ p → record { op =  λ x →  ap (F ±± (extensionality1 f _ _ p)) x ; 
                                   ext = λ x y q → extensionality (F ±± (extensionality1 f _ _ p)) x y q };
               id-trp = λ p x →  Fam10.id-trp F (extensionality1 f _ _ p) x ;
               ir-trp = λ p q x → Fam10.ir-trp F (extensionality1 f _ _ p) (extensionality1 f _ _ q) x;
               fn-trp = λ q p n x → Fam10.fn-trp F (extensionality1 f _ _ q) (extensionality1 f _ _ p) (extensionality1 f _ _ n) x
             }




κ° :  {A : setoid} -> (g : setoidmap1 A VV) -> Fam A
-- κ° {A} g = comp-with-can-std A g


κ° g = κ-Fam ⊙⊙ g

κ°-trp-prop : {A : setoid} -> (g : setoidmap1 A VV) 
             -> (a b : || A ||) -> (p : < A > a ~ b)
             -> (x : || κ (g • a) ||)
             -> ((g • a) ‣ x) ≐ ((g • b) ‣ (ap (κ° g ± p) x))
κ°-trp-prop {A} g a b p x =
  let lm :  ap1 g a ≐ ap1 g b
      lm = >><< (extensionality1 g _ _ p) 
  in  e+prop lm x 


 


κ°-trp-prop2 : {A : setoid} -> (g : setoidmap1 A VV) 
               -> (a b : || A ||) -> (p : < A > a ~ b)
               -> (x : || κ (g • a) ||)
               -> < κ (g • b) >   (ap (κ° g ± p) x) ~  (ap (κ-Fam ±± (extensionality1 g a b p)) x) -- (ap (κ° g ± p) x)
κ°-trp-prop2 {A} g a b p x = <> (refV _)




-- Every subsetoid of V gives rise to a set in V.

Sub-to-V : (S : subsetoid VV) -> V
Sub-to-V S = sup (|| δ S ||) (ap1 (ι S))

-- the operation is extensional 

ext-Sub-to-V-lm : (S T : subsetoid VV) -> (inclusion-subsetoids S T) -> (Sub-to-V S) ⊆ (Sub-to-V T)
ext-Sub-to-V-lm S T p = 
    λ x q ->  let q' : Σ || δ S || (λ y → x ≐ (ι S) • y)
                  q' = q
                  y :  || δ S ||
                  y = pj1 q
                  q'' :  x ≐ (ι S) • y
                  q'' = pj2 q
                  lm : Σ (|| δ S => δ T ||) (\f -> exteq1 (ι S) (comp1 (ι T) f))
                  lm = p
                  f : || δ S => δ T ||
                  f = pj1 p
                  lm' :  << VV >> ((ι S) • (pj1 q)) ~
                                     ((comp1 (ι T) (pj1 p)) • (pj1 q))
                  lm' = pj2 p y
                  main :  Σ || δ T || (λ y → x ≐ ((ι T) • y))
                  main = (ap f y) , traV q'' (>><< lm')
              in main

-- inclusion-subsetoids : {B : classoid} -> (S  T : subsetoid B) -> Set
-- inclusion-subsetoids {B} S T = Σ (|| δ S => δ T ||) (\f -> exteq1  (ι S) (comp1 (ι T) f)) 




ext-Sub-to-V :  (S T : subsetoid VV) -> equal-subsetoids S T -> (Sub-to-V S) ≐ (Sub-to-V T)
ext-Sub-to-V S T p = extensional-eqV (Sub-to-V S) (Sub-to-V T) 
                                     (ext-Sub-to-V-lm S T (prj1 p)) 
                                     (ext-Sub-to-V-lm T S (prj2 p))
V-to-Sub-iota-op : (u : V) -> || κ u || -> V
V-to-Sub-iota-op u a = u ‣ a

V-to-Sub-iota-ext : (u : V) ->  (a b : || κ u ||) 
         -> < κ u > a ~ b 
         -> << VV >> V-to-Sub-iota-op u a ~ V-to-Sub-iota-op u b
V-to-Sub-iota-ext u a b p = <<>> (>< p)

V-to-Sub-iota-inj : (u : V) ->  (a b : || κ u ||) 
         -> << VV >> V-to-Sub-iota-op u a ~ V-to-Sub-iota-op u b
         -> < κ u > a ~ b 
V-to-Sub-iota-inj u a b p = <> (>><< p)

V-to-Sub-iota : (u : V) -> setoidmap1 (κ u) VV
V-to-Sub-iota u = record { op = V-to-Sub-iota-op u 
                         ; ext =  V-to-Sub-iota-ext u }

V-to-Sub : V -> subsetoid VV 
V-to-Sub u = record { delta = κ u 
                    ; iota = V-to-Sub-iota u 
                    ; inj = V-to-Sub-iota-inj u }




membV-member :  (u v : V) -> u ∈ v -> member u  (V-to-Sub v)
membV-member u v (p1 , p2) = p1 , (sym' (<<>> p2))

member-membV :  (u v : V)  -> member u  (V-to-Sub v) -> u ∈ v
member-membV u v (p1 , p2) = p1 , symV (>><< p2)

ext-V-to-Sub-half :  (u v : V) -> u ≐ v -> inclusion-subsetoids (V-to-Sub u) (V-to-Sub v)
ext-V-to-Sub-half u v q = inclusion-lm-1-0 (V-to-Sub u) (V-to-Sub v)
                                (λ x p → membV-member x v (memV-right-ext x u v (member-membV x u p) q))

ext-V-to-Sub :  (u v : V) -> u ≐ v -> equal-subsetoids (V-to-Sub u) (V-to-Sub v) 
ext-V-to-Sub u v p = pair (ext-V-to-Sub-half u v p) (ext-V-to-Sub-half v u (symV p))





-- The isomorphism V ≅ Pow(V)

subsetoids-VV :  setoidmap11 (subsetoids VV) VV
subsetoids-VV = record { op = Sub-to-V 
                       ; ext = λ x y p → <<>> (ext-Sub-to-V x y (>><< p))  
                       }


VV-subsetoids : setoidmap11 VV (subsetoids VV) 
VV-subsetoids = record { op = V-to-Sub 
                       ; ext = λ x y p → <<>> ( ext-V-to-Sub x y (>><< p)) 
                       }

VV-subsetoids-inv-right : (u : ||| VV |||) ->
  << VV >> ap11 subsetoids-VV (ap11 VV-subsetoids u) ~ u
VV-subsetoids-inv-right (sup a f) = <<>> (refV (sup a f))

VV-subsetoids-inv-left : (A : ||| subsetoids VV |||) ->
  << subsetoids VV >> ap11  VV-subsetoids (ap11 subsetoids-VV A) ~ A
VV-subsetoids-inv-left A = <<>> (equal-lm-1-0 (ap11 VV-subsetoids (ap11 subsetoids-VV A)) A 
                                   (λ x → pair (λ p → p) (λ p → p)))



-- some lemmas for   subsetoids VV



make-function : (a : V) -> (g :  setoidmap1 (κ a) VV) -> V
make-function a g = sup (# a) (\x -> < a ‣ x , g • x >)



make-function-lm : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
  (x y : V) -> (< x , y > ∈ make-function a g) -> 
  Σ (# a) (\u -> < x , y > ≐ < a ‣ u , g • u >)
make-function-lm a g x y p = 
  let  mf = make-function a g
       u = pj1 p
       lm1 : < x , y > ≐ mf ‣ u
       lm1 = pj2 p
  in u , lm1 


make-function-lm2 : (a : V) -> (g :  setoidmap1 (κ a) VV) ->
  (x y : V) -> 
  Σ (# a) (\u -> < x , y > ≐ < a ‣ u , g • u >) ->
  (< x , y > ∈ make-function a g)
make-function-lm2 a g x y p = p

make-function-is-set-of-pairs1-lm : (a : V) 
   -> (g :  setoidmap1 (κ a) VV) -> (y : # (make-function a g))
   -> is-pairV1 ((make-function a g) ‣ y)
make-function-is-set-of-pairs1-lm (sup A f) g y = record { cp1 = _ ; cp2 = _ ; eqp = refl-eqV _ }

make-function-is-set-of-pairs1 :  (a : V) -> (g :  setoidmap1 (κ a) VV) 
  -> is-set-of-pairs1 (make-function a g)
make-function-is-set-of-pairs1 a g z p = 
   let mf = make-function a g
       y = pj1 p 
       lm1 : z ≐ (bV mf y)
       lm1 = pj2 p 
       lm2 : is-pairV1 (bV mf y)
       lm2 = make-function-is-set-of-pairs1-lm a g y
   in is-pairV1-ext _ _ (symV lm1) lm2


make-function-is-functional :  (a : V) -> (g :  setoidmap1 (κ a) VV) 
  -> is-functional (make-function a g)
make-function-is-functional a g x y z p q =
   let q1 : Σ (# a) (\u -> < x , z > ≐ < a ‣ u , g • u >)
       q1 = make-function-lm a g x z q
       u = pj1 q1
       q1b : < x , z > ≐ < a ‣ u , g • u >
       q1b = pj2 q1
       p1 : Σ (# a) (\u -> < x , y > ≐ < a ‣ u , g • u >)
       p1 = make-function-lm a g x y p
       v = pj1 p1
       p1b : < x , y > ≐ < a ‣ v , g • v >
       p1b = pj2 p1
       eq1 :  x ≐ a ‣ u
       eq1 = prj1 (pairV-inv-1 q1b)
       eq2 :  x ≐ a ‣ v
       eq2 = prj1 (pairV-inv-1 p1b)
       eq3 : a ‣ u ≐ a ‣ v
       eq3 = traV (symV eq1) eq2
       lm : ap1 g u ≐ ap1 g v
       lm = >><< (extensionality1 g u v (<> eq3)) 
       eq4 :  z ≐  ap1 g u
       eq4 = prj2 (pairV-inv-1 q1b)
       eq5 :  y ≐  ap1 g v   
       eq5 = prj2 (pairV-inv-1 p1b)

   in symV (traV eq4 (traV lm (symV eq5)))


make-function-is-total :  (a : V) -> (g :  setoidmap1 (κ a) VV) 
  -> is-total-on (make-function a g) a
make-function-is-total a g x p = 
    let  p1 :  Σ (# a) (\y -> x ≐ a ‣ y)
         p1 = p 
         p2 : x ≐ (a  ‣ (pj1 p1))
         p2 = pj2 p1
         lm :  Σ (# a) (λ u →
                 < x , g • (pj1 p) > ≐
                 < a ‣ u , g • u >)
         lm = pj1 p1 , pairV-ext p2 (refV _) 
         main : Σ10 V (λ y → < x , y > ∈ make-function a g)
         main = ap1 g (pj1 p1) , make-function-lm2 a g _ _ lm
    in main


{--

--}
