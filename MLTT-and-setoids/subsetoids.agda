
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- {-# OPTIONS --no-eta-equality #-}

-- Agda version 2.5.2

module subsetoids where

open import basic-types
open import basic-setoids
open import dependent-setoids


{-- moved this to basic-setoids.agda

record setoidmap1 (A : setoid) (B : classoid) : Set1 where
  field
    op : || A || ->  ||| B |||
    ext : (x y : || A ||) -> (< A > x ~ y)  -> (<< B >> (op x) ~ (op y))

ap1 : {A : setoid} -> {B : classoid} -> (f : setoidmap1 A B) -> (a : || A ||) -> ||| B |||
ap1 f a = setoidmap1.op f a

infix 10 _•_

-- •  is  \bu2
_•_ : {A : setoid} -> {B : classoid} -> (f : setoidmap1 A B) -> (a : || A ||) -> ||| B |||
_•_ f a = ap1 f a

exteq1 : {A : setoid}->  {B : classoid} -> (f g : setoidmap1 A B) -> Set
exteq1 {A} {B} f g = (x : || A ||) ->  << B >> (f • x) ~ (g • x)

setoidmaps1 : (A : setoid) -> (B : classoid) -> classoid
setoidmaps1 A B = record {object = setoidmap1 A B
                          ; _∼_  =  exteq1 {A} {B}
                          ; eqrel = record { rf' = λ f x → refl' B (f • x) 
                                           ; sy' = λ f g p x → sym' {B} (p x) 
                                           ; tr' = λ f g h p q x → tra' {B} (p x) (q x) }
                         }


extensionality1 : {A : setoid} -> {B : classoid} -> (f : setoidmap1 A B) -> (x y : || A ||) -> 
             (< A > x ~ y) ->  (<< B >> (f • x) ~ (f • y))
extensionality1 {A} {B} f x y p = (setoidmap1.ext f x y) p

is-injective1 : {A : setoid} -> {B : classoid} -> (f : setoidmap1 A B) -> Set
is-injective1 {A} {B} f = (x y : || A ||) -> (<< B >> (f • x) ~ (f • y)) ->  < A > x ~ y




comp1 : {A B : setoid} -> {C : classoid} -> (f : setoidmap1 B C) -> (g : || A => B ||) -> setoidmap1 A C
comp1 {A} {B} {C} f g =  record { op =   (\x -> ap1 f (ap g x)) 
                                ; ext = λ x y p → setoidmap1.ext f (ap g x) (ap g y) 
                                                                    (setoidmap.ext g x y p)
                               }
        


record setoidmap11 (A B : classoid) : Set1 where
  field
    op : ||| A ||| ->  ||| B |||
    ext : (x y : ||| A |||) -> (<< A >> x ~ y)  -> (<< B >> (op x) ~ (op y))

ap11 : {A B : classoid} -> (f : setoidmap11 A B) -> (a : ||| A  |||) -> ||| B |||
ap11 f a = setoidmap11.op f a


extensionality11 : {A B : classoid} -> (f : setoidmap11 A B) -> (x y : ||| A |||) -> 
             (<< A >> x ~ y) ->  (<< B >> (ap11 f x) ~ (ap11 f  y))
extensionality11 {A} {B} f x y p = (setoidmap11.ext f x y) p



comp11 : {A B C : classoid} -> (f : setoidmap11 B C) -> (g : setoidmap11 A B) -> setoidmap11 A C
comp11 {A} {B} {C} f g =  record { op =   (\x -> ap11 f (ap11 g x)) 
                                ; ext = λ x y p → setoidmap11.ext f (ap11 g x) (ap11 g y) 
                                                                    (setoidmap11.ext g x y p)
                               }

comp01 : {A : setoid} -> {B C : classoid} -> (f : setoidmap11 B C) -> (g : setoidmap1 A B) -> setoidmap1 A C
comp01 {A} {B} {C} f g =  record { op =   (\x -> ap11 f (ap1 g x)) 
                                ; ext = λ x y p → setoidmap11.ext f (ap1 g x) (ap1 g y) 
                                                                    (setoidmap1.ext g x y p)
                               }

--}

                          
record subsetoid (B : classoid) : Set1 where
  field               
    delta : setoid
    iota : setoidmap1 delta B
    inj : is-injective1 iota

δ : {B : classoid} -> (subsetoid B) -> setoid
δ S = subsetoid.delta S

ι : {B : classoid} -> (S : subsetoid B) -> setoidmap1 (δ S) B
ι S = subsetoid.iota S

ι-inj : {B : classoid} -> (S : subsetoid B) -> is-injective1 (ι S)
ι-inj {B} S = subsetoid.inj S

member : {B : classoid} -> (x : ||| B |||) -> (S : subsetoid B) -> Set
member {B} x S =  Σ (|| δ S ||) (\u -> << B >>  (ap1 (ι S) u) ~  x)

member-inj-lm : {B : classoid}  -> (S : subsetoid B) -> (u v : || δ S ||) ->
     << B >>  (ap1 (ι S) u) ~ (ap1 (ι S) v) -> <  δ S > u ~ v 
member-inj-lm {B} S u v p = subsetoid.inj S u v p

member-inj-lm2 : {B : classoid}  -> (S : subsetoid B) -> (u : || δ S ||) ->
     member (ap1 (ι S) u) S
member-inj-lm2 {B} S u =  u , refl' B _

inclusion-subsetoids1 : {B : classoid} -> (S  T : subsetoid B) -> Set1
inclusion-subsetoids1 {B} S T = (x : ||| B |||) -> (member x S) -> (member x T)

inclusion-subsetoids : {B : classoid} -> (S  T : subsetoid B) -> Set
inclusion-subsetoids {B} S T = Σ (|| δ S => δ T ||) (\f -> exteq1  (ι S) (comp1 (ι T) f)) 

θ : {B : classoid} -> (S  T : subsetoid B) -> inclusion-subsetoids S T -> || δ S => δ T ||
θ S T p = pj1 p

θ-prop : {B : classoid} -> (S  T : subsetoid B) -> (p : inclusion-subsetoids S T) -> 
    exteq1 (ι S) (comp1 (ι T) (θ S T p))
θ-prop S T p =  pj2 p



θ-id : {B : classoid} -> (S : subsetoid B) -> (p : inclusion-subsetoids S S) -> 
    < δ S => δ S > θ S S p ~ idmap 
θ-id {B} S p =  <> (λ x → let lm :   exteq1(ι S)  (comp1 (ι S) (θ S S p)) 
                              lm = θ-prop S S p
                          in sym {δ S} (ι-inj S _ _ (lm x)))



θ-ir : {B : classoid} -> (S  T : subsetoid B) -> (p q : inclusion-subsetoids S T) -> 
    < δ S => δ T > θ S T p ~ θ S T q 
θ-ir {B} S T p q = 
                 <>  (
                    let lm :   exteq1 (comp1 (ι T) (θ S T p))  (comp1 (ι T) (θ S T q)) 
                        lm = λ x → tra' {B} (sym' {B} (θ-prop {B} S T p x)) (θ-prop {B} S T q x)
                    in λ x → ι-inj T _ _ (lm x))



θ-fn : {B : classoid} -> (R S T : subsetoid B) 
       -> (p : inclusion-subsetoids R S) 
       -> (q : inclusion-subsetoids S T) 
       -> (r : inclusion-subsetoids R T) ->
    < δ R => δ T > (θ R T r) ~ ((θ S T q) ° (θ R S p)) 
θ-fn {B} R S T p q r 
       = <> (λ x → 
                (let lm1 : exteq1 (ι R) (comp1 (ι S) (θ R S p))  
                     lm1 = θ-prop R S p
                     lm2 : exteq1 (ι S) (comp1 (ι T) (θ S T q))
                     lm2 = θ-prop S T q
                     lm3 : exteq1 (ι R) (comp1 (ι T) (θ R T r))
                     lm3 = θ-prop R T r
                     lm :  << B >> ap1 (ι T) (ap (θ R T r) x)  ~ ap1 (ι T) (ap (θ S T q) (ap (θ R S p)  x))
                     lm = tra' {B} (sym' {B} (lm3 x)) (tra' {B} (lm1 x) (lm2 _))
                     main' :  < δ T > ap (θ R T r) x ~ ap (θ S T q) (ap (θ R S p)  x)
                     main' = ι-inj T _ _ lm                  
                     main :  < δ T > ap (θ R T r) x ~ ap ((θ S T q) ° (θ R S p))  x
                     main = main'
                 in main))





inclusion-subsetoids1-op : {B : classoid} -> (S  T : subsetoid B) 
  -> (p : inclusion-subsetoids1 {B} S T)
  -> || δ S || -> || δ T ||
inclusion-subsetoids1-op {B} S T p u = pj1 ( p (ap1 (ι S) u) (member-inj-lm2 {B} S u)) 



inclusion-subsetoids1-fun : {B : classoid} -> (S  T : subsetoid B) 
  -> (p : inclusion-subsetoids1 {B} S T)
  -> || δ S => δ T ||                                    
inclusion-subsetoids1-fun {B} S T p 
    = record { op = inclusion-subsetoids1-op S T p 
             ; ext = λ x y q → 
                   let q' : < δ S > x ~ y
                       q' = q
                       p' :  (x : ||| B |||) -> (member x S) -> (member x T)
                       p' = p
                       p1 : member ((ι S) • x) T
                       p1 = p' ((ι S) • x) (member-inj-lm2 S x)
                       p12 : << B >> ((ι T) • (pj1 (p (ap1 (ι S) x) (member-inj-lm2 S x))))  ~ ((ι S) • x)
                       p12 = pj2 p1
                       p2 : member ((ι S) • y) T
                       p2 = p' ((ι S) • y) (member-inj-lm2 S y)
                       p22 : << B >> ((ι T) • (pj1 (p ((ι S) • y) (member-inj-lm2 S y))))  ~  ((ι S) • y)
                       p22 = pj2 p2
                       eq :  << B >>  ((ι S) • x) ~ ((ι S) • y) 
                       eq = extensionality1 (ι S) x y q'
                       lm :  << B >> ap1 (ι T) (pj1 (p (ap1 (ι S) x) (member-inj-lm2 S x)))  ~
                                     ap1 (ι T) (pj1 (p (ap1 (ι S) y) (member-inj-lm2 S y))) 
                       lm = tra' {B} p12 (tra' {B} eq (sym' {B} p22))
                       main : < δ T > inclusion-subsetoids1-op S T p x ~
                                      inclusion-subsetoids1-op S T p y
                       main = member-inj-lm {B} T _ _ lm 
                   in main }


inclusion-lm-1-0 : {B : classoid} -> (S  T : subsetoid B) ->
        inclusion-subsetoids1 S T ->  inclusion-subsetoids S T
inclusion-lm-1-0 {B} S T p = inclusion-subsetoids1-fun {B} S T p  , 
                   (λ x -> let p1 : member (ap1 (ι S) x) T
                               p1 = p (ap1 (ι S) x) (member-inj-lm2 S x)
                               p12 : << B >> ap1 (ι T) (pj1 (p (ap1 (ι S) x) (member-inj-lm2 S x)))  ~ ap1 (ι S) x
                               p12 = pj2 p1
                               main :  << B >> ap1 (ι S) x ~
                                              ap1 (comp1 (ι T) (inclusion-subsetoids1-fun S T p)) x
                               main = sym' {B} p12
                          in main)


inclusion-lm-0-1 : {B : classoid} -> (S  T : subsetoid B) ->
        inclusion-subsetoids S T ->  inclusion-subsetoids1 S T
inclusion-lm-0-1 {B} S T p = λ x q → 
         ap (pj1 p) (pj1 q) ,  
        let lm : << B >>  ap1 (ι S) (pj1 q) ~ x
            lm = pj2 q
            main : << B >> ap1 (ι T) (ap (pj1 p) (pj1 q)) ~ x
            main = tra' {B} (sym' {B} (pj2 p (pj1 q))) lm
        in main



equal-subsetoids1 : {B : classoid} -> (S  T : subsetoid B) -> Set1
equal-subsetoids1 {B} S T = (x : ||| B |||) -> (iff (member x S) (member x T))

equal-subsetoids : {B : classoid} -> (S  T : subsetoid B) -> Set
equal-subsetoids {B} S T = and (inclusion-subsetoids S T)  (inclusion-subsetoids T S)

equal-lm-1-0 : {B : classoid} -> (S  T : subsetoid B) ->
        equal-subsetoids1 S T ->  equal-subsetoids S T
equal-lm-1-0 S T p = pair (inclusion-lm-1-0 S T (λ x q → prj1 (p x) q)) 
                          (inclusion-lm-1-0 T S (λ x q → prj2 (p x) q))

equal-lm-0-1 : {B : classoid} -> (S  T : subsetoid B) ->
        equal-subsetoids S T ->  equal-subsetoids1 S T
equal-lm-0-1 {B} S T p = λ x → pair (inclusion-lm-0-1 {B} S T (prj1 p) x) 
                                    (inclusion-lm-0-1 {B} T S (prj2 p) x)




subsetoids :  classoid -> classoid
subsetoids B = record { object = subsetoid B 
                      ; _∼_ = equal-subsetoids 
                      ; eqrel = record { rf' = λ S → equal-lm-1-0 S S (λ x → pair (λ p → p) (λ p → p)) 
                                       ; sy' = λ S T p → pair (prj2 p) (prj1 p) 
                                       ; tr' = λ S T M p q → 
                                          equal-lm-1-0 S M (λ x → 
                                                 pair (λ hy → prj1 (equal-lm-0-1 T M q x) (prj1 (equal-lm-0-1 S T p x) hy))
                                                      (λ hy → prj2 (equal-lm-0-1 S T p x) (prj2 (equal-lm-0-1 T M q x) hy))) 
                                       }
                      }



eq-lemma : (B : classoid) -> (S  T : ||| subsetoids B |||) 
          -> << subsetoids B >> S ~ T -> (x : ||| B |||) 
          ->  member x S -> member x T
eq-lemma B S T p x =  prj1 (equal-lm-0-1 S T (>><< p) x)




-- So subsetoids ( ... (subsetoids B) ...) is still a classoid



-- bounded families

BFam : (A : setoid) -> (B : classoid) -> Set1
BFam A B = setoidmap1 A (subsetoids B)


global-member : {A : setoid} -> {B : classoid} -> (f : setoidmap1 A B) -> (S : BFam A B) -> Set
global-member {A} {B} f S =  (x : || A ||) -> member (f • x)  (S • x)



-- TO DO

BFam-Fam-std : (A : setoid) -> (B : classoid) -> (S : BFam A B) -> (x : || A ||) -> setoid
BFam-Fam-std A B S x =  δ (S • x)



BFam-Fam-trp : (A : setoid) -> (B : classoid) -> (S : BFam A B) -> (a b : || A ||) 
    -> ( p : < A > a ~ b)
    -> || BFam-Fam-std A B S a => BFam-Fam-std A B S b ||
BFam-Fam-trp A B S a b p =
    let lm : equal-subsetoids (S • a) (S • b)
        lm = >><< (extensionality1 S _ _ p) 
    in  (θ (S • a) (S • b) (prj1 lm))




BFam-Fam : (A : setoid) -> (B : classoid) -> (S : BFam A B) -> Fam A
BFam-Fam A B S = record { std = λ x → BFam-Fam-std A B S x  
                        ; trp = λ {a} {b} p → BFam-Fam-trp A B S a b p 
                        ; id-trp = λ {a} p x → >< (θ-id (ap1 S a) ((prj1 (>><< (extensionality1 S _ _ p))))) x  
                        ; ir-trp = λ {a} {b} p q x → >< (θ-ir (ap1 S a ) (ap1 S b) 
                                                          (prj1 (>><< (extensionality1 S _ _ p))) 
                                                          (prj1 (>><< (extensionality1 S _ _ q)))) x 
                        ; fn-trp = λ {a} {b} {c} q p r x → >< (θ-fn (ap1 S a) (ap1 S b) (ap1 S c )
                                                               (prj1 (>><< (extensionality1 S _ _ p))) 
                                                               (prj1 (>><< (extensionality1 S _ _ q))) 
                                                               (prj1 (>><<(extensionality1 S _ _ r)))) x 
                        } 

{--
extensionality1 : {A : setoid} -> {B : classoid} -> (f : setoidmap1 A B) -> (x y : || A ||) -> 
             (< A > x ~ y) ->  (<< B >> (f • x) ~ (f • y))
--}


global-member-element-op : (A : setoid) -> (B : classoid) -> (S : BFam A B) -> (f : setoidmap1 A B) -> 
  (p : global-member f S) -> (x : || A ||) -> || BFam-Fam A B S § x ||
global-member-element-op A B S f p x =  pj1 (p x)



global-member-element : (A : setoid) -> (B : classoid) -> (S : BFam A B) -> (f : setoidmap1 A B) -> 
  (p : global-member f S) -> || Π-std A (BFam-Fam A B S) ||
global-member-element A B S f p 
      = (global-member-element-op A B S f p) , 
         (λ x y q ->  
           let lm1 : << B >> ap1 (ι (ap1 S x)) (pj1 (p x)) ~ ap1 f x
               lm1 = pj2 (p x)
               lm2 : << B >> ap1 (ι (ap1 S y)) (pj1 (p y)) ~ ap1 f y
               lm2 = pj2 (p y)
               lm3 : << B >>  ap1 f x ~ ap1 f y
               lm3 = extensionality1 f x y q 
               lm4 : << B >> ap1 (ι (ap1 S x)) (pj1 (p x)) ~ ap1 (ι (ap1 S y)) (pj1 (p y))
               lm4 = tra' lm1 (tra' lm3 (sym' lm2))
               lm5 :  exteq1 (ι (ap1 S x)) (comp1 (ι (ap1 S y)) (θ (ap1 S x) (ap1 S y) 
                                (prj1 (>><< (extensionality1 S _ _ q)))))
               lm5 = θ-prop (ap1 S x) (ap1 S y) (prj1 (>><< (extensionality1 S _ _ q))) 
               lm6 : << B >> ap1 (ι (ap1 S x)) (pj1 (p x)) ~
                             ap1 (comp1 (ι (ap1 S y))
                                         (θ (ap1 S x) (ap1 S y) (prj1 (>><< (extensionality1 S x y q)))))
                                 (pj1 (p x))
               lm6 = lm5 (pj1 (p x))
               main'' :  << B >>   ap1 (ι (ap1 S y)) (ap (θ (ap1 S x) (ap1 S y) 
                                      (prj1 (>><< (extensionality1 S _ _ q)))) (pj1 (p x)))  
                              ~  ap1 (ι (ap1 S y)) (pj1 (p y))
               main'' = sym' {B} (tra' {B} (sym' {B} lm4) lm6)
               main' : < δ (ap1 S y) >  ap (θ (ap1 S x) (ap1 S y) 
                                         (prj1 (>><< (extensionality1 S _ _ q)))) (pj1 (p x)) ~ (pj1 (p y))
               main' = ι-inj (ap1 S y)  _ _  main''
               main : < δ (ap1 S y) >  ap (BFam-Fam A B S ± q) (pj1 (p x)) ~ (pj1 (p y))
               main = main'
           in main)

{--

--  (BFam-Fam A B S ± q) = (θ (ap1 S x) (ap1 S y) (prj1 (extensionality1 S _ _ q)))

-- BFam-Fam-trp A B S a b p =
--    let lm : equal-subsetoids (ap1 S a) (ap1 S b)
--        lm = extensionality1 S _ _ p
--    in  (θ (ap1 S a) (ap1 S b) (prj1 lm))

-- θ-prop : {B : classoid} -> (S  T : subsetoid B) -> (p : inclusion-subsetoids S T) -> 
--    exteq1 (ι S) (comp1 (ι T) (θ S T p))
-- θ-prop S T p =  pj2 p

--}
