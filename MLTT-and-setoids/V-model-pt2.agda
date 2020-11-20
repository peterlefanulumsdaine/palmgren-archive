-- disable the K axiom:

{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-pt2 where

open import basic-types
open import basic-setoids
open import dependent-setoids
open import subsetoids
open import iterative-sets
open import iterative-sets-pt2
open import iterative-sets-pt3
open import V-model-pt0
open import V-model-pt1

--

mk--Fx-op : {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       -> || κ-Fam §§ (apt A u) ||
       -> ||| VV |||
mk--Fx-op A B u z = apt B (u , z)

mk-Par-op-Fx-op : {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       -> || κ-Fam §§ (apt A u) ||
       -> V
mk-Par-op-Fx-op A B u z =  apt B (u , z)

mk-Par-op-Fx-ext : {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       -> (x y : || κ-Fam §§ (apt A u) ||)
       ->  < κ-Fam §§ (apt A u) > x ~ y
       ->  << VV >> mk-Par-op-Fx-op A B u x ~ mk-Par-op-Fx-op A B u y
mk-Par-op-Fx-ext A B u x y p =  extensionality1 (ty.type B) (u , x) (u , y) (<> (pairV-ext (refV _) (>< p)))




mk-Par-op-Fx : {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       -> setoidmap1 (κ-Fam §§ (apt A u)) VV
mk-Par-op-Fx A B u = record { op = mk-Par-op-Fx-op A B u
                            ; ext = mk-Par-op-Fx-ext A B u }


mk-Par-op : {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> || κ Γ || ->  ||| Par VV κ-Fam |||
mk-Par-op  A B u = record { Ix = (apt A u)
                         ; Fx = mk-Par-op-Fx A B u }



mk-Par-ext :
          {Γ : ctx}
       -> (A : ty Γ)
       -> (B : ty (Γ ▷ A))
       -> (x y : || κ Γ ||)
       -> < κ Γ > x ~ y ->
       << Par VV κ-Fam >> mk-Par-op A B x ~ mk-Par-op A B y
mk-Par-ext {Γ} A B x y p =
          let lm1 : << VV >> Ixx (mk-Par-op A B x) ~ Ixx (mk-Par-op A B y) -- i.e  << VV >> (A • x) ~  (A • y)
              lm1 =  (extensionality1 (ty.type A) x y p)
              main : Σ (<< VV >> Ixx (mk-Par-op A B x) ~ Ixx (mk-Par-op A B y))
                      (λ p₁ →
                         (x₁ : || κ-Fam §§ Ixx (mk-Par-op A B x) ||) →
                           << VV >> Fxx (mk-Par-op A B x) • x₁ ~
                                    (Fxx (mk-Par-op A B y) • ap (κ-Fam ±± p₁) x₁))
              main = lm1 , (λ z → let eq3 :  < κ (Γ ▷ A) > (x , z) ~  (y , ap (κ-Fam ±± lm1) z)
                                      eq3 = <> (pairV-ext (>< p) (e+prop (>><< lm1) z))
                                      eq2 : << VV >> (apt B (x , z))  ~ (apt B (y , (ap (κ-Fam ±±
                                                                         (extensionality1 (ty.type A) x y p))
                                                                          z)))
                                      eq2 = extensionality1 (ty.type B)  (x , z) (y , (ap
                                                                       (κ-Fam ±±
                                                                         (extensionality1 (ty.type A) x y p))
                                                                          z)) eq3

                                      eq : << VV >> Fxx (mk-Par-op A B x) • z ~
                                              (Fxx (mk-Par-op A B y) • ap (κ-Fam ±± (extensionality1 (ty.type A) x y p)) z)
                                      eq = eq2
                                  in eq)
          in <<>> main



mk-Par :  {Γ : ctx}
       -> (A : ty Γ)  -> (B : ty (Γ ▷ A))
       -> setoidmap1 (κ Γ)  (Par VV κ-Fam)
mk-Par  A B = record { op = mk-Par-op A B
                      ; ext = mk-Par-ext A B }



subsetoids-VV-inj : (A B : ||| subsetoids VV |||)
         -> (q :  << VV >>  ap11 subsetoids-VV A ~ ap11 subsetoids-VV B)
         -> << subsetoids VV >> A ~ B
subsetoids-VV-inj A B q = tra'
                               (sym' (VV-subsetoids-inv-left A))
                               (tra' (extensionality11 VV-subsetoids
                                                      (ap11 subsetoids-VV A)
                                                      (ap11 subsetoids-VV B)
                                                      q)
                                     (VV-subsetoids-inv-left B))



κ-Fam-aux5 : (A B : ||| subsetoids VV |||)
         -> (q :  << VV >>  ap11 subsetoids-VV A ~  ap11 subsetoids-VV B)
         -> (v : || δ A ||)
         -> (ap1 (ι B) (ap (κ-Fam ±± q) v)) ≐ (ap1 (ι A) v)
κ-Fam-aux5 A B q v = let lmq :  sup (|| δ A ||) (ap1 (ι A))  ≐ sup (|| δ B ||) (ap1 (ι B))
                         lmq = >><< q
                         lm  : (ap1 (ι B) (e+ (>><< q) v)) ≐ (ap1 (ι A) v)
                         lm = symV (e+prop (>><< q) v)
                     in lm




-- Pi- formation rule


Π-f :  {Γ : ctx}
--
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
--     ---------------------------------------
       -> ty Γ
--
Π-f A B = ty.tyy (comp01 piVV (mk-Par A  B))



-- equalities expanding  (Π-f {Γ} A B) ‣ h  etc


Π-f-exp1 :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       ->  (apt (Π-f A B)  u) ≐ piV (apt A u) (mk-Par-op-Fx A B u)
Π-f-exp1 A B u = refV _

Π-f-exp2 :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       ->  (apt (Π-f A B)  u) ≐ sup (piV-iV (apt A u) (mk-Par-op-Fx A B u))
                                    (piV-bV (apt A u) (mk-Par-op-Fx A B u))
Π-f-exp2 A B u = refV _

Π-f-exp3 :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       -> (h : # (apt (Π-f {Γ} A B)  u))
       -> (apt (Π-f {Γ} A B)  u) ‣ h ≐  sup (#  (apt A u)) (\x ->  <  (apt A u) ‣ x , (apt B  (u ,  x)) ‣ ((pj1 h) x) >)
Π-f-exp3  A B u h = refV _



Π-f-exp3a :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       -> (h : # (apt (Π-f {Γ} A B)  u))
       -> (x : # (apt A u))
       -> ((apt (Π-f {Γ} A B)  u) ‣ h) ‣ x ≐  < (apt A u) ‣ x , (apt B  (u ,  x)) ‣ ((pj1 h) x) >
Π-f-exp3a  A B u h x = refV _

Π-f-exp3b :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       -> (h : # (apt (Π-f {Γ} A B)  u))
       -> (x y : # (apt A u))
       ->  (apt A u) ‣ x ≐  (apt A u) ‣ y
       ->  (apt B  (u ,  x)) ‣ ((pj1 h) x)  ≐ (apt B  (u ,  y)) ‣ ((pj1 h) y)
Π-f-exp3b {Γ} A B u h x y p =
    let  eq : < κ (Γ ▷ A) > (u , x) ~ (u , y)
         eq = <> (pairV-ext (refV (Γ ‣ u)) p)
         eq1 : (apt B  (u ,  x)) ≐ (apt B  (u ,  y))
         eq1 = >><< (extensionality1 (ty.type B) (u , x) (u , y) eq)
         lm : < κ (apt B (u , y)) >
               ap (κ° (Fxx (ap1 (mk-Par A B) u)) ± (<> p)) (pj1 h x) ~ pj1 h y
         lm = pj2 h x y (<> p)
         main : (apt B  (u ,  x)) ‣ ((pj1 h) x)  ≐ (apt B  (u ,  y)) ‣ ((pj1 h) y)
         main = traV (e+prop eq1 ((pj1 h) x)) (>< lm)
    in main



Π-f-exp4 :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u v : || κ Γ ||)
       -> (h : # (apt (Π-f A B) u))
       -> (k : # (apt (Π-f A B)  v))
       -> (apt (Π-f A B)  u) ‣ h ≐  (apt (Π-f A B)  v) ‣ k
       -> and ((x : (# (apt A u))) -> Σ (# (apt A v)) (\y -> < (apt A u) ‣ x , (apt B (u ,  x)) ‣ ((pj1 h) x) >
                                                      ≐  < (apt A v) ‣ y , (apt B (v ,  y)) ‣ ((pj1 k) y) >))
              ((y : (# (apt A v))) -> Σ (# (apt A u)) (\x -> < (apt A u) ‣ x , (apt B (u ,  x)) ‣ ((pj1 h) x) >
                                                      ≐  < (apt A v) ‣ y , (apt B (v ,  y)) ‣ ((pj1 k) y) >))
Π-f-exp4  A B u v h k p = p



Π-f-exp5 :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u v : || κ Γ ||)
       -> (h : # (apt (Π-f A B) u))
       -> (k : # (apt (Π-f A B)  v))
       -> and ((x : (# (apt A u))) -> Σ (# (apt A v)) (\y -> < (apt A u) ‣ x , (apt B (u ,  x)) ‣ ((pj1 h) x) >
                                                      ≐  < (apt A v) ‣ y , (apt B (v ,  y)) ‣ ((pj1 k) y) >))
              ((y : (# (apt A v))) -> Σ (# (apt A u)) (\x -> < (apt A u) ‣ x , (apt B (u ,  x)) ‣ ((pj1 h) x) >
                                                      ≐  < (apt A v) ‣ y , (apt B (v ,  y)) ‣ ((pj1 k) y) >))
       -> (apt (Π-f A B)  u) ‣ h ≐  (apt (Π-f A B)  v) ‣ k
Π-f-exp5  A B u v h k p = p



Π-f-exp5b :  {Γ : ctx}
       -> (A : ty Γ)   -> (B B' : ty (Γ ▷ A))
       -> (u v : || κ Γ ||)
       -> (h : # (apt (Π-f A B) u))
       -> (k : # (apt (Π-f A B') v))
       -> and ((x : (# (apt A u))) -> Σ (# (apt A v)) (\y -> < (apt A u) ‣ x , (apt B (u ,  x)) ‣ ((pj1 h) x) >
                                                      ≐  < (apt A v) ‣ y , (apt B' (v ,  y)) ‣ ((pj1 k) y) >))
              ((y : (# (apt A v))) -> Σ (# (apt A u)) (\x -> < (apt A u) ‣ x , (apt B (u ,  x)) ‣ ((pj1 h) x) >
                                                      ≐  < (apt A v) ‣ y , (apt B' (v ,  y)) ‣ ((pj1 k) y) >))
       -> (apt (Π-f A B)  u) ‣ h ≐  (apt (Π-f A B')  v) ‣ k
Π-f-exp5b  A B B' u v h k p =
    pair (λ x → (pj1 (prj1 p x)) , (pairV-ext (prj1 (pairV-inv-1 (pj2 (prj1 p x)))) ((prj2 (pairV-inv-1 (pj2 (prj1 p x)))))))
         (λ y → (pj1 (prj2 p y)) , (pairV-ext (prj1 (pairV-inv-1 (pj2 (prj2 p y)))) (prj2 (pairV-inv-1 (pj2 (prj2 p y))))))



Π-f-exp6 :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       -> (h k : # (apt (Π-f A B) u))
       -> ((x : (# (apt A u))) ->
              ((apt B (u ,  x)) ‣ ((pj1 h) x)
            ≐  (apt B (u ,  x)) ‣ ((pj1 k) x)))
       -> (apt (Π-f A B)  u) ‣ h ≐  (apt (Π-f A B)  u) ‣ k
Π-f-exp6 A B u h k p = Π-f-exp5 A B u u h k
                          (pair (λ x → x , pairV-ext (refV _) (p x))
                                (λ x → x , pairV-ext (refV _) (p x)))


Π-f-exp7 :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       -> (h : # (apt (Π-f A B) u))
       -> (k : # (apt (Π-f A B) u))
       -> (apt (Π-f A B)  u) ‣ h ≐  (apt (Π-f A B)  u) ‣ k
       -> and ((x : (# (apt A u))) -> Σ (# (apt A u)) (\y -> < (apt A u) ‣ x , (apt B (u ,  x)) ‣ ((pj1 h) x) >
                                                          ≐  < (apt A u) ‣ y , (apt B (u ,  y)) ‣ ((pj1 k) y) >))
              ((y : (# (apt A u))) -> Σ (# (apt A u)) (\x -> < (apt A u) ‣ x , (apt B (u ,  x)) ‣ ((pj1 h) x) >
                                                          ≐  < (apt A u) ‣ y , (apt B (u ,  y)) ‣ ((pj1 k) y) >))
Π-f-exp7  A B u h k p = p

Π-f-exp3c :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (u : || κ Γ ||)
       -> (h k : # (apt (Π-f {Γ} A B)  u))
       -> (apt (Π-f A B)  u) ‣ h ≐  (apt (Π-f A B)  u) ‣ k
       -> (x : # (apt A u))
       -> (apt B  (u ,  x)) ‣ ((pj1 h) x)  ≐ (apt B  (u ,  x)) ‣ ((pj1 k) x)
Π-f-exp3c {Γ} A B u h k p x =
    let  lm = (prj1 (Π-f-exp7 A B u h k p)) x
         t = pj1 lm
         eq : < apt A u ‣ x , apt B (u , x) ‣ pj1 h x > ≐  < apt A u ‣ t , apt B (u , t) ‣ pj1 k t >
         eq = pj2 lm
         eq1 : apt A u ‣ x ≐  apt A u ‣ t
         eq1 = prj1 (pairV-inv-1 eq)
         eq2 :  apt B (u , x) ‣ pj1 h x  ≐  apt B (u , t) ‣ pj1 k t
         eq2 = prj2 (pairV-inv-1 eq)
         lm2 :  apt B (u , t) ‣ (ap (κ° (Fxx (ap1 (mk-Par A B) u)) ± (<> eq1)) (pj1 k x)) ≐ apt B (u , t) ‣ pj1 k t
         lm2 = >< (pj2 k x t (<> eq1))
         lm2b : < κ (Γ ▷ A) >  (u , x) ~ (u , t)
         lm2b = <> (pairV-ext (refV _) eq1)
         lm2c : (apt B  (u ,  x)) ≐  (apt B  (u ,  t))
         lm2c = >><< (extensionality1 (ty.type B) (u ,  x) (u ,  t) lm2b)
         lm3 : apt B (u , t) ‣ (ap (κ° (Fxx (ap1 (mk-Par A B) u)) ± (<> eq1)) (pj1 k x)) ≐ (apt B  (u ,  x)) ‣ ((pj1 k) x)
         lm3 = symV (e+prop lm2c ((pj1 k) x))
         eq3 :  apt B (u , t) ‣ pj1 k t  ≐ (apt B  (u ,  x)) ‣ ((pj1 k) x)
         eq3 = traV (symV lm2) lm3
         main : (apt B  (u ,  x)) ‣ ((pj1 h) x)  ≐ (apt B  (u ,  x)) ‣ ((pj1 k) x)
         main = traV eq2 eq3
    in main



-- should be moved to iterative-sets-**

irr22-lm : (u z z' v : V)
           -> (p : u ≐ z)
           -> (q : z ≐ v)
           -> (r : u ≐ z')
           -> (t : z' ≐ v)
           -> (x : # u) ->
           v ‣ ap (κ-Fam ±± (<<>> q)) (ap (κ-Fam ±± (<<>> p)) x)
                           ≐
           v ‣  ap (κ-Fam ±± (<<>> t)) (ap (κ-Fam ±± (<<>> r)) x)
irr22-lm u z z' v p q r t x = traV (irr2-lm u z v p q (traV p q) x)
                                   (symV (irr2-lm u z' v r t (traV p q) x))




-- towards congruence rules for Pi-formation

Π-f-rcong-half-map-ext :  {Γ : ctx}
          -> (A : ty Γ)   -> (B B' : ty (Γ ▷ A))
          -> (p : Γ ▷ A ==> B == B')
          -> (x : || κ Γ ||)
          -> (f : # (ty.type (Π-f A B) • x))
          -> (u v  : # (Ixx (ap1 (mk-Par A B') x)))
          -> (q  : < κ (Ixx (ap1 (mk-Par A B') x)) > u ~ v)
          -> (< κ° (Fxx (ap1 (mk-Par A B') x)) § v >
              ap (κ° (Fxx (ap1 (mk-Par A B') x)) ± q)
              (e+ (>><< (ape p (x , u))) (pj1 f u))
              ~ e+ (>><< (ape p (x , v))) (pj1 f v))
Π-f-rcong-half-map-ext {Γ} A B B' p x f u v q =
    let lm : < κ (apt B (x , v))  >  -- < κ° (Fxx (ap1 (mk-Par A B) x)) § v >
             ap (κ° (Fxx (ap1 (mk-Par A B) x)) ± q)
                (pj1 f u)
              ~  (pj1 f v)
        lm = pj2 f u v q
        lm' :   < κ (apt B' (x , v))  >  -- < κ° (Fxx (ap1 (mk-Par A B) x)) § v >
                e+ (>><< (ape p (x , v))) (ap (κ° (Fxx (ap1 (mk-Par A B) x)) ± q)
                                (pj1 f u))
              ~ e+ (>><< (ape p (x , v))) (pj1 f v)
        lm' = <> (e+ext (>><< (ape p (x , v))) _ _ (>< lm))

        lm2 : (apt B' (x , v)) ‣ (ap (κ° (Fxx (ap1 (mk-Par A B') x)) ± q) (e+ (>><< (ape p (x , u))) (pj1 f u)))
              ≐ (apt B' (x , v)) ‣ (e+ (>><< (ape p (x , v))) (ap (κ° (Fxx (ap1 (mk-Par A B) x)) ± q)
                                                 (pj1 f u)))
        lm2 = (irr22-lm (apt B (x , u)) (apt B' (x , u)) (apt B (x , v)) (apt B' (x , v))  _ _ _ _  (pj1 f u))
    in <> (traV lm2 (>< lm'))





Π-f-rcong-half-map :  {Γ : ctx}
          -> (A : ty Γ)   -> (B B' : ty (Γ ▷ A))
          -> (Γ ▷ A ==> B == B')
          -> (x : || κ Γ ||)
          -> (f : # (ty.type (Π-f A B) • x))
          -> (# (ty.type (Π-f A B') • x))
Π-f-rcong-half-map {Γ} A B B' p x f =
          ((\y -> e+ (>><< (ape p (x , y))) (pj1 f y))) , Π-f-rcong-half-map-ext {Γ} A B B' p x f
Π-f-rcong-half : {Γ : ctx}
          -> (A : ty Γ)   -> (B B' : ty (Γ ▷ A))
          -> (Γ ▷ A ==> B == B')
          -> (x : || κ Γ ||)
          -> ty.type (Π-f A B) • x ≤ (ty.type (Π-f A B') • x)
Π-f-rcong-half {Γ} A B B' p x f =
       Π-f-rcong-half-map {Γ} A B B' p x f  ,  Π-f-exp5b A B B' x x f (Π-f-rcong-half-map A B B' p x f)
              (pair (λ u → u , (pairV-ext (refV _) (e+prop (>><< (ape p (x , u))) (pj1 f u))))
                    (λ v → v , (pairV-ext (refV _) (e+prop (>><< (ape p (x , v))) (pj1 f v)))))



-- a congruence rule for Pi-formation

Π-f-rcong :  {Γ : ctx}
--
       -> (A : ty Γ)   -> (B B' : ty (Γ ▷ A))
       ->  (Γ ▷ A ==> B == B')
--     ---------------------------------------
       -> (Γ  ==>  Π-f A B == Π-f A B')
--
Π-f-rcong {Γ} A B B' p =
     mk-eqty (λ x
    → <<>> (extensional-eqV (ty.type (Π-f A B) • x) (ty.type (Π-f A B') • x)
            (half-eqV-to-inclusion _ _ (Π-f-rcong-half A B B' p x))
            (half-eqV-to-inclusion _ _ ((Π-f-rcong-half A B' B (tysym p) x)))))




-- lambda abstraction

lambda-op  :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (b : raw (Γ ▷ A))
       -> || κ Γ || -> V
lambda-op A B b x = sup (# (apt A x))
                            (λ y → pairV ((apt A x) ‣ y) (apr b ( x , y )))

lambda-ext  :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (b : raw (Γ ▷ A))
       -> (u v : || κ Γ ||)
       -> < κ Γ > u ~ v
       -> << VV >> lambda-op A B b u ~ lambda-op A B b v
lambda-ext A B b u v p =
        let eq :  (apt A u) ≐ (apt A v)
            eq = >><< (extensionality1 (ty.type A) u v p)
            p' = >< p
        in  <<>> (eqV-unexpand (lambda-op A B b u) (lambda-op  A B b v)
                         (λ x →  (e+ eq x) ,
                                 pairV-ext (e+prop eq x)
                                           (>><< (extensionality1 (raw.rawterm b)
                                                (u , x)
                                                (v , e+ (>><< (extensionality1 (ty.type A) u v p)) x)
                                                (<> (pairV-ext p' (e+prop eq x)))))
                                 )
                         (λ y →  e+ (symV eq) y ,
                                 pairV-ext (symV (e+prop (symV eq) y))
                                           (>><< (extensionality1 (raw.rawterm b)
                                                 (u , e+ (symV (>><< (extensionality1 (ty.type A) u v p))) y)
                                                 (v , y)
                                                 (<> (pairV-ext p' (symV (e+prop (symV eq) y))))))
                                 )
                 )




lambda  :  {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (b : raw (Γ ▷ A))
       -> raw Γ
lambda A B b = mkraw (record { op = lambda-op A B b
                             ; ext = lambda-ext A B b })





-- towards Pi-introduction rule

Π-i-aux2 : {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (b : raw (Γ ▷ A))
       -> (p : Γ ▷ A ==> b :: B)
       -> (u : || κ Γ ||)
       -> (x y : # (apt A u))
       -> (q : < κ (apt A u) > x ~ y)
       -> < (κ° (mk-Par-op-Fx A B u)) § y > (ap (κ° (mk-Par-op-Fx A B u) ± q) (pj1 (apel p (u , x))))  ~  pj1 (apel p (u , y))
Π-i-aux2 {Γ} A B b p u x y q =
    let  lmx : (apr b  (u , x)) ∈  (apt B (u , x))
         lmx = apel p (u , x)
         lmx2 : (apr b (u , x)) ≐ (apt B (u , x)) ‣ pj1 (apel p (u , x))
         lmx2 = pj2 lmx
         lmy : (apr b (u , y)) ∈  (apt B (u , y))
         lmy = apel p (u , y)
         lmy2 : (apr b  (u , y)) ≐ (apt B  (u , y)) ‣ pj1 (apel p (u , y))
         lmy2 = pj2 lmy
         lmq : < κ (Γ ▷ A) >  (u , x) ~ (u , y)
         lmq = <> (pairV-ext (refV  (Γ ‣ u)) (>< q))
         lmq2 : << VV >> (apr b (u , x)) ~ (apr b (u , y))
         lmq2 = extensionality1 (raw.rawterm b) (u , x) (u , y) lmq
         lmq3 : << VV >> (apt B (u , x)) ~ (apt B (u , y))
         lmq3 = extensionality1 (ty.type B) (u , x) (u , y) lmq


         main :   (apt B  (u , y)) ‣ (ap (κ° (mk-Par-op-Fx A B u) ± q) (pj1 (apel p (u , x))))
                  ≐ ((mk-Par-op-Fx A B u • y) ‣ pj1 (apel p (u , y)))
         main = traV (traV (traV (symV (e+prop (>><< lmq3) (pj1 (apel p (u , x))) )) (symV lmx2)) (>><< lmq2)) lmy2
    in  <> main






Π-i-aux : {Γ : ctx}
       -> (A : ty Γ)   -> (B : ty (Γ ▷ A))
       -> (b : raw (Γ ▷ A))
       -> Γ ▷ A ==> b :: B
       -> (u : || κ Γ ||)
       -> piV-iV (apt A u) (mk-Par-op-Fx A B u)
Π-i-aux A B b p u =
    let h : (x : # (apt A u)) ->  # ((mk-Par-op-Fx A B u) • x)
        h = λ z → pj1 (apel p (u , z))
        hx :  (x y : # (apt A u))
              -> (p : < κ (apt A u) > x ~ y)
              -> < (κ° (mk-Par-op-Fx A B u))  § y > (ap (κ° (mk-Par-op-Fx A B u) ± p) (h x))  ~ h y
        hx = Π-i-aux2 A B b p u
    in h , hx


-- Pi-introduction

Π-i  :  {Γ : ctx}
       -> (A : ty Γ)   -> {B : ty (Γ ▷ A)}
       -> {b : raw (Γ ▷ A)}
       -> Γ ▷ A ==> b :: B
--  -----------------------------------------
        -> Γ ==> lambda A B b :: Π-f A B
--
Π-i {Γ} A {B} {b} p =   mk-elt (\x ->
    let h : piV-iV (apt A x) (mk-Par-op-Fx A B x)
        h =  Π-i-aux A B b p x

        lm2 : sup (# (apt A  x))
                            (λ y → pairV ((apt A x) ‣ y) (apr b ( x , y )))
              ≐ sup (# (apt A x))
                            (\y ->  < (apt A x) ‣ y , ((mk-Par-op-Fx A B x) • y) ‣ ((pj1 h) y) >)
        lm2 = pair (λ t → t , pairV-ext (refV _) (pj2 (apel p (x , t))))
                   (λ t → t , pairV-ext (refV _) (pj2 (apel p (x , t))))

        lm1 : apr (lambda A B b) x ≐ piV-bV (apt A x) (mk-Par-op-Fx A B x) h
        lm1 = lm2
        lm : apr (lambda A B b) x ∈ piV (apt A x) (mk-Par-op-Fx A B x)
        lm = h , lm1
        main : apr (lambda A B b) x ∈ ap11 piVV (mk-Par A B • x)
        main = lm
    in main)



-- towards a xi-rule for lambda

Π-xi-raw  :  {Γ : ctx}
       -> (A : ty Γ)   -> {B : ty (Γ ▷ A)}
       -> (b : raw (Γ ▷ A))
       -> (b' : raw (Γ ▷ A))
       -> (<< Raw (Γ ▷ A) >> b ~ b')
       ->  (x : || κ Γ ||)
       ->  apr (lambda A B b) x ≐ apr (lambda A B b') x
Π-xi-raw  A {B} b b' p x =
         let  p' = >><< (>><< p)
              eq :  sup (# (apt A x))
                            (λ y → pairV ((apt A x) ‣ y) (apr b ( x , y )))
                    ≐
                    sup (# (apt A x))
                            (λ y → pairV ((apt A x) ‣ y) (apr b' ( x , y )))
              eq = easy-eqV (# (apt A x)) _ _
                     (λ y → pairV-ext (refV _) (>><< (p'  (x ,  y))))
         in eq

-- the xi-rule



Π-xi  :  {Γ : ctx}
       -> (A : ty Γ)   -> {B : ty (Γ ▷ A)}
       -> {b : raw (Γ ▷ A)}
       -> {b' : raw (Γ ▷ A)}
       -> (r : Γ ▷ A ==> b == b' :: B)
--  -----------------------------------------
        -> Γ ==> lambda A B b ==  lambda A B b' :: Π-f A B
--
Π-xi {Γ} A {B} {b} {b'} r =
                      let r1 = (prj1 r)
                      in
                          pair (Π-xi-raw {Γ} A {B} b b' (<<>> (<<>> (λ x → <<>> (r1 x)))))
                                 (pair (Π-i A {B} {b} (prj1 (prj2 r)))
                                       (Π-i A {B} {b'} (prj2 (prj2 r))))

