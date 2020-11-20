-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- {-# OPTIONS --no-eta-equality #-}

-- Agda version 2.5.2


module iterative-sets-pt3 where

open import basic-types
open import basic-setoids
open import dependent-setoids
open import subsetoids
open import iterative-sets
open import iterative-sets-pt2


-- generalities about parameterizations and families


record Par-elts (A : classoid) (F : Fam10 A) : Set1 where
  field
     Ix :  ||| A |||
     Fx :  setoidmap1 (F §§ Ix) A

Ixx : {A : classoid} -> {F : Fam10 A} -> Par-elts A F -> ||| A |||
Ixx u = Par-elts.Ix u

Fxx : {A : classoid} -> {F : Fam10 A} -> (u : Par-elts A F) -> setoidmap1 (F §§ (Ixx u)) A
Fxx u =  Par-elts.Fx u



Par-eq : {A : classoid} -> {F : Fam10 A} -> (u v : Par-elts A F) -> Set
Par-eq {A} {F} u v =
     Σ  (<< A >> (Ixx u) ~ (Ixx v))
      (\p -> (x : || F §§ (Ixx u) ||)
           ->  << A >>  ((Fxx u) • x) ~  ((Fxx v) • (ap (F ±± p) x)))


Par-eq-rf' : {A : classoid} -> {F : Fam10 A} -> (u : Par-elts A F) -> Par-eq u u
Par-eq-rf' {A} {F} u = (refl' A (Ixx u)) ,
        (λ x → extensionality1 (Fxx u)  x  (ap (F ±± (refl' A (Ixx u))) x)
                    (sym {F §§ Ixx u} (Fam10.id-trp F (refl' A (Ixx u)) x)))


Par-eq-sy' : {A : classoid} -> {F : Fam10 A} -> (u v : Par-elts A F) -> Par-eq u v -> Par-eq v u
Par-eq-sy' {A} {F} u v p = sym' {A} (pj1 p) ,
        (λ x → let p1 = pj1 p
                   p2 : << A >> Fxx u • ap (F ±± (sym' {A} (pj1 p))) x ~
                           (Fxx v • ap (F ±± (pj1 p)) (ap (F ±± (sym' {A} (pj1 p))) x))
                   p2 = pj2 p (ap (F ±± (sym' {A} (pj1 p))) x)
               in tra' {A} (sym' {A} (extensionality1 (Fxx v) _ _ (Fam10-inv-eq A F _ _ (pj1 p) x)))
                           (sym' {A} p2))

Par-eq-tr' : {A : classoid} -> {F : Fam10 A} -> (u v z : Par-elts A F)
          -> Par-eq u v -> Par-eq v z -> Par-eq u z
Par-eq-tr' {A} {F} u v z p q = (tra' {A} (pj1 p) (pj1 q)) ,
        (λ x → let p1 = pj1 p
                   p2 = pj2 p x
                   q1 = pj1 q
                   q2 = pj2 q (ap (F ±± (pj1 p)) x)
               in tra' {A} p2
                           (tra' {A} q2
                                     (extensionality1 (Fxx z) _ _ (sym {F §§ Ixx z} (Fam10.fn-trp F _ _ _ x)))))



Par : (A : classoid) -> (F : Fam10 A) -> classoid
Par A F = record { object = Par-elts A F
                 ; _∼_ = Par-eq {A} {F}
                 ; eqrel = record { rf' = Par-eq-rf'
                                  ; sy' = Par-eq-sy'
                                  ; tr' = Par-eq-tr'} }






e+prop' : (u v : V) ->
         (p : u ≐ v) -> (x : # u) ->
         u ‣  x ≐ v ‣ ap (κ-Fam ±± (<<>> p)) x
e+prop' u v p x = e+prop p x

e-prop' : (u v : V) ->
         (p : u ≐ v) -> (y : # v) ->
         u ‣ ap (κ-Fam ±± (<<>> (symV p))) y ≐ v ‣ y
e-prop' u v p y = traV (symV (eqV-left-right-prop p y)) (e-prop p y)




irr2-lm : (u z v : V)
           -> (p : u ≐ z)
           -> (q : z ≐ v)
           -> (r : u ≐ v)
            -> (x : # u) ->
           v ‣ ap (κ-Fam ±± (<<>> q)) (ap (κ-Fam ±± (<<>> p)) x)
                           ≐
           v ‣ (ap (κ-Fam ±± (<<>> r)) x)
irr2-lm u z v p q r x =
   let lm1 : u ‣ x  ≐ v ‣ ap (κ-Fam ±± (<<>> r)) x
       lm1 = e+prop' u v r x
       lm2 : u ‣ x  ≐ z ‣ ap (κ-Fam ±± (<<>> p)) x
       lm2 = e+prop' u z p x
       lm3 : z ‣ ap (κ-Fam ±± (<<>> p)) x ≐ v ‣ ap (κ-Fam ±±  (<<>> q)) (ap (κ-Fam ±± (<<>> p)) x)
       lm3 = e+prop' z v q  (ap (κ-Fam ±± (<<>> p)) x)

   in symV (traV (symV lm1) (traV lm2 lm3))


irr-lm : (u z v : V)
           -> (p : u ≐ z)
           -> (r : u ≐ v)
            -> (x : # u) ->
           z ‣  (ap (κ-Fam ±± (<<>> p)) x)
                           ≐
           v ‣ (ap (κ-Fam ±± (<<>> r)) x)
irr-lm u z v p r x =
   let lm1 : u ‣ x  ≐ z ‣ ap (κ-Fam ±± (<<>> p)) x
       lm1 = e+prop' u z p x
       lm2 : u ‣ x  ≐ v ‣ ap (κ-Fam ±± (<<>> r)) x
       lm2 = e+prop' u v r x


   in  traV (symV lm1) lm2

irr1-lm : (u v : V)
           -> (p : u ≐ v)
           -> (r : u ≐ v)
            -> (x : # u) ->
           v ‣  (ap (κ-Fam ±± (<<>> p)) x)
                           ≐
           v ‣ (ap (κ-Fam ±± (<<>> r)) x)
irr1-lm u v p r x = irr-lm u v v p r x



Fxx-lm : (u v : ||| Par VV κ-Fam |||)
             -> (p : << Par VV κ-Fam >> u ~ v)
             -> (x : # (Ixx v)) ->
                    << VV >> (Fxx v • ap (κ-Fam ±± pj1 (>><< p)) (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) x)) ~ (Fxx v • x)
Fxx-lm u v p x = let lm : < κ-Fam §§ Ixx v > x ~
                                              ap (κ-Fam ±± pj1 (>><< p)) (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) x)
                     lm = sym {κ-Fam §§ Ixx v} (Fam10-inv-eq  VV κ-Fam _ _ (pj1 (>><< p)) x)
                 in sym' (extensionality1 (Fxx v) _ _ lm)




Fxx-lm' : (u v : ||| Par VV κ-Fam |||)
             -> (p : << Par VV κ-Fam >> u ~ v)
             -> (x : # (Ixx v)) ->
                    << VV >> (Fxx u • (ap (κ-Fam ±± (sym' (pj1 (>><< p )))) x))
                            ~ (Fxx v • x)
Fxx-lm' u v p x =
                      let  -- p1 : (Ixx u) ≐ (Ixx v)
                           -- p1 = >><< (pj1 (>><< p))
                           -- -p1 : (Ixx v) ≐ (Ixx u)
                           -- -p1 = symV p1

                           p2 :  (x : || κ-Fam §§ (Ixx u) ||)
                                    ->  << VV >>  ((Fxx u) • x) ~  ((Fxx v) • (ap (κ-Fam ±±  (pj1 (>><< p))) x))
                           p2 = pj2 (>><< p)
                           p2' : << VV >> Fxx u • ap (κ-Fam ±± sym' (pj1 (>><< p))) x ~
                                 (Fxx v • ap (κ-Fam ±± (pj1 (>><< p))) (ap (κ-Fam ±± sym' (pj1 (>><< p))) x))
                           p2' = p2 (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) x)
                           p3 : << VV >>
                                 (Fxx v • ap (κ-Fam ±± (pj1 (>><< p))) (ap (κ-Fam ±± sym' (pj1 (>><< p))) x))
                                 ~ (Fxx v • x)
                           p3 = Fxx-lm u v p x
                           p4 : << VV >> Fxx u • ap (κ-Fam ±± sym' (pj1 (>><< p))) x ~ (Fxx v • x)
                           p4 = tra' p2' p3
                      in p4







-- sigma and pi constructions for the V-model

sigmaV-op : ||| Par VV κ-Fam ||| ->  ||| VV |||
sigmaV-op u = sigmaV (Ixx u) (Fxx u)

sigmaV-ext0-map : (u v : ||| Par VV κ-Fam |||)
             -> << Par VV κ-Fam >> u ~ v
             -> # (sigmaV (Ixx u) (Fxx u))
             -> # (sigmaV (Ixx v) (Fxx v))
sigmaV-ext0-map u v p x = ap (κ-Fam ±± (pj1 (>><< p))) (pj1 x) , ap (κ-Fam ±± (pj2 (>><< p) (pj1 x))) (pj2 x)


sigmaV-half-ext : (u v : ||| Par VV κ-Fam |||) -> << Par VV κ-Fam >> u ~ v ->   sigmaV-op u ⊆ sigmaV-op v
sigmaV-half-ext u v p =
                   let p1 : (Ixx u) ≐ (Ixx v)
                       p1 = >><< (pj1 (>><< p))
                       p2 :  (x : || κ-Fam §§ (Ixx u) ||)
                                   ->  << VV >>  ((Fxx u) • x) ~  ((Fxx v) • (ap (κ-Fam ±± (pj1 (>><< p))) x))
                       p2 = pj2 (>><< p)
                       lm1 :  (x :  Σ (# (Ixx u)) (\y -> # ((Fxx u) • y))) ->
                                         Σ (Σ (# (Ixx v)) (\y -> # ((Fxx v) • y)))
                                           (\y ->
                                            (< (Ixx u) ‣ (pj1 x) , ((Fxx u) • (pj1 x)) ‣ (pj2 x) >
                                             ≐ < (Ixx v) ‣ (pj1 y) , ((Fxx v) • (pj1 y)) ‣ (pj2 y) >))
                       lm1 x = let p2b = p2 (pj1 x)
                                   p2bb =  e+prop (>><< p2b) (pj2 x)
                               in
                                  (sigmaV-ext0-map u v p x) ,
                                  (pairV-ext (e+prop p1 (pj1 x))
                                             p2bb)
                   in half-eqV-to-inclusion _ _ lm1

sigmaV-ext : (u v : ||| Par VV κ-Fam |||) -> << Par VV κ-Fam >> u ~ v -> << VV >>  sigmaV-op u ~ sigmaV-op v
sigmaV-ext u v p = <<>> (extensional-eqV (sigmaV-op u) (sigmaV-op v)
                        (sigmaV-half-ext u v p)
                        (sigmaV-half-ext v u (sym' {Par VV κ-Fam} {u} {v} p)))




sigmaVV : setoidmap11 (Par VV κ-Fam) VV
sigmaVV = record { op = sigmaV-op ; ext = sigmaV-ext }



piV-op : ||| Par VV κ-Fam ||| ->  ||| VV |||
piV-op u = piV (Ixx u) (Fxx u)


piV-ext00 : {u v : ||| Par VV κ-Fam |||}
             -> << Par VV κ-Fam >> u ~ v
             -> ((x : # (Ixx u)) → # (Fxx u • x))
             -> (x : # (Ixx v)) → # (Fxx v • x)
piV-ext00 {u} {v} p h x =  ap (κ-Fam ±± (Fxx-lm' u v p x)) (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) x))




piV-ext0-lm : (u v : ||| Par VV κ-Fam |||)
             -> (p : << Par VV κ-Fam >> u ~ v)
             -> (h : # (piV (Ixx u) (Fxx u)))
             -> (x y : # (Ixx v))
             -> (p' : < κ (Ixx v) > x ~ y)
             ->  < κ° (Fxx v) § y > ap (κ° (Fxx v) ± p') (piV-ext00 {u} {v} p (pj1 h) x) ~
                                    piV-ext00 {u} {v} p (pj1 h) y
piV-ext0-lm u v p h x y p' =
       let  q : < κ (Ixx u) > (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) x) ~ (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) y)
            q = extensionality (κ-Fam ±± (sym' (pj1 (>><< p)))) x y p'
            h2 : (x₁ y₁ : # (Ixx u)) (p₁ : < κ (Ixx u) > x₁ ~ y₁) →
                 < κ° (Fxx u) § y₁ > ap (κ° (Fxx u) ± p₁) (pj1 h x₁) ~ pj1 h y₁
            h2 = pj2 h
            h2' : < κ° (Fxx u) § ap (κ-Fam ±± sym' (pj1 (>><< p))) y >
                  ap (κ° (Fxx u) ± extensionality (κ-Fam ±± sym' (pj1 (>><< p))) x y p')
                    (pj1 h (ap (κ-Fam ±± sym' (pj1 (>><< p))) x))
                  ~ pj1 h (ap (κ-Fam ±± sym' (pj1 (>><< p))) y)
            h2' = h2 _ _ q
            lm :  < κ° (Fxx v) § y >  (ap (κ-Fam ±± (Fxx-lm' u v p y)) (ap (κ° (Fxx u) ± extensionality (κ-Fam ±± sym' (pj1 (>><< p))) x y p')
                                             (pj1 h (ap (κ-Fam ±± sym' (pj1 (>><< p))) x))))
                      ~ (ap (κ-Fam ±± (Fxx-lm' u v p y)) ((pj1 h) (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) y)))
            lm = extensionality (κ-Fam ±± (Fxx-lm' u v p y)) _ _ h2'

            lm2 : < κ° (Fxx v) § y >
                   ap (κ° (Fxx v) ± p')
                      (ap (κ-Fam ±± Fxx-lm' u v p x)
                           (pj1 h (ap (κ-Fam ±± sym' (pj1 (>><< p))) x)))
                   ~
                   ap (κ-Fam ±± Fxx-lm' u v p y)
                      (ap (κ° (Fxx u) ± extensionality (κ-Fam ±± sym' (pj1 (>><< p))) x y p')
                           (pj1 h (ap (κ-Fam ±± sym' (pj1 (>><< p))) x)))
            lm2 = Fam10-trp-fn2 VV κ-Fam (Fxx u • ap (κ-Fam ±± sym' (pj1 (>><< p))) x) (Fxx v • x)  (Fxx v • y) (Fxx u • ap (κ-Fam ±± sym' (pj1 (>><< p))) y)  _ (Fxx-lm' u v p x) (Fxx-lm' u v p y) _  (pj1 h (ap (κ-Fam ±± sym' (pj1 (>><< p))) x))
            main : < κ° (Fxx v) § y > (ap (κ° (Fxx v) ± p')
                                        (ap (κ-Fam ±± (Fxx-lm' u v p x)) ((pj1 h) (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) x)))) ~
                                        (ap (κ-Fam ±± (Fxx-lm' u v p y)) ((pj1 h) (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) y)))

            main = tra lm2 lm


       in main -- main

{--

Fam10-trp-fn2 : (A : classoid) -> (F : Fam10 A) -> (a b c d : ||| A  |||)
          -> (q : << A >>  b ~ c) -> (p : << A >>  a ~ b)
          -> (r : << A >>  d ~ c) -> (u : << A >>  a ~ d)
          -> (x : || F §§ a ||) -> < F §§ c > ap (F ±± q) (ap (F ±± p) x) ~ ap (F ±± r) (ap (F ±± u) x)

--}



piV-ext0-map : (u v : ||| Par VV κ-Fam |||)
             -> << Par VV κ-Fam >> u ~ v
             -> # (piV (Ixx u) (Fxx u))
             -> # (piV (Ixx v) (Fxx v))
piV-ext0-map u v p h = piV-ext00 {u} {v} p (pj1 h) , \x -> \y -> piV-ext0-lm u v p h x y




piV-half-ext-lm : (u v : ||| Par VV κ-Fam |||) -> (p : << Par VV κ-Fam >> u ~ v)
             -> (h : # (piV (Ixx u) (Fxx u)))
             -> piV (Ixx u) (Fxx u) ‣ h ≐
                piV (Ixx v) (Fxx v) ‣ piV-ext0-map u v p h
piV-half-ext-lm u v p (h , he) =
   let q : << VV >> (Ixx u) ~ (Ixx v)
       q = pj1 (>><< p)
       he'   : (x y : # (Ixx u)) -> (r : < κ (Ixx u) > x ~ y) ->
                  < κ° (Fxx u) § y > ap (κ° (Fxx u) ± r) (h x) ~ h y
       he' = he
       he'' : (x y : # (Ixx u)) -> (r : < κ (Ixx u) > x ~ y) ->
                  < κ ((Fxx u) • y) >  (ap (κ-Fam ±± (extensionality1 (Fxx u) x y r)) (h x))  ~ (h y)
       he'' = he'

       eq :  (x : ||  κ-Fam §§ (Ixx u) ||)
                ->  << VV >>  ((Fxx u) • x) ~  ((Fxx v) • (ap (κ-Fam ±± q) x))
       eq = pj2 (>><< p)
       lm1 : (x : # (Ixx u)) →
                 Σ (# (Ixx v))
                    (λ y →
                       < Ixx u ‣ x , (Fxx u • x) ‣ h x > ≐
                       < Ixx v ‣ y , (Fxx v • y) ‣ piV-ext00 {u} {v} p h y >)
       lm1 x =  let
                    eq1 : << VV >> Fxx u • x ~ (Fxx v • e+ (>><< (pj1 (>><< p))) x)
                    eq1 = eq x

                    eq1c : < κ (Ixx u) > (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x)) ~ x
                    eq1c = Fam10-inv-gen VV κ-Fam (Ixx v) (Ixx u) _ _ x

                    eq1d : < κ° (Fxx u) § x > h x ~ (ap (κ° (Fxx u) ± eq1c) (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+  (>><< (pj1 (>><< p))) x))))
                    eq1d = sym {κ° (Fxx u) § x} (he' _ _ eq1c)
                    eq1e : (Fxx u • x) ‣ h x ≐
                           (Fxx u • x) ‣ (ap (κ° (Fxx u) ± eq1c) (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x))))
                    eq1e = >< eq1d

                    eq1b : (Fxx u • x) ‣  (ap (κ° (Fxx u) ± eq1c) (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x)))) ≐
                             (Fxx v •  e+ (>><< (pj1 (>><< p))) x) ‣ e+ (>><< (pj2 (>><< p) x))  (ap (κ° (Fxx u) ± eq1c) (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x))))
                    eq1b = e+prop (>><< eq1)  (ap (κ° (Fxx u) ± eq1c) (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x))))

                    eq1faa : < κ° (Fxx v) § (e+ (>><< (pj1 (>><< p))) x) >
                                (e+ (>><< (pj2 (>><< p) x)) (ap (κ° (Fxx u) ± eq1c) (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x)))))
                               ~ (ap (κ-Fam ±± (Fxx-lm' u v p (e+ (>><< (pj1 (>><< p))) x)))
                                                                (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x))))
                    eq1faa = sym  -- {κ° (Fxx v) § e+ (pj1 p) x}
                                 (Fam10.fn-trp κ-Fam  _ (extensionality1 (Fxx u) _ _ eq1c) (Fxx-lm' u v p (e+ (>><< (pj1 (>><< p))) x))
                                               (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x))))
-- to revise

                    eq1fa : (Fxx v • e+ (>><< (pj1 (>><< p))) x) ‣ e+ (>><< (pj2 (>><< p) x))  (ap (κ° (Fxx u) ± eq1c) (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x))))
                             ≐
                            (Fxx v • e+ (>><< (pj1 (>><< p))) x) ‣ ap (κ-Fam ±± (Fxx-lm' u v p (e+ (>><< (pj1 (>><< p))) x)))
                                                                (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x)))
                    eq1fa = >< eq1faa
                    eq1f : (Fxx u • x) ‣ (ap (κ° (Fxx u) ± eq1c) (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x))))
                             ≐
                           (Fxx v • e+ (>><< (pj1 (>><< p))) x) ‣ ap (κ-Fam ±± (Fxx-lm' u v p (e+ (>><< (pj1 (>><< p))) x)))
                                                                (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x)))
                    eq1f = traV eq1b eq1fa

                    lm1e : (Fxx u • x) ‣ h x ≐
                           (Fxx v • e+ (>><< (pj1 (>><< p))) x) ‣ ap (κ-Fam ±± (Fxx-lm' u v p (e+ (>><< (pj1 (>><< p))) x)))
                                                                (h (ap (κ-Fam ±± (sym' (pj1 (>><< p)))) (e+ (>><< (pj1 (>><< p))) x)))
                    lm1e = traV eq1e eq1f

                    lm1f : (Fxx u • x) ‣ h x ≐
                           (Fxx v • e+ (>><< (pj1 (>><< p))) x) ‣ piV-ext00 {u} {v} p h (e+ (>><< (pj1 (>><< p))) x)
                    lm1f = lm1e

                in   (e+ (>><< q) x) ,
                        pairV-ext (e+prop (>><< q) x)
                                lm1f


       lm2 :  (y : # (Ixx v)) →
                 Σ (# (Ixx u))
                   (λ x →
                       < Ixx u ‣ x , (Fxx u • x) ‣ h x > ≐
                       < Ixx v ‣ y , (Fxx v • y) ‣ piV-ext00 {u} {v} p h y >)
       lm2 y =  let p1  : << VV >> Ixx u ~ Ixx v
                    p1 = pj1 (>><< p)
                    -p1 = sym' (pj1 (>><< p))
                    x' : # (Ixx u)
                    x' = ap (κ-Fam ±± -p1) y

                    r : << VV >> Fxx u • ap (κ-Fam ±± -p1) y ~ (Fxx v • y)
                    r = Fxx-lm' u v p y
                    eq' : Fxx u • x' ≐ (Fxx v • ap (κ-Fam ±± p1) x')  -- use eq
                    eq' = >><< (eq x')


                    lm2h : (Fxx u • x') ‣ (h x') ≐
                         (Fxx v • ap (κ-Fam ±± pj1 (>><< p)) x') ‣
                          (ap (κ-Fam ±± (pj2 (>><< p) x')) (h x'))
                    lm2h = e+prop' _ _ eq' (h x')
                    mm :  < κ (Ixx v) > (ap (κ-Fam ±± pj1 (>><< p)) x') ~  y
                    mm = Fam10-inv-gen VV κ-Fam _ _ (pj1 (>><< p)) _ y

                    lmm : << VV >> (Fxx v • ap (κ-Fam ±± pj1 (>><< p)) x') ~ (Fxx v • y)
                    lmm = extensionality1 (Fxx v) _ _ mm

                    tp :   << VV >> Fxx u • ap (κ-Fam ±± sym' (pj1 (>><< p))) y ~
                           (Fxx v • ap (κ-Fam ±± pj1 (>><< p)) (ap (κ-Fam ±± sym' (pj1 (>><< p))) y))
                    tp = (pj2 (>><< p) x')

                    lm2l : (Fxx v • y) ‣ ap (κ-Fam ±±  lmm) (ap (κ-Fam ±± pj2 (>><< p) x') (h x'))
                           ≐
                           (Fxx v • y) ‣ (ap (κ-Fam ±± r) (h x'))
                    lm2l = irr2-lm _ _ (Fxx v • y)  _ (>><< lmm) (>><< r) (h x')

-- **

                    lm2k : (Fxx v • ap (κ-Fam ±± pj1 (>><< p)) x') ‣ (ap (κ-Fam ±± (pj2 (>><< p) x')) (h x'))
                           ≐
                           (Fxx v • y) ‣ ap (κ-Fam ±±  lmm)
                                         (ap (κ-Fam ±± pj2 (>><< p) x')
                                           (h x'))
                    lm2k = e+prop' _ _ (>><< lmm) (ap (κ-Fam ±± (pj2 (>><< p) x')) (h x'))
                    lm2g : (Fxx v • ap (κ-Fam ±± pj1 (>><< p)) x') ‣ (ap (κ-Fam ±± (pj2 (>><< p) x')) (h x'))
                           ≐
                          (Fxx v • y) ‣ (ap (κ-Fam ±± r) (h (ap (κ-Fam ±± -p1) y)))
                    lm2g = traV lm2k lm2l
                    lm2f :  (Fxx u • x') ‣ h x' ≐
                            (Fxx v • y) ‣ (ap (κ-Fam ±± r) (h (ap (κ-Fam ±± -p1) y)))

                    lm2f = traV lm2h lm2g

                in  x' , pairV-ext (e-prop' _ _ (>><< p1) y) lm2f



       lm : sup (# (Ixx u)) (\x ->  < (Ixx u) ‣ x , ((Fxx u) • x) ‣ (h x) >)
            ≐ sup (# (Ixx v)) (\x ->  < (Ixx v) ‣ x , ((Fxx v) • x) ‣ (piV-ext00 {u} {v} p h x) >)
       lm = pair lm1 lm2
   in lm



piV-half-eqV : (u v : ||| Par VV κ-Fam |||) -> << Par VV κ-Fam >> u ~ v ->  piV-op u ≤ piV-op v
piV-half-eqV u v p = let  lm1 :  (h : # (piV (Ixx u) (Fxx u))) ->
                                         Σ (# (piV (Ixx v) (Fxx v)))
                                           (\k ->
                                            (piV (Ixx u) (Fxx u) ‣ h ≐ (piV (Ixx v) (Fxx v)) ‣ k))
                          lm1 h = piV-ext0-map u v p h , piV-half-ext-lm u v p h
                     in lm1

piV-half-ext : (u v : ||| Par VV κ-Fam |||) -> << Par VV κ-Fam >> u ~ v ->  piV-op u ⊆ piV-op v
piV-half-ext u v p = half-eqV-to-inclusion _ _ (piV-half-eqV u v p)

piV-ext : (u v : ||| Par VV κ-Fam |||) -> << Par VV κ-Fam >> u ~ v -> << VV >>  piV-op u ~ piV-op v
piV-ext u v p =  <<>> (extensional-eqV (piV-op u) (piV-op v)
                                 (piV-half-ext u v p)
                                 (piV-half-ext v u (sym' {Par VV κ-Fam} {u} {v} p)))


piVV : setoidmap11 (Par VV κ-Fam) VV
piVV = record { op = piV-op ; ext = piV-ext }


{--
--}
