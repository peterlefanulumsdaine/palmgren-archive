-- disable the K axiom:


{-# OPTIONS --without-K #-}


-- Agda version 2.5.2


module V-model-epi-rules where

open import basic-types
open import basic-setoids       
open import dependent-setoids   
open import subsetoids          
open import iterative-sets      
open import iterative-sets-pt2  
open import iterative-sets-pt3  
open import iterative-sets-pt4
open import iterative-sets-pt5-wop -- wop = use universe operator and W
open import iterative-sets-pt6-wop
open import V-model-pt0
open import V-model-pt1         
open import V-model-pt2         
open import V-model-pt3         
open import V-model-pt4         
open import V-model-pt5         
open import V-model-pt6         
open import V-model-pt7         
open import V-model-pt8         
open import V-model-pt9         
open import V-model-pt10
open import V-model-pt13-wop
open import V-model-pt11-wop

open import V-model-all-rules-wop

-- 

-- ⊢ 


ty-substr-lm-ref : {Γ : ctx}
  -> (A : ty Γ)
  -> (p : << Ctx >> Γ ~ Γ)
  -> Γ ==> A == A [[ subst-trp p ]]
ty-substr-lm-ref {Γ} A p =  
  let lm =  >><< (Sub-trp-prop {Γ} A p)
  in tysym (mk-eqty (>><< lm))


ty-substr-lm-sym : {Δ Γ : ctx}
  -> (A : ty Δ)
  -> (B : ty Γ)
  -> (p : << Ctx >> Δ ~ Γ)
  -> (Δ ==> A == B [[ subst-trp p ]])
  -> Γ ==> B == A [[ subst-trp (sym' p) ]]
ty-substr-lm-sym {Δ} {Γ} A B p eq =
  let lm :  Δ ==> (B [[ subst-trp p ]]) == A
      lm = tysym eq
      lm2 :  Γ ==> (B [[ subst-trp p ]])  [[ subst-trp (sym' p) ]] == A  [[ subst-trp (sym' p) ]]
      lm2 = tyeq-subst (subst-trp (sym' p)) lm
      lm4 : Γ ==> B == (B [ ids ])
      lm4 = tysym (tysubst-id B)
      lm5 : Γ ==> ((B [[ subst-trp p ]]) [[ subst-trp (sym' p) ]]) == B [ (subst-trp p) ⌢ (subst-trp (sym' p)) ]
      lm5 = tysym (tysubst-com B (subst-trp p) (subst-trp (sym' p)))
      lm6 : < Subst Γ Γ > ids ~ ((subst-trp p) ⌢ (subst-trp (sym' p)))
      lm6 = sym (tra (subst-trp-fun (sym' p) p (tra' (sym' p) p)) (subst-trp-id (tra' (sym' p) p)))
      lm7 : Γ ==> B == (B [[ subst-trp p ]]) [[ subst-trp (sym' p) ]]
      lm7 = tytra lm4 (tytra (tyeq-subst2 B ids ((subst-trp p) ⌢ (subst-trp (sym' p))) lm6) (tysym lm5))
  in tytra lm7 lm2



ty-substr-lm-tra : {Δ Γ H : ctx}
  -> (A : ty Δ)
  -> (B : ty Γ)
  -> (C : ty H)
  -> (p : << Ctx >> Δ ~ Γ)
  -> (q : << Ctx >> Γ ~ H)
  -> (Δ ==> A == B [[ subst-trp p ]])
  -> (Γ ==> B == C [[ subst-trp q ]])
  -> Δ ==> A == C [[ subst-trp (tra' p q) ]]
ty-substr-lm-tra {Δ} {Γ} {H} A B C p q eq1 eq2 = 
  let lm :  Δ ==> (B [[ subst-trp p ]]) == (C  [[ subst-trp q ]] [[ subst-trp p ]])
      lm = tyeq-subst (subst-trp p) eq2
      lm2 : Δ ==> A == (C  [[ subst-trp q ]] [[ subst-trp p ]])
      lm2 = tytra eq1 lm
      lm3 : Δ ==> (C [[ subst-trp q ]]) [[ subst-trp p ]] == C [[ (subst-trp q) ⌢ (subst-trp p) ]]
      lm3 = tysym (tysubst-com C (subst-trp q)  (subst-trp p))
      lm4 : < Subst Δ H > (subst-trp q ⌢ subst-trp p) ~ (subst-trp (tra' p q))
      lm4 = subst-trp-fun p q (tra' p q)
      lm5 :  < Subst Δ H > subst-trp q ⌢ subst-trp p ~ subst-trp (tra' p q)
      lm5 = subst-trp-fun p q (tra' p q)
      lm6 : Δ ==> (C [[ subst-trp q ]]) [[ subst-trp p ]] == C [[ subst-trp (tra' p q) ]]
      lm6 = tytra lm3 (tyeq-subst2 C (subst-trp q ⌢ subst-trp p) (subst-trp (tra' p q)) lm5) 
  in tytra lm2 lm6



ty-substr-lm-irr : {Δ Γ : ctx}
  -> (A : ty Γ)
  -> (p  q : << Ctx >> Δ ~ Γ)
  -> Δ ==> A [[ subst-trp p ]] == A [[ subst-trp q ]]
ty-substr-lm-irr {Δ} {Γ} A p q = tyeq-subst2 A (subst-trp p) (subst-trp q) (subst-trp-irr _ _)


ty-substr-lm-fun : {H Δ Γ : ctx}
  -> (A : ty Γ)
  -> (p : << Ctx >> Δ ~ Γ)
  -> (q : << Ctx >> H ~ Δ)
  -> H ==> (A [[ subst-trp p ]]) [[ subst-trp q ]] == (A [[ subst-trp (tra' q p) ]])
ty-substr-lm-fun {Δ} {Γ} A p q = 
          tytra (tysym (tysubst-com A (subst-trp p) (subst-trp q))) 
                (tyeq-subst2 A (subst-trp p ⌢ subst-trp q)  (subst-trp (tra' q p)) 
                               (subst-trp-fun q p (tra' q p)))



ty-substr-lm-inv : {Δ Γ : ctx}
  -> (A : ty Γ)
  -> (p : << Ctx >> Δ ~ Γ)
  -> Γ ==> (A [[ subst-trp p ]]) [[ subst-trp (sym' p) ]] == A
ty-substr-lm-inv {Δ} {Γ} A p = tytra (ty-substr-lm-fun A p (sym' p)) (tysym (ty-substr-lm-ref A (tra' (sym' p) p)))


-- types and elements in context



data ty-in-ctx : Set1 where
  _⊢_ : (ct : ctx) -> (ty ct) ->  ty-in-ctx 

data el-in-ctx : Set1 where
  _⊢_ : (ct : ctx) -> (raw ct) ->  el-in-ctx 


 {--
Γ ⊢ a
Γ ⊢ A

(Γ ⊢ a) ≈ (Γ' ⊢ a')
(Γ ⊢ a)  ::: (Γ' ⊢ A)
(Γ ⊢ A) ≈ (Γ' ⊢ A')
--}



ty-in-ctx-eq :  (u v : ty-in-ctx) -> Set
ty-in-ctx-eq (Γ ⊢ A) (Γ' ⊢ A') = Σ (<< Ctx >> Γ ~ Γ') 
                     (\p -> Γ ==> A ==  (A' [[ subst-trp p ]]) )  

rf-ty-in-ctx-eq :  (u : ty-in-ctx) 
      -> ty-in-ctx-eq u u
rf-ty-in-ctx-eq (Γ ⊢ A) = (refl' Ctx _) , ty-substr-lm-ref {Γ} A (refl' Ctx Γ) 

sy-ty-in-ctx-eq :  (u  v : ty-in-ctx) 
      -> ty-in-ctx-eq u v 
      -> ty-in-ctx-eq v u
sy-ty-in-ctx-eq (Γ ⊢ A) (Γ' ⊢ A') (p1 , p2) =
  let lm = ty-substr-lm-sym {Γ} {Γ'} A A' p1
  in
      (sym' p1) , lm p2

tr-ty-in-ctx-eq :  (u v z : ty-in-ctx) 
      -> ty-in-ctx-eq u v -> ty-in-ctx-eq v z 
      -> ty-in-ctx-eq u z
tr-ty-in-ctx-eq  (Γ ⊢ A) (Γ' ⊢ A') (Γ'' ⊢ A'')  (p1 , p2) (q1 , q2) =
  let lm = ty-substr-lm-tra {Γ} {Γ'}  {Γ''}  A A' A'' p1 q1
  in
      (tra' p1 q1) , lm p2 q2

Ty-in-ctx : classoid
Ty-in-ctx = record { object = ty-in-ctx 
                   ; _∼_ = ty-in-ctx-eq 
                   ; eqrel = record { rf' = rf-ty-in-ctx-eq 
                                    ; sy' = sy-ty-in-ctx-eq 
                                    ; tr' = tr-ty-in-ctx-eq 
                                    } 
                   }


infix 5 _≈_

_≈_ : ||| Ty-in-ctx ||| ->  ||| Ty-in-ctx ||| -> Set
A ≈ B = (<< Ty-in-ctx >> A  ~  B)





-- terms-in-context

-- move this :

raw-subst-ext1 : {Δ Γ : ctx} 
     -> (a b : raw Γ)
     -> (f : subst Δ Γ) 
     -> << Raw Γ >> a ~ b
     -> << Raw Δ >> a [ f ] ~ (b [ f ])
raw-subst-ext1 {Δ} {Γ} a  b f p = 
    <<>> (<<>> (λ x → let lm1 = >><< (>><< p) (aps f x)
                          lm :  << VV >> raw.rawterm (a [ f ]) • x ~  (raw.rawterm (b [ f ]) • x)
                          lm = <<>> (>><< lm1)
                       in lm
         ))


raw-subst-ext2 : {Δ Γ : ctx} 
     -> (a : raw Γ)
     -> (f g : subst Δ Γ) 
     -> < Subst Δ Γ > f ~ g
     -> << Raw Δ >> a [ f ] ~ (a [ g ])
raw-subst-ext2 {Δ} {Γ} a f g p = <<>> (<<>> (λ x → extensionality1 (raw.rawterm a) (aps f x) (aps g x) (>< (>< p) x)))



raw-substr-lm-ref : {Γ : ctx}
  -> (a : raw Γ)
  -> (p : << Ctx >> Γ ~ Γ)
  -> << Raw Γ >> a ~ (a [ subst-trp p ])
raw-substr-lm-ref {Γ} a p = sym' (sub-trp-prop a p)



raw-substr-lm-sym : {Δ Γ : ctx}
  -> (a : raw Δ)
  -> (b : raw Γ)
  -> (p : << Ctx >> Δ ~ Γ)
  -> (<< Raw Δ >> a ~ (b [ subst-trp p ]))
  -> << Raw Γ >> b ~ (a [ subst-trp (sym' p) ])
raw-substr-lm-sym {Δ} {Γ} a b p eq = 
   let lm : << Raw Γ >> a [ subst-trp (sym' p) ] ~ (b [ subst-trp p ]  [ subst-trp (sym' p) ])
       lm = raw-subst-ext1 a (b [ subst-trp p ]) (subst-trp (sym' p)) eq
       lm1 :  << Raw Γ >> b [  (subst-trp p) ⌢ (subst-trp (sym' p)) ]
                           ~ ((b [ subst-trp p ]) [ subst-trp (sym' p) ])
       lm1 = sub-comp-prop b (subst-trp p) (subst-trp (sym' p))
       lm2 : << Raw Γ >> b [ subst-trp (tra' (sym' p) p) ] ~ b
       lm2 = sub-trp-prop b (tra' (sym' p) p)
       lm3 : < Subst Γ Γ >  subst-trp (tra' (sym' p) p)  ~  (subst-trp p ⌢ subst-trp (sym' p))
       lm3 = sym (subst-trp-fun (sym' p) p  (tra' (sym' p) p))
       lm4 :  << Raw Γ >> (b [ subst-trp p ]) [ subst-trp (sym' p) ] ~ b
       lm4 = tra' (sym' 
                  (tra' (raw-subst-ext2 b (subst-trp (tra' (sym' p) p)) ((subst-trp p ⌢ subst-trp (sym' p))) lm3) 
                         lm1)) 
                  lm2
   in sym' (tra' lm lm4)
 


raw-substr-lm-tra : {Δ Γ H : ctx}
  -> (a : ty Δ)
  -> (b : ty Γ)
  -> (c : ty H)
  -> (p : << Ctx >> Δ ~ Γ)
  -> (q : << Ctx >> Γ ~ H)
  -> (<< Raw Δ >> a ~ (b [ subst-trp p ]))
  -> (<< Raw Γ >> b ~ (c [ subst-trp q ]))
  -> << Raw Δ >> a ~ (c [ subst-trp (tra' p q) ])
raw-substr-lm-tra {Δ} {Γ} {H} a b c p q eq1 eq2 =  
   let
     lm1 :  << Raw Δ >> (b [ subst-trp p ]) ~ ((c [ subst-trp q ]) [ subst-trp p ])
     lm1 = raw-subst-ext1 b (c [ subst-trp q ]) (subst-trp p) eq2
     lm2 : << Raw Δ >> ((c [ subst-trp q ]) [ subst-trp p ]) ~ (c [ subst-trp (tra' p q) ])
     lm2 = tra' (sym' (sub-comp-prop c (subst-trp q) (subst-trp p))) 
                (raw-subst-ext2 c (subst-trp q ⌢ subst-trp p) (subst-trp (tra' p q)) 
                     (subst-trp-fun p q (tra' p q))) 

   in tra' eq1 (tra' lm1 lm2)
 

raw-substr-lm-irr : {Δ Γ : ctx}
  -> (a : ty Γ)
  -> (p  q : << Ctx >> Δ ~ Γ)
  -> << Raw Δ >> a [ subst-trp p ] ~ (a [ subst-trp q ])
raw-substr-lm-irr {Δ} {Γ} a p q = raw-subst-ext2 a (subst-trp p) (subst-trp q) (subst-trp-irr p q) 


el-in-ctx-eq :  (u v : el-in-ctx) -> Set
el-in-ctx-eq (Γ ⊢ a) (Γ' ⊢ a') = Σ (<< Ctx >> Γ ~ Γ') 
                     (\p -> << Raw Γ >> a ~ (a' [[ subst-trp p ]]) )

rf-el-in-ctx-eq :  (u : el-in-ctx) 
      -> el-in-ctx-eq u u
rf-el-in-ctx-eq (Γ ⊢ a) = 
  let lm =  raw-substr-lm-ref {Γ} a  (refl' Ctx _)
  in  (refl' Ctx _) , lm


sy-el-in-ctx-eq :  (u v : el-in-ctx) 
      -> el-in-ctx-eq u v 
      -> el-in-ctx-eq v u
sy-el-in-ctx-eq (Γ ⊢ a) (Γ' ⊢ a') (p1 , p2) =  
  let lm =  raw-substr-lm-sym {Γ} {Γ'} a a' 
  in (sym' p1) , lm p1 p2



tr-el-in-ctx-eq :  (u v z : el-in-ctx) 
      -> el-in-ctx-eq u v -> el-in-ctx-eq v z 
      -> el-in-ctx-eq u z
tr-el-in-ctx-eq (Γ ⊢ a) (Γ' ⊢ a') (Γ'' ⊢ a'') (p1 , p2) (q1 , q2) = 
  let lm =  raw-substr-lm-tra {Γ} {Γ'} {Γ''}
                              a a' a'' 
  in tra' p1 q1 , lm p1 q1 p2 q2


El-in-ctx : classoid
El-in-ctx = record { object = el-in-ctx 
                   ; _∼_ = el-in-ctx-eq 
                   ; eqrel = record { rf' = rf-el-in-ctx-eq 
                                    ; sy' = sy-el-in-ctx-eq 
                                    ; tr' = tr-el-in-ctx-eq 
                                    } 
                    }


infix 5 _≈≈_

_≈≈_ : ||| El-in-ctx ||| ->  ||| El-in-ctx ||| -> Set
A ≈≈ B = (<< El-in-ctx >> A  ~  B)



_:::_ : el-in-ctx -> ty-in-ctx -> Set
(Γ ⊢ a) ::: (Γ' ⊢ A) =  Σ (<< Ctx >> Γ ~ Γ') 
                           (\p -> Γ ==> a :: (A [[ subst-trp p ]]) ) 


::-::: : (Γ : ctx) -> (a : raw Γ) -> (A : ty Γ) -> 
           (Γ ==> a :: A) ->  (Γ ⊢ a) ::: (Γ ⊢ A)
::-::: Γ a A p = (refl' Ctx Γ) , elttyeq p (ty-substr-lm-ref A (refl' Ctx Γ))


:::-:: : (Γ : ctx) -> (a : raw Γ) -> (A : ty Γ) -> 
             (Γ ⊢ a) ::: (Γ ⊢ A) -> (Γ ==> a :: A) 
:::-:: Γ a A (p , q) = elttyeq q (tysym (ty-substr-lm-ref A p))

=::-::: : (Γ : ctx) -> (a b : raw Γ) -> (A : ty Γ) 
       ->  (Γ ==> a == b :: A) 
       -> (and ((Γ ⊢ a) ::: (Γ ⊢ A))  (and  ((Γ ⊢ b) ::: (Γ ⊢ A)) ((Γ ⊢ a) ≈≈ (Γ ⊢ b))))
=::-::: Γ a b A (pair p1 (pair p2 p3)) = 
       let eq :  << Raw Γ >> b ~ (b [[ subst-trp (refl' Ctx Γ) ]])
           eq = sym' (sub-trp-prop b (refl' Ctx Γ))
           lm : (Γ ⊢ a) ≈≈ (Γ ⊢ b)
           lm = <<>> ((refl' Ctx Γ) , tra' (<<>> (<<>> (λ x → <<>> (p1 x)))) eq)
           lm1 : Γ ==> a :: A [[ subst-trp (refl' Ctx Γ) ]]
           lm1 = elttyeq p2 (ty-substr-lm-ref A  (refl' Ctx Γ))
           lm2 : Γ ==> b :: A [[ subst-trp (refl' Ctx Γ) ]]
           lm2 = elttyeq p3  (ty-substr-lm-ref A  (refl' Ctx Γ))
       in  pair ((refl' Ctx Γ) , lm1) (pair (refl' Ctx Γ , lm2) lm)

tyeq-new : 
   {Γ Γ' Γ'' : ctx}
   -> (a : raw Γ)
   -> (A  : ty Γ') 
   -> (B  : ty Γ'') 
   -> (Γ ⊢ a) ::: (Γ' ⊢ A) 
   -> (Γ' ⊢ A) ≈ (Γ'' ⊢ B)
   -> (Γ ⊢ a) ::: (Γ'' ⊢ B) 
tyeq-new {Γ} {Γ'} {Γ''} a A B p q =
   let p1 = pj1 p
       p2 = pj2 p
       q1 = pj1 (>><< q)
       q2 = pj2 (>><< q)
       lm : Γ ==> (A [[ subst-trp (pj1 p) ]]) == (B [[ subst-trp (pj1 (>><< q)) ]]) [[ subst-trp (pj1 p) ]]
       lm = tyeq-subst (subst-trp (pj1 p)) q2 
       lm2 :  Γ ==> (B [[ subst-trp (pj1 (>><< q)) ]]) [[ subst-trp (pj1 p) ]] == B [[ subst-trp (tra' (pj1 p) (pj1 (>><< q))) ]]
       lm2 = tysym (tytra (tyeq-subst2 B 
                              (subst-trp (tra' (pj1 p) (pj1 (>><< q)))) 
                              ((subst-trp (pj1 (>><< q))) ⌢ ( subst-trp (pj1 p)))
                               (sym (subst-trp-fun (pj1 p) (pj1 (>><< q)) (tra' (pj1 p) (pj1 (>><< q)))))) 
                           (tysubst-com B (subst-trp (pj1 (>><< q))) (subst-trp (pj1 p))))
       lm3 :  Γ ==> (A [[ subst-trp (pj1 p) ]]) == B [[ subst-trp (tra' (pj1 p) (pj1 (>><< q))) ]]
       lm3 = tytra lm lm2
    in (tra' p1 q1) , elttyeq p2 lm3



tyeq2-new : 
   {Γ Γ' Γ'' : ctx}
   -> (a : raw Γ)
   -> (b : raw Γ')
   -> (A : ty Γ'') 
   -> (Γ' ⊢ b) ::: (Γ'' ⊢ A) 
   -> (Γ ⊢ a) ≈≈ (Γ' ⊢ b)
   -> (Γ ⊢ a) ::: (Γ'' ⊢ A) 
tyeq2-new {Γ} {Γ'} {Γ''} a b A p q = 
   let p1 = pj1 p
       p2 = pj2 p
       q1 = pj1 (>><< q)
       q2 = pj2 (>><< q)
       lm1 : Γ ==> b  [[ subst-trp (pj1 (>><< q)) ]] :: (A [[ subst-trp (pj1 p) ]]) [[ subst-trp (pj1 (>><< q)) ]]
       lm1 = elt-subst (subst-trp (pj1 (>><< q))) p2
       lm2 : Γ ==> (A [[ subst-trp (pj1 p) ]]) [[ subst-trp (pj1 (>><< q)) ]] 
                      == A [[ subst-trp (tra' (pj1 (>><< q)) (pj1 p)) ]]
       lm2 = ty-substr-lm-fun A (pj1 p) (pj1 (>><< q)) 
       lm3 : Γ ==> a ::  (A [[ subst-trp (pj1 p) ]]) [[ subst-trp (pj1 (>><< q)) ]] 
       lm3 = subj-red  (b [[ subst-trp (pj1 (>><< q)) ]]) a lm1 (sym' q2)
       lm4 : Γ ==> a :: A [[ subst-trp (tra' (pj1 (>><< q)) (pj1 p)) ]]
       lm4 = elttyeq lm3 lm2
    in (tra' q1 p1) , lm4


tyeq3-new : 
   {Δ Γ : ctx}
   -> (A : ty Γ) 
   -> (p :  << Ctx >> Δ ~ Γ)
   -> (Γ ⊢ A) ≈ (Δ ⊢ (A [[ subst-trp p ]]))
tyeq3-new {Δ} {Γ} A p = <<>> ((sym' p) , tysym (ty-substr-lm-inv A p))

tyeq4-new : 
   {Δ Γ : ctx}
   -> (a : raw Γ) 
   -> (p :  << Ctx >> Δ ~ Γ)
   -> (Γ ⊢ a) ≈≈ (Δ ⊢ (a [[ subst-trp p ]]))
tyeq4-new {Δ} {Γ} a p = <<>> ((sym' p) , tra' (sym' (tra' (raw-subst-ext2 a (subst-trp p ⌢ subst-trp (sym' p))
                                                                            (subst-trp (tra' (sym' p) p))
                                                                            (subst-trp-fun (sym' p) p (tra' (sym' p) p)))
                                                          (sub-trp-prop a (tra' (sym' p) p))))
                                              (sub-comp-prop a (subst-trp p) (subst-trp (sym' p))))



-- Some rules written with the new judgement forms.

-- to do: 


P15-Π-f-cong-new : {Γ : ctx}
--
      -> (A  A' : ty Γ) 
      -> (Γ ⊢ A) ≈ (Γ ⊢ A') 
      -> (B : ty (Γ ▷ A))
      -> (B' : ty (Γ ▷ A'))
      -> ((Γ ▷ A) ⊢ B) ≈ ((Γ ▷ A') ⊢ B') 
-- ---------------------
      -> Γ ==> Π-f A B == Π-f A' B'
P15-Π-f-cong-new {Γ} A A' p B B' q =
    let p1 = pj1 (>><< p)
        p2 = pj2 (>><< p)
        lm1 :  Γ ==> A == A'
        lm1 = tytra p2 (tysym (ty-substr-lm-ref A' (pj1 (>><< p))))
        q1 = pj1 (>><< q)
        q2 = pj2 (>><< q)
        

    in P15-Π-f-cong {Γ} A A' lm1 B B' 
         (tytra q2  
               (ty-substr-lm-irr B'  (pj1 (>><< q))  
                                     (ext-eq' A A'
                                          (tytra (pj2 (>><< p))
                                              (tysym (ty-substr-lm-ref A' (pj1 (>><< p))))))) ) 


{--

ty-substr-lm-irr : {Δ Γ : ctx}
  -> (A : ty Γ)
  -> (p  q : << Ctx >> Δ ~ Γ)
  -> Δ ==> A [[ subst-trp p ]] == A [[ subst-trp q ]]


P15-Π-f-cong : {Γ : ctx}
--
      -> (A  A' : ty Γ) 
      -> (p : Γ ==> A == A')
      -> (B : ty (Γ ▷ A))
      -> (B' : ty (Γ ▷ A'))
      -> (Γ ▷ A ==> B == (B' [[  subst-trp (ext-eq' A A' p) ]]))
-- ---------------------
      -> Γ ==> Π-f A B == Π-f A' B'
--
P15-Π-f-cong = Π-f-cong

--}



Sg2-Σ-f-cong-new : {Γ : ctx}
--
      -> (A  A' : ty Γ) 
      -> (Γ ⊢ A) ≈ (Γ ⊢ A') 
      -> (B : ty (Γ ▷ A))
      -> (B' : ty (Γ ▷ A'))
      -> ((Γ ▷ A) ⊢ B) ≈ ((Γ ▷ A') ⊢ B') 
-- ---------------------
      -> Γ ==> Σ-f A B == Σ-f A' B'
Sg2-Σ-f-cong-new {Γ} A A' p B B' q =
    let p1 = pj1 (>><< p)
        p2 = pj2 (>><< p)
        lm1 :  Γ ==> A == A'
        lm1 = tytra p2 (tysym (ty-substr-lm-ref A' (pj1 (>><< p))))
        q1 = pj1 (>><< q)
        q2 = pj2 (>><< q)        

    in Sg2-Σ-f-cong {Γ} A A' lm1 B B' 
         (tytra q2  
               (ty-substr-lm-irr B'  (pj1 (>><< q))  
                                     (ext-eq' A A'
                                          (tytra (pj2 (>><< p))
                                              (tysym (ty-substr-lm-ref A' (pj1 (>><< p))))))) ) 


{--
Sg2-Σ-f-cong : {Γ : ctx}
--
      -> (A  A' : ty Γ) 
      -> (p : Γ ==> A == A')
      -> (B : ty (Γ ▷ A))
      -> (B' : ty (Γ ▷ A'))
      -> (Γ ▷ A ==> B == (B' [[  subst-trp (ext-eq' A A' p) ]]))
-- --------------------------------------------------------------
      -> Γ ==> Σ-f A B == Σ-f A' B'
--
Sg2-Σ-f-cong = Σ-f-cong
--}


