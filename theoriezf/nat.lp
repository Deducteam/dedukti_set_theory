require open zf.theoriezf.logic;

constant symbol nat : Set;
symbol zero : El nat;
symbol s : El nat → El nat;

symbol one ≔ s zero;
symbol two ≔ s one;
symbol three ≔ s two;

symbol eqNP : El nat → El nat → El prop;
rule π(eqNP $x $y) ↪ Π (P : El nat → El prop), π (P $x ⇒ P $y);

constant symbol Peano3 : Π (x y: El nat), π((eqNP (s x) (s y)) ⇒ (eqNP x y));
constant symbol Peano4 : Π (x : El nat), π(¬(eqNP (s x) zero));

constant symbol recN : Π (P : El nat → El prop),
π(P zero) 
→ π(`∀ x, (P x) ⇒ (P (s x)))
→ π(`∀ x, (P x));

opaque symbol lemmaNP : Π (x : El nat), π(eqNP x x) 
≔ begin
assume x P Px;
refine Px
end;

opaque symbol lemmaSymNP : Π (x y : El nat), π((eqNP x y) ⇒ (eqNP y x)) 
≔ begin
assume x y;
simplify;
assume Pxy P;
refine Pxy (λ z, (P z) ⇒ (P x)) _;
assume Px;
refine Px
end;

opaque symbol lemmaTransNP : Π (x y z: El nat), π(((eqNP x y) ∧ (eqNP y z)) ⇒ (eqNP x z))
≔ begin
assume x y z Pxyz P Px;
refine (and_ed _ _ Pxyz) P ((and_eg _ _ Pxyz) P Px)
end;

opaque symbol eqNPor : Π (x y : El nat), π((eqNP x y) ∨ (¬(eqNP x y)))
≔ begin
refine recN _ _ _
{refine recN _ _ _
//Cas x = 0, y = 0
{refine or_ig _ _ _;
simplify;
assume P Pz;
refine Pz}
//Cas x = 0, s y
{assume x Px;
refine or_id _ _ _;
assume H0;
refine Peano4 x _;
refine lemmaSymNP zero (s x) H0;
assume x Hx}}
{refine recN _ _ _
//Cas s x, y = 0
{refine or_id _ _ _;
refine Peano4 x}
//Cas s x, s y
{assume y Hrec;
refine or_e _ _ _ (Hx y) _ _
{assume Hxy;
refine or_ig _ _ _;
refine Hxy (λ z, eqNP (s x) (s z)) _;
refine lemmaNP (s x)}
{assume Hxy;
refine or_id _ _ _;
assume Hsxsy;
refine Hxy _;
refine Peano3 x y Hsxsy}}}
end;
