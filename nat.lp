require open Logic.Z.logic;

constant symbol nat : Set;
symbol zero : El nat;
symbol s : El nat → El nat;

symbol one ≔ s zero;
symbol two ≔ s one;
symbol three ≔ s two;

constant symbol Peano3 : Π (x y: El nat), π(((s x) = (s y)) ⇒ (x = y));
constant symbol Peano4 : Π (x : El nat), π(¬((s x) = zero));

constant symbol recN : Π (P : El nat → El prop),
π(P zero) 
→ π(`∀ x, (P x) ⇒ (P (s x)))
→ π(`∀ x, (P x));

opaque symbol eqNPor : Π (x y : El nat), π((x = y) ∨ (¬(x = y)))
≔ begin
refine recN _ _ _
{refine recN _ _ _
//Cas x = 0, y = 0
{refine or_il _ _ _;
simplify;
assume P Pz;
refine Pz}
//Cas x = 0, s y
{assume x Px;
refine or_ir _ _ _;
assume H0;
refine Peano4 x _;
refine sym nat zero (s x) H0}}
{assume x Hx;
refine recN _ _ _
//Cas s x, y = 0
{refine or_ir _ _ _;
refine Peano4 x}
//Cas s x, s y
{assume y Hrec;
refine or_e _ _ _ (Hx y) _ _
{assume Hxy;
refine or_il _ _ _;
refine Hxy (λ z, (s x) = (s z)) _;
refine refl nat (s x)}
{assume Hxy;
refine or_ir _ _ _;
assume Hsxsy;
refine Hxy _;
refine Peano3 x y Hsxsy}}}
end;
