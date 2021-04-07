require open zf.theoriezf.logique;
require open zf.theoriezf.lemme1_6;
require open zf.theoriezf.lemme7_13;
require open zf.theoriezf.lemme14_18;
require open zf.theoriezf.lemme19_21;
require open zf.theoriezf.lemme22_27;
//require open zf.theoriezf.lemme28_34;
//require open zf.theoriezf.lemme35_41;
//require open zf.theoriezf.lemme42_45;
require open zf.theoriezf.nat;

constant symbol formula : Set;
constant symbol eqF : El Nat → El Nat → El formula;
constant symbol inF : El Nat → El Nat → El formula;
constant symbol andF : El formula → El formula → El formula;
constant symbol orF : El formula → El formula → El formula;
constant symbol qF : (El Nat → El formula) → El formula;

symbol if : El Nat → Graph → Graph → Graph;
rule if zero $g1 $g2 ↪ $g2;
rule if (s zero) $g1 $g2 ↪ $g1;



constant symbol recF : Π (P : El formula → Prop), 
π(∀ Nat (λ x, ∀ Nat (λ y, P (eqF x y))))
→ π(∀ Nat (λ x, ∀ Nat (λ y, P (inF x y))))
→ π(∀ formula (λ f, ∀ formula (λ g, (P f ∧ P g) ⇒ (P (andF f g)))))
→ π(∀ formula (λ f, ∀ formula (λ g, (P f ∨ P g) ⇒ (P (orF f g)))))
→ π(∀ formula (λ f, P f));

symbol interpretation : (El Nat → Graph) → El formula → Prop;
rule interpretation $σ (eqF $x $y) ↪ ($σ $x) simeq ($σ $y);
rule interpretation $σ (inF $x $y) ↪ ($σ $x) ∈ ($σ $y);
rule interpretation $σ (andF $f $g) ↪ (interpretation $σ $f) ∧ (interpretation $σ $g);
rule interpretation $σ (orF $f $g) ↪ (interpretation $σ $f) ∨ (interpretation $σ $g);

symbol update : (El Nat → Graph) → El Nat → Graph → (El Nat → Graph);
rule update $σ $x $a $y ↪ if (eqN $x $y) $a ($σ $y);

constant symbol axiom1 : Π (σ : El Nat → Graph), Π (x y : El Nat), Π (a : Graph), π((((eqNP (eqN x y) (s zero)) ⇒ (((update σ x a) y) simeq a))) ∧ ((eqNP (eqN x y) zero) ⇒ (((update σ x a) y) simeq (σ y))));
constant symbol axiom2 : Π (x y : El Nat), π((eqNP (eqN x y) (s zero)) ∨ (eqNP (eqN x y) zero));

opaque symbol lemme32 : Π (a b : Graph), Π (σ : El Nat → Graph), Π (z : El Nat), Π (f : El formula), π(((interpretation (update σ z a) f) ∧ (a simeq b)) ⇒ (interpretation (update σ z b) f))
≔ begin
assume a b σ z;
apply recF (λ f, ((interpretation (update σ z a) f) ∧ (a simeq b)) ⇒ (interpretation (update σ z b) f));
assume x y Heq;
apply or_e _ _ _ (axiom2 z x);
apply or_e _ _ _ (axiom2 z y);
assume Hy Hx;
apply lemme5 (update σ z b x) b (update σ z b y) (and_i _ _ _ _);
apply (and_eg _ _ (axiom1 σ z x b)) Hx;
apply lemme4 (update σ z b y) b ((and_eg _ _ (axiom1 σ z y b)) Hy);
assume Hy Hx;
apply lemme5 (update σ z b x) b (update σ z b y) (and_i _ _ _ _);
apply (and_eg _ _ (axiom1 σ z x b)) Hx;
apply lemme5 b a (update σ z b y) (and_i _ _ (lemme4 a b (and_ed _ _ Heq)) _);
apply lemme5 a (update σ z a x) (update σ z b y) (and_i _ _ _ _);
apply lemme4 (update σ z a x) a ((and_eg _ _ (axiom1 σ z x a)) Hx);
apply lemme5 (update σ z a x) (update σ z a y) (update σ z b y) (and_i _ _ (and_eg _ _ Heq) _);
apply lemme5 (update σ z a y) (σ y) (update σ z b y) (and_i _ _ _ _);
apply (and_ed _ _ (axiom1 σ z y a)) Hy;
apply lemme4 (update σ z b y) (σ y) ((and_ed _ _ (axiom1 σ z y b)) Hy);
apply or_e _ _ _ (axiom2 z y);
assume Hy Hx;
end;




/* Anciennes versions
//constant symbol axiom : Π (σ : El Nat → Graph), Π (x y : El Nat), Π (a : Graph), π((((eqNP (eqN x y) (s zero)) ∧ (((update σ x a) y) simeq a))) ∨ ((eqNP (eqN x y) zero) ∧ (((update σ x a) y) simeq (σ y))));
apply or_e _ _ _ (axiom σ z x b);
apply or_e _ _ _ (axiom σ z y b);
assume Hy Hx;
apply lemme5 (update σ z b x) b (update σ z b y) (and_i _ _ (and_ed _ _ Hx) (lemme4 (update σ z b y) b (and_ed _ _ Hy)));
assume Hy Hx;
apply lemme5 (update σ z b x) a (update σ z b y) (and_i _ _ _ _);
apply lemme5 (update σ z b x) b a (and_i _ _ (and_ed _ _ Hx) (lemme4 a b (and_ed _ _ Heq)));
apply lemme5 a (σ y) (update σ z b y) (and_i _ _ _ (lemme4 (update σ z b y) (σ y) (and_ed _ _ Hy)));
apply and_eg _ _ Heq;
end;

apply lemme3 b;
assume x y Hin;
apply ExElim n _ (and_eg _ _ Hin) _;
assume z Hz;
apply ExElim relat _ (and_ed _ _ Hin) _;
assume r Hr;
apply ExElim n _ ((and_ed _ _ (and_eg _ _ Hr)) (root a) z (root b) _) _;
apply and_i _ _ (and_eg _ _ Hz) (and_eg _ _ (and_eg _ _ Hr));
assume u Hu;
apply ExIntro n u _ _ ;
apply and_i;
apply and_eg _ _ Hu;
apply lemme5 b a (cr b u) (and_i _ _ (lemme4 a b (and_ed _ _ Hin)) _);
apply lemme5 a (cr a z) (cr b u) (and_i _ _ (and_ed _ _ Hz) _);
apply ExIntro relat r _ _;
apply and_i;
apply and_i;
apply and_ed _ _ Hu;
apply and_ed _ _ (and_eg _ _ Hr);
apply and_ed _ _ Hr;
assume f g Hfg Hand;
apply and_i;
apply (and_eg _ _ Hfg) (and_i _ _ (and_eg _ _ (and_eg _ _ Hand)) (and_ed _ _ Hand));
apply (and_ed _ _ Hfg) (and_i _ _ (and_ed _ _ (and_eg _ _ Hand)) (and_ed _ _ Hand));
assume f g Hfg Hor;
apply or_e _ _ _ Hfg;
assume Hf;
apply or_e _ _ _ (and_eg _ _ Hor);
assume Hfor;
apply or_ig;
apply Hf (and_i _ _ Hfor (and_ed _ _ Hor));
*/

