require open zf.theoriezf.logique;
require open zf.theoriezf.lemme1_6;
require open zf.theoriezf.lemme7_13;
require open zf.theoriezf.lemme14_18;
require open zf.theoriezf.lemme19_21;
require open zf.theoriezf.lemme22_27;
require open zf.theoriezf.lemme28_34;
//require open zf.theoriezf.lemme35_41;
//require open zf.theoriezf.lemme42_45;
require open zf.theoriezf.nat;

constant symbol formula : Set;
constant symbol eqF : El Nat → El Nat → El formula;
constant symbol inF : El Nat → El Nat → El formula;
constant symbol andF : El formula → El formula → El formula;
constant symbol orF : El formula → El formula → El formula;
constant symbol qF : El Nat → El formula → El formula;

symbol if : El Nat → Graph → Graph → Graph;
rule if zero $g1 $g2 ↪ $g2;
rule if (s zero) $g1 $g2 ↪ $g1;

constant symbol recF : Π (P : El formula → Prop), 
π(∀ Nat (λ x, ∀ Nat (λ y, P (eqF x y))))
→ π(∀ Nat (λ x, ∀ Nat (λ y, P (inF x y))))
→ π(∀ formula (λ f, ∀ formula (λ g, (P f ∧ P g) ⇒ (P (andF f g)))))
→ π(∀ formula (λ f, ∀ formula (λ g, (P f ∧ P g) ⇒ (P (orF f g)))))
→ π(∀ formula (λ f, (P f) ⇒ (∀ Nat (λ x, P (qF x f)))))
→ π(∀ formula (λ f, P f));

symbol interpretation : (El Nat → Graph) → El formula → Prop;
rule interpretation $σ (eqF $x $y) ↪ ($σ $x) simeq ($σ $y);
rule interpretation $σ (inF $x $y) ↪ ($σ $x) ∈ ($σ $y);
rule interpretation $σ (andF $f $g) ↪ (interpretation $σ $f) ∧ (interpretation $σ $g);
rule interpretation $σ (orF $f $g) ↪ (interpretation $σ $f) ∨ (interpretation $σ $g);

symbol update : (El Nat → Graph) → El Nat → Graph → (El Nat → Graph);
rule update $σ $x $a $y ↪ if (eqN $x $y) $a ($σ $y);

rule interpretation $σ (qF $x $f) ↪ ∀ g (λ a, interpretation (update $σ $x a) $f);

opaque symbol lemmeSymNP : Π (x y : El Nat), π((eqNP x y) ⇒ (eqNP y x)) 
≔ begin
assume x y;
simpl;
assume Pxy P;
apply Pxy (λ z, (P z) ⇒ (P x));
assume Px;
apply Px;
end;

opaque symbol axiom1 : Π (σ : El Nat → Graph), Π (x y : El Nat), Π (a : Graph), π((((eqNP (eqN x y) (s zero)) ⇒ (((update σ x a) y) simeq a))) ∧ ((eqNP (eqN x y) zero) ⇒ (((update σ x a) y) simeq (σ y))))
≔ begin
assume σ x y a;
apply and_i;
assume H0;
simpl update;
apply imp_i (eqNP (eqN x y) (s zero)) _ _ _;
assume H;
apply imp_i (eqNP (s zero) (eqN x y)) _ _ _;
assume H';
apply H' (λ w, (if w a (σ y)) simeq a) _;
apply lemme3 a;
apply lemmeSymNP (eqN x y) (s zero) H0;
apply H0;
assume H1;
simpl update;
apply imp_i (eqNP (eqN x y) zero) _ _ _;
assume H;
apply imp_i (eqNP zero (eqN x y)) _ _ _;
assume H';
apply H' (λ w, (if w a (σ y)) simeq (σ y)) _;
apply lemme3 (σ y);
apply lemmeSymNP (eqN x y) zero H1;
apply H1;
end;

constant symbol axiom2 : Π (x y : El Nat), π((eqNP (eqN x y) (s zero)) ∨ (eqNP (eqN x y) zero));

opaque symbol lemmeUp : Π (σ : El Nat → Graph), Π (x : El Nat), Π (a b : Graph), π((a simeq b) ⇒ (∀ Nat (λ y, (update σ x a y) simeq (update σ x b y))))
≔ begin
assume σ x a b Hab y;
apply or_e _ _ _ (axiom2 x y);
assume H1;
apply lemme5 (update σ x a y) b (update σ x b y) (and_i _ _ _ _);
apply lemme5 (update σ x a y) a b (and_i _ _ _ Hab);
apply (and_eg _ _ (axiom1 σ x y a)) H1;
apply lemme4 (update σ x b y) b ((and_eg _ _ (axiom1 σ x y b)) H1);
assume H0;
apply lemme5 (update σ x a y) (σ y) (update σ x b y) (and_i _ _ _ _);
apply (and_ed _ _ (axiom1 σ x y a)) H0;
apply lemme4 (update σ x b y) (σ y) ((and_ed _ _ (axiom1 σ x y b)) H0);
end;

opaque symbol lemmeUp2 : Π (σ : El Nat → Graph), Π (x y : El Nat), Π (a b c : Graph), π((a simeq b) ⇒ (∀ Nat (λ z, (update (update σ x a) y c z) simeq (update (update σ x b) y c z))))
≔ begin
assume σ x y a b c Hab z;
apply or_e _ _ _ (axiom2 y z);
assume H1;
apply lemme5 (update (update σ x a) y c z) c (update (update σ x b) y c z) (and_i _ _ _ _);
apply (and_eg _ _ (axiom1 (update σ x a) y z c)) H1;
apply lemme4 (update (update σ x b) y c z) c ((and_eg _ _ (axiom1 (update σ x b) y z c)) H1);
assume H0;
apply lemme5 (update (update σ x a) y c z) (update σ x a z ) (update (update σ x b) y c z) (and_i _ _ _ _);
apply (and_ed _ _ (axiom1 (update σ x a) y z c)) H0;
apply lemme5 (update σ x a z) (update σ x b z) (update (update σ x b) y c z) (and_i _ _ _ _);
apply lemmeUp σ x a b Hab z;
apply lemme4 (update (update σ x b) y c z) (update σ x b z) ((and_ed _ _ (axiom1 (update σ x b) y z c)) H0);
end;

symbol valuation : Set;
rule El valuation ↪ El Nat → El g;

opaque symbol lemmeInt : Π (f : El formula), π(∀ valuation (λ σ, ∀ valuation (λ σ', ((interpretation σ f) ∧ (∀ Nat (λ x, (σ x) simeq (σ' x)))) ⇒ (interpretation σ' f))))
≔ begin
apply recF (λ f, ∀ valuation (λ σ, ∀ valuation (λ σ', ((interpretation σ f) ∧ (∀ Nat (λ x, (σ x) simeq (σ' x)))) ⇒ (interpretation σ' f))));
assume x y σ σ' Heq;
simpl interpretation;
apply lemme5 (σ' x) (σ y) (σ' y) (and_i _ _ _ (and_ed _ _ Heq y));
apply lemme5 (σ' x) (σ x) (σ y) (and_i _ _ _ (and_eg _ _ Heq));
apply lemme4 (σ x) (σ' x) (and_ed _ _ Heq x);
assume x y σ σ' Hin;
apply lemme31 (σ' x) (σ y) (σ' y) (and_i _ _ _ (and_ed _ _ Hin y));
apply lemme30 (σ x) (σ y) (σ' x) (and_i _ _ (and_eg _ _ Hin) (and_ed _ _ Hin x));
assume f g Hfg σ σ' Hand;
apply and_i;
apply (and_eg _ _ Hfg σ σ') (and_i _ _ (and_eg _ _ (and_eg _ _ Hand)) (and_ed _ _ Hand));
apply (and_ed _ _ Hfg σ σ') (and_i _ _ (and_ed _ _ (and_eg _ _ Hand)) (and_ed _ _ Hand));
assume f g Hfg σ σ' Hor;
apply or_e _ _ _ (and_eg _ _ Hor);
assume Hf;
apply or_ig;
apply (and_eg _ _ Hfg σ σ') (and_i _ _ Hf (and_ed _ _ Hor));
assume Hg;
apply or_id;
apply (and_ed _ _ Hfg σ σ') (and_i _ _ Hg (and_ed _ _ Hor));
assume f Hf x σ σ' Hq c;
apply Hf (update σ x c) (update σ' x c) (and_i _ _ (and_eg _ _ Hq c) _);
assume z;
apply or_e _ _ _ (axiom2 x z);
assume H1;
simpl update;
apply imp_i (eqNP (eqN x z) (s zero)) _ _ _;
assume H;
apply imp_i (eqNP (s zero) (eqN x z)) _ _ _;
assume H';
apply H' (λ w, (if w c (σ z)) simeq (if w c (σ' z))) _;
apply lemme3 c;
apply lemmeSymNP (eqN x z) (s zero) H1;
apply H1;
assume H0;
simpl update;
apply imp_i (eqNP (eqN x z) zero) _ _ _;
assume H;
apply imp_i (eqNP zero (eqN x z)) _ _ _;
assume H';
apply H' (λ w, (if w c (σ z)) simeq (if w c (σ' z))) _;
apply and_ed _ _ Hq z;
apply lemmeSymNP (eqN x z) zero H0;
apply H0;
end;

opaque symbol lemme32 : Π (a b : Graph), Π (z : El Nat), Π (f : El formula), π(∀ valuation (λ σ, ((interpretation (update σ z a) f) ∧ (a simeq b)) ⇒ (interpretation (update σ z b) f)))
≔ begin
assume a b z;
apply recF (λ f, ∀ valuation (λ σ, (interpretation (update σ z a) f ∧ (a simeq b)) ⇒ interpretation (update σ z b) f));
assume x y σ Heq;
apply lemme5 (update σ z b x) (update σ z a x) (update σ z b y) (and_i _ _ _ _);
apply lemme4 (update σ z a x) (update σ z b x) (lemmeUp σ z a b (and_ed _ _ Heq) x);
apply lemme5 (update σ z a x) (update σ z a y) (update σ z b y) (and_i _ _ _ _);
apply and_eg _ _ Heq;
apply lemmeUp σ z a b (and_ed _ _ Heq) y;
assume x y σ Hin;
apply lemme31 (update σ z b x) (update σ z a y) (update σ z b y) (and_i _ _ _ _);
apply lemme30 (update σ z a x) (update σ z a y) (update σ z b x) (and_i _ _ _ _);
apply and_eg _ _ Hin;
apply lemmeUp σ z a b (and_ed _ _ Hin) x;
apply lemmeUp σ z a b (and_ed _ _ Hin) y;
assume f g Hfg σ Hand;
apply and_i;
apply ((and_eg _ _ Hfg) σ) (and_i _ _ (and_eg _ _ (and_eg _ _ Hand)) (and_ed _ _ Hand));
apply ((and_ed _ _ Hfg) σ) (and_i _ _ (and_ed _ _ (and_eg _ _ Hand)) (and_ed _ _ Hand));
assume f g Hfg σ Hor;
apply or_e _ _ _ (and_eg _ _ Hor);
assume Hf;
apply or_ig;
apply ((and_eg _ _ Hfg) σ) (and_i _ _ Hf (and_ed _ _ Hor));
assume Hg;
apply or_id;
apply ((and_ed _ _ Hfg) σ) (and_i _ _ Hg (and_ed _ _ Hor));
assume f Hf x σ Heq c;
apply lemmeInt f (update (update σ z a) x c) (update (update σ z b) x c) (and_i _ _ _ _);
apply (and_eg _ _ Heq) c;
apply (lemmeUp2 σ z x a b c) (and_ed _ _ Heq);
end;
