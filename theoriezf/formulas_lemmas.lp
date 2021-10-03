require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.lemmas1_6;
require open zf.theoriezf.lemmas7_13;
require open zf.theoriezf.lemmas14_18;
require open zf.theoriezf.lemmas19_21;
require open zf.theoriezf.lemmas28_34;
require open zf.theoriezf.formulas;
require open zf.theoriezf.nat;

opaque symbol lemmaUpdate1_1 : Π (σ : El nat → Graph), Π (a : Graph), Π (z x: El nat), π((update1 σ x a x z) simeq a)
≔ begin
assume σ a z;
apply recN _;
apply lemma3 a;
assume x Hx;
simplify update1;
apply Hx;
end;

opaque symbol lemmaUpdate1_2 : Π (σ : El nat → Graph), Π (a : Graph), Π (z x y: El nat), π((¬ (eqNP x y)) ⇒ ((update1 σ x a y z) simeq (σ z)))
≔ begin
assume σ a z;
apply recN _;
apply recN _;
//Cas x = 0, y = 0
assume H0;
apply f_e _ _;
apply H0 _;
assume P P0;
apply P0;
//Cas x = 0, s y
assume y Hrec Hy;
simplify update1;
apply lemma3 (σ z);
assume x Hx;
apply recN _;
//Cas s x, y = 0
assume H0;
simplify update1;
apply lemma3 (σ z);
//Cas s x, s y
assume y Hrec Hy;
simplify update1;
apply Hx y _;
assume Hxy;
apply Hy _;
apply Hxy (λ z, eqNP (s x) (s z)) _;
apply lemmaNP (s x);
end;

opaque symbol axiom1 : Π (σ : El nat → Graph), Π (x y z: El nat), Π (a : Graph), π(((eqNP x y) ⇒ (((update1 σ x a) y z) simeq a)) ∧ (¬(eqNP x y) ⇒ (((update1 σ x a) y z) simeq (σ z))))
≔ begin
assume σ x y z a;
apply and_i;
assume H0;
apply imp_i (eqNP x y) _ _ _;
assume H;
apply imp_i (eqNP y x) _ _ _;
assume H';
apply H' (λ w, (update1 σ w a y z) simeq a) _;
apply lemmaUpdate1_1 σ a z y;
apply lemmaSymNP x y H0;
apply H0;
assume H1;
apply lemmaUpdate1_2 σ a z x y H1;
end;

opaque symbol lemmaUp : Π (σ : El nat → Graph), Π (x : El nat), Π (a b : Graph), π((a simeq b) ⇒ (∀ nat (λ y, (update σ x a y) simeq (update σ x b y))))
≔ begin
assume σ x a b Hab y;
apply or_e _ _ _ (eqNPor x y);
assume H1;
apply lemma5 (update σ x a y) b (update σ x b y) (and_i _ _ _ _);
apply lemma5 (update σ x a y) a b (and_i _ _ _ Hab);
simplify update;
apply (and_eg _ _ (axiom1 σ x y y a)) H1;
apply lemma4 (update σ x b y) b ((and_eg _ _ (axiom1 σ x y y b)) H1);
assume H0;
apply lemma5 (update σ x a y) (σ y) (update σ x b y) (and_i _ _ _ _);
apply (and_ed _ _ (axiom1 σ x y y a)) H0;
apply lemma4 (update σ x b y) (σ y) ((and_ed _ _ (axiom1 σ x y y b)) H0);
end;

opaque symbol lemmaUp2 : Π (σ : El nat → Graph), Π (x y : El nat), Π (a b c : Graph), π((a simeq b) ⇒ (∀ nat (λ z, (update (update σ x a) y c z) simeq (update (update σ x b) y c z))))
≔ begin
assume σ x y a b c Hab z;
apply or_e _ _ _ (eqNPor y z);
assume H1;
apply lemma5 (update (update σ x a) y c z) c (update (update σ x b) y c z) (and_i _ _ _ _);
simplify update;
apply (and_eg _ _ (axiom1 (update σ x a) y z z c)) H1;
apply lemma4 (update (update σ x b) y c z) c ((and_eg _ _ (axiom1 (update σ x b) y z z c)) H1);
assume H0;
apply lemma5 (update (update σ x a) y c z) (update σ x a z ) (update (update σ x b) y c z) (and_i _ _ _ _);
simplify update;
apply (and_ed _ _ (axiom1 (update σ x a) y z z c)) H0;
apply lemma5 (update σ x a z) (update σ x b z) (update (update σ x b) y c z) (and_i _ _ _ _);
apply lemmaUp σ x a b Hab z;
apply lemma4 (update (update σ x b) y c z) (update σ x b z) ((and_ed _ _ (axiom1 (update σ x b) y z z c)) H0);
end;

opaque symbol lemmaVal : Π (σ σ' : El nat → Graph), Π (x : El nat), Π (c : Graph), π ((∀ nat (λ y, σ y simeq σ' y)) ⇒ (∀ nat (λ z, (update σ x c z) simeq (update σ' x c z))))
≔ begin
assume σ σ' x c H z;
apply or_e _ _ _ (eqNPor x z);
assume H1;
apply imp_i (eqNP x z) _ _ _;
assume H;
apply imp_i (eqNP z x) _ _ _;
assume H';
apply H' (λ w, (update1 σ w c z z) simeq (update1 σ' w c z z)) _;
apply lemma5 (update1 σ z c z z) c (update1 σ' z c z z) (and_i _ _ _ _);
apply (and_eg _ _ (axiom1 σ z z z c)) (lemmaNP z);
apply lemma4 (update1 σ' z c z z) c ((and_eg _ _ (axiom1 σ' z z z c)) (lemmaNP z));
apply lemmaSymNP x z H1;
apply H1;
assume H0;
simplify update;
apply lemma5 (update1 σ x c z z) (σ z) (update1 σ' x c z z) (and_i _ _ _ _);
apply (and_ed _ _ (axiom1 σ x z z c)) H0;
apply lemma5 (σ z) (σ' z) (update1 σ' x c z z) (and_i _ _ _ _);
apply H z;
apply lemma4 (update1 σ' x c z z) (σ' z) ((and_ed _ _ (axiom1 σ' x z z c)) H0);
end;

opaque symbol lemmaInt : Π (f : El formula), π(∀ valuation (λ σ, ∀ valuation (λ σ', ((interpretation σ f) ∧ (∀ nat (λ x, (σ x) simeq (σ' x)))) ⇒ (interpretation σ' f))))
≔ begin
apply recF (λ f, ∀ valuation (λ σ, ∀ valuation (λ σ', ((interpretation σ f) ∧ (∀ nat (λ x, (σ x) simeq (σ' x)))) ⇒ (interpretation σ' f))));
assume x y σ σ' Heq;
simplify interpretation;
apply lemma5 (σ' x) (σ y) (σ' y) (and_i _ _ _ (and_ed _ _ Heq y));
apply lemma5 (σ' x) (σ x) (σ y) (and_i _ _ _ (and_eg _ _ Heq));
apply lemma4 (σ x) (σ' x) (and_ed _ _ Heq x);
assume x y σ σ' Hin;
apply lemma31 (σ' x) (σ y) (σ' y) (and_i _ _ _ (and_ed _ _ Hin y));
apply lemma30 (σ x) (σ y) (σ' x) (and_i _ _ (and_eg _ _ Hin) (and_ed _ _ Hin x));
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
assume f g Hfg σ σ' Himp Hf;
apply (and_ed _ _ Hfg σ σ') (and_i _ _ _ (and_ed _ _ Himp));
apply and_eg _ _ Himp _;
apply (and_eg _ _ Hfg σ' σ) (and_i _ _ Hf _);
assume x;
apply lemma4 (σ x) (σ' x) (and_ed _ _ Himp x);
assume f Hf x σ σ' Hall c;
apply Hf (update σ x c) (update σ' x c) (and_i _ _ (and_eg _ _ Hall c) _);
apply lemmaVal σ σ' x c (and_ed _ _ Hall);
assume f Hf x σ σ' Hex;
apply ExElim g _ (and_eg _ _ Hex) _;
assume c Hc;
apply ExIntro g c _ _;
apply Hf (update σ x c) (update σ' x c) (and_i _ _ Hc _);
apply lemmaVal σ σ' x c (and_ed _ _ Hex);
assume σ σ' H;
apply and_eg _ _ H;
assume σ σ' H;
apply and_eg _ _ H;
end;
