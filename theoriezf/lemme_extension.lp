require open zf.theoriezf.logique;
require open zf.theoriezf.lemme1_6;
require open zf.theoriezf.lemme7_13;
require open zf.theoriezf.lemme14_18;
require open zf.theoriezf.lemme19_21;
//require open zf.theoriezf.lemme22_27;
require open zf.theoriezf.lemme28_34;
//require open zf.theoriezf.lemme35_41;
//require open zf.theoriezf.lemme42_45;
//require open zf.theoriezf.lemme46_51;
require open zf.theoriezf.extension;
require open zf.theoriezf.nat;

opaque symbol lemmeSymNP : Π (x y : El nat), π((eqNP x y) ⇒ (eqNP y x)) 
≔ begin
assume x y;
simpl;
assume Pxy P;
apply Pxy (λ z, (P z) ⇒ (P x));
assume Px;
apply Px;
end;

opaque symbol lemmeNP : Π (x : El nat), π(eqNP x x) 
≔ begin
assume x P Px;
apply Px;
end;

opaque symbol lemmeTransNP : Π (x y z: El nat), π(((eqNP x y) ∧ (eqNP y z)) ⇒ (eqNP x z))
≔ begin
assume x y z Pxyz P Px;
apply (and_ed _ _ Pxyz) P ((and_eg _ _ Pxyz) P Px);
end;

opaque symbol lemmeNegS : Π (x : El nat), π(¬(eqNP (s x) x))
≔ begin
apply recN _;
assume H0;
apply H0;
assume x Hx P;
apply Hx _;
apply P;
end;

opaque symbol lemmeUpdate1_1 : Π (σ : El nat → Graph), Π (a : Graph), Π (z x: El nat), π((update1 σ x a x z) simeq a)
≔ begin
assume σ a z;
apply recN _;
apply lemme3 a;
assume x Hx;
simpl update1;
apply Hx;
end;

opaque symbol lemmeUpdate1_2 : Π (σ : El nat → Graph), Π (a : Graph), Π (z x y: El nat), π((¬ (eqNP x y)) ⇒ ((update1 σ x a y z) simeq (σ z)))
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
simpl update1;
apply lemme3 (σ z);
assume x Hx;
apply recN _;
//Cas s x, y = 0
assume H0;
simpl update1;
apply lemme3 (σ z);
//Cas s x, s y
assume y Hrec Hy;
simpl update1;
apply Hx y _;
assume Hxy;
apply Hy _;
simpl eqNP;
apply Hxy;
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
apply lemmeUpdate1_1 σ a z y;
apply lemmeSymNP x y H0;
apply H0;
assume H1;
apply lemmeUpdate1_2 σ a z x y H1;
end;

opaque symbol axiom2 : Π (x y : El nat), π((eqNP x y) ∨ (¬(eqNP x y)))
≔ begin
apply recN _;
apply recN _;
//Cas x = 0, y = 0
apply or_ig;
simpl;
assume P Pz;
apply Pz;
//Cas x = 0, s y
assume x Px;
apply or_id;
assume H0;
apply lemmeSymNP zero (s x) H0;
assume x Hx;
apply recN _;
//Cas s x, y = 0
apply or_id;
assume H0;
apply H0;
//Cas s x, s y
assume y Hrec;
apply or_e _ _ _ Hrec;
assume H1;
apply or_id;
assume H;
apply lemmeNegS y _;
apply lemmeTransNP (s y) (s x) y (and_i _ _ (lemmeSymNP (s x) (s y) H) H1);
assume H2;
apply or_e _ _ _ (Hx y);
assume H3;
apply or_ig;
simpl;
apply H3;
assume H4;
apply or_id;
assume H;
apply H4 H;
end;

opaque symbol lemmeUp : Π (σ : El nat → Graph), Π (x : El nat), Π (a b : Graph), π((a simeq b) ⇒ (∀ nat (λ y, (update σ x a y) simeq (update σ x b y))))
≔ begin
assume σ x a b Hab y;
apply or_e _ _ _ (axiom2 x y);
assume H1;
apply lemme5 (update σ x a y) b (update σ x b y) (and_i _ _ _ _);
apply lemme5 (update σ x a y) a b (and_i _ _ _ Hab);
simpl update;
apply (and_eg _ _ (axiom1 σ x y y a)) H1;
apply lemme4 (update σ x b y) b ((and_eg _ _ (axiom1 σ x y y b)) H1);
assume H0;
apply lemme5 (update σ x a y) (σ y) (update σ x b y) (and_i _ _ _ _);
apply (and_ed _ _ (axiom1 σ x y y a)) H0;
apply lemme4 (update σ x b y) (σ y) ((and_ed _ _ (axiom1 σ x y y b)) H0);
end;

opaque symbol lemmeUp2 : Π (σ : El nat → Graph), Π (x y : El nat), Π (a b c : Graph), π((a simeq b) ⇒ (∀ nat (λ z, (update (update σ x a) y c z) simeq (update (update σ x b) y c z))))
≔ begin
assume σ x y a b c Hab z;
apply or_e _ _ _ (axiom2 y z);
assume H1;
apply lemme5 (update (update σ x a) y c z) c (update (update σ x b) y c z) (and_i _ _ _ _);
simpl update;
apply (and_eg _ _ (axiom1 (update σ x a) y z z c)) H1;
apply lemme4 (update (update σ x b) y c z) c ((and_eg _ _ (axiom1 (update σ x b) y z z c)) H1);
assume H0;
apply lemme5 (update (update σ x a) y c z) (update σ x a z ) (update (update σ x b) y c z) (and_i _ _ _ _);
simpl update;
apply (and_ed _ _ (axiom1 (update σ x a) y z z c)) H0;
apply lemme5 (update σ x a z) (update σ x b z) (update (update σ x b) y c z) (and_i _ _ _ _);
apply lemmeUp σ x a b Hab z;
apply lemme4 (update (update σ x b) y c z) (update σ x b z) ((and_ed _ _ (axiom1 (update σ x b) y z z c)) H0);
end;

opaque symbol lemmeVal : Π (σ σ' : El nat → Graph), Π (x : El nat), Π (c : Graph), π ((∀ nat (λ y, σ y simeq σ' y)) ⇒ (∀ nat (λ z, (update σ x c z) simeq (update σ' x c z))))
≔ begin
assume σ σ' x c H z;
apply or_e _ _ _ (axiom2 x z);
assume H1;
apply imp_i (eqNP x z) _ _ _;
assume H;
apply imp_i (eqNP z x) _ _ _;
assume H';
apply H' (λ w, (update1 σ w c z z) simeq (update1 σ' w c z z)) _;
apply lemme5 (update1 σ z c z z) c (update1 σ' z c z z) (and_i _ _ _ _);
apply (and_eg _ _ (axiom1 σ z z z c)) (lemmeNP z);
apply lemme4 (update1 σ' z c z z) c ((and_eg _ _ (axiom1 σ' z z z c)) (lemmeNP z));
apply lemmeSymNP x z H1;
apply H1;
assume H0;
simpl update;
apply lemme5 (update1 σ x c z z) (σ z) (update1 σ' x c z z) (and_i _ _ _ _);
apply (and_ed _ _ (axiom1 σ x z z c)) H0;
apply lemme5 (σ z) (σ' z) (update1 σ' x c z z) (and_i _ _ _ _);
apply H z;
apply lemme4 (update1 σ' x c z z) (σ' z) ((and_ed _ _ (axiom1 σ' x z z c)) H0);
end;

opaque symbol lemmeInt : Π (f : El formula), π(∀ valuation (λ σ, ∀ valuation (λ σ', ((interpretation σ f) ∧ (∀ nat (λ x, (σ x) simeq (σ' x)))) ⇒ (interpretation σ' f))))
≔ begin
apply recF (λ f, ∀ valuation (λ σ, ∀ valuation (λ σ', ((interpretation σ f) ∧ (∀ nat (λ x, (σ x) simeq (σ' x)))) ⇒ (interpretation σ' f))));
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
assume f g Hfg σ σ' Himp Hf;
apply (and_ed _ _ Hfg σ σ') (and_i _ _ _ (and_ed _ _ Himp));
apply and_eg _ _ Himp _;
apply (and_eg _ _ Hfg σ' σ) (and_i _ _ Hf _);
assume x;
apply lemme4 (σ x) (σ' x) (and_ed _ _ Himp x);
assume f Hf x σ σ' Hall c;
apply Hf (update σ x c) (update σ' x c) (and_i _ _ (and_eg _ _ Hall c) _);
apply lemmeVal σ σ' x c (and_ed _ _ Hall);
assume f Hf x σ σ' Hex;
apply ExElim g _ (and_eg _ _ Hex) _;
assume c Hc;
apply ExIntro g c _ _;
apply Hf (update σ x c) (update σ' x c) (and_i _ _ Hc _);
apply lemmeVal σ σ' x c (and_ed _ _ Hex);
assume σ σ' H;
apply and_eg _ _ H;
assume σ σ' H;
apply and_eg _ _ H;
end;

opaque symbol lemme32 : Π (z : El nat), Π (f : El formula), π(∀ g (λ a, ∀ g (λ b, (∀ valuation (λ σ, ((interpretation (update σ z a) f) ∧ (a simeq b)) ⇒ (interpretation (update σ z b) f))))))
≔ begin
assume z;
apply recF (λ f, ∀ g (λ a, ∀ g (λ b, ∀ valuation (λ σ, (interpretation (update σ z a) f ∧ (a simeq b)) ⇒ interpretation (update σ z b) f))));
assume x y a b σ Heq;
apply lemme5 (update σ z b x) (update σ z a x) (update σ z b y) (and_i _ _ _ _);
apply lemme4 (update σ z a x) (update σ z b x) (lemmeUp σ z a b (and_ed _ _ Heq) x);
apply lemme5 (update σ z a x) (update σ z a y) (update σ z b y) (and_i _ _ _ _);
apply and_eg _ _ Heq;
apply lemmeUp σ z a b (and_ed _ _ Heq) y;
assume x y a b σ Hin;
apply lemme31 (update σ z b x) (update σ z a y) (update σ z b y) (and_i _ _ _ _);
apply lemme30 (update σ z a x) (update σ z a y) (update σ z b x) (and_i _ _ _ _);
apply and_eg _ _ Hin;
apply lemmeUp σ z a b (and_ed _ _ Hin) x;
apply lemmeUp σ z a b (and_ed _ _ Hin) y;
assume f g Hfg a b σ Hand;
apply and_i;
apply ((and_eg _ _ Hfg) a b σ) (and_i _ _ (and_eg _ _ (and_eg _ _ Hand)) (and_ed _ _ Hand));
apply ((and_ed _ _ Hfg) a b σ) (and_i _ _ (and_ed _ _ (and_eg _ _ Hand)) (and_ed _ _ Hand));
assume f g Hfg a b σ Hor;
apply or_e _ _ _ (and_eg _ _ Hor);
assume Hf;
apply or_ig;
apply ((and_eg _ _ Hfg) a b σ) (and_i _ _ Hf (and_ed _ _ Hor));
assume Hg;
apply or_id;
apply ((and_ed _ _ Hfg) a b σ) (and_i _ _ Hg (and_ed _ _ Hor));
assume f g Hfg a b σ Himp Hf;
apply (and_ed _ _ Hfg a b σ) (and_i _ _ _ (and_ed _ _ Himp));
apply and_eg _ _ Himp _;
apply (and_eg _ _ Hfg b a σ) (and_i _ _ Hf _);
apply lemme4 a b (and_ed _ _ Himp);
assume f Hf x a b σ Hall c;
apply lemmeInt f (update (update σ z a) x c) (update (update σ z b) x c) (and_i _ _ _ _);
apply (and_eg _ _ Hall) c;
apply (lemmeUp2 σ z x a b c) (and_ed _ _ Hall);
assume f Hf x a b σ Hex;
apply ExElim g _ (and_eg _ _ Hex) _;
assume c Hc;
apply ExIntro g c _ _;
apply lemmeInt f (update (update σ z a) x c) (update (update σ z b) x c) (and_i _ _ _ _);
apply Hc;
apply (lemmeUp2 σ z x a b c) (and_ed _ _ Hex);
assume a b σ H;
apply and_eg _ _ H;
assume a b σ H;
apply and_eg _ _ H;
end;

opaque symbol lemme41 : Π (x y : El nat), Π (f : El formula), Π (c d : Graph), π(∀ valuation (λ σ, ((interpretation (update (update σ x c) y d) f) 
∧ (∀ g (λ a, ∀ g (λ a', ∀ g (λ b, ((a' ∈ a) ∧ (interpretation (update (update σ x a) y b) f)) ⇒ (∃ g (λ b', ((b' ∈ b) ∧ (interpretation (update (update σ x a') y b') f))))))))
∧ (∀ g (λ b, ∀ g (λ b', ∀ g (λ a, ((b' ∈ b) ∧ (interpretation (update (update σ x a) y b) f)) ⇒ (∃ g (λ a', ((a' ∈ a) ∧ (interpretation (update (update σ x a') y b') f))))))))) ⇒ (c simeq d)))
≔ begin
assume x y f c d σ H;
apply ExIntro relat (λ u, λ v, interpretation (update (update σ x (cr c u)) y (cr d v)) f) _ _;
apply and_i;
apply and_i;
apply lemmeInt f (update (update σ x c) y (cr d (root d))) (update (update σ x (cr c (root c))) y (cr d (root d))) (and_i _ _ _ _);
apply lemme32 y f d (cr d (root d)) (update σ x c) (and_i _ _ _ _);
apply (and_eg _ _ (and_eg _ _ H));
apply lemme6 d;
apply lemmeUp2 σ x y c (cr c (root c)) (cr d (root d)) _;
apply lemme6 c;
assume u u' v Hu;
apply ExElim g _ ((and_ed _ _ (and_eg _ _ H)) (cr c u) (cr c u') (cr d v) (and_i _ _ _ _)) _;
apply lemme28 (cr c u) u' (and_eg _ _ Hu);
apply and_ed _ _ Hu;
assume b Hb;
apply ExElim n _ (and_eg _ _ Hb) _;
assume v' Hv';
apply ExIntro n v' _ _;
apply and_i;
apply and_eg _ _ Hv';
apply lemme32 y f b (cr d v') (update σ x (cr c u')) (and_i _ _ _ _);
apply and_ed _ _ Hb;
apply and_ed _ _ Hv';
assume v v' u Hv;
apply ExElim g _ ((and_ed _ _ H) (cr d v) (cr d v') (cr c u) (and_i _ _ _ _)) _;
apply lemme28 (cr d v) v' (and_eg _ _ Hv);
apply and_ed _ _ Hv;
assume b Hb;
apply ExElim n _ (and_eg _ _ Hb) _;
assume u' Hu';
apply ExIntro n u' _ _;
apply and_i;
apply and_eg _ _ Hu';
apply lemmeInt f (update (update σ x b) y (cr d v')) (update (update σ x (cr c u')) y (cr d v')) (and_i _ _ _ _);
apply and_ed _ _ Hb;
apply lemmeUp2 σ x y b (cr c u') (cr d v') _;
apply and_ed _ _ Hu';
end;

opaque symbol lemmeHypExt : Π (c d : Graph), π((∀ g (λ z, (z ∈ c) ⇔ (z ∈ d))) ⇒ ((((c simeq c) ∧ (d simeq d)) ∨ (c simeq d))
∧ (∀ g (λ a, ∀ g (λ a', ∀ g (λ b, ((a' ∈ a) ∧ (((a simeq c) ∧ (b simeq d)) ∨ (a simeq b))) ⇒ (∃ g (λ b', ((b' ∈ b) ∧ (((a' simeq c) ∧ (b' simeq d)) ∨ (a' simeq b')))))))))
∧ (∀ g (λ b, ∀ g (λ b', ∀ g (λ a, ((b' ∈ b) ∧ (((a simeq c) ∧ (b simeq d)) ∨ (a simeq b))) ⇒ (∃ g (λ a', ((a' ∈ a) ∧ (((a' simeq c) ∧ (b' simeq d)) ∨ (a' simeq b')))))))))))
≔ begin
assume c d Hext;
apply and_i;
apply and_i;
apply or_ig;
apply (and_i _ _ (lemme3 c) (lemme3 d));
assume a a' b H;
apply or_e _ _ _ (and_ed _ _ H);
assume H1;
apply ExIntro g a' _ _;
apply and_i;
apply lemme31 a' d b (and_i _ _ _ _);
apply (and_eg _ _ (Hext a')) (lemme31 a' a c (and_i _ _ (and_eg _ _ H) (and_eg _ _ H1)));
apply lemme4 b d (and_ed _ _ H1);
apply or_id;
apply lemme3 a';
assume H2;
apply ExIntro g a' _ _;
apply and_i;
apply lemme31 a' a b (and_i _ _ (and_eg _ _ H) H2);
apply or_id;
apply lemme3 a';
assume b b' a H;
apply or_e _ _ _ (and_ed _ _ H);
assume H1;
apply ExIntro g b' _ _;
apply and_i;
apply lemme31 b' c a (and_i _ _ _ _);
apply (and_ed _ _ (Hext b')) (lemme31 b' b d (and_i _ _ (and_eg _ _ H) (and_ed _ _ H1)));
apply lemme4 a c (and_eg _ _ H1);
apply or_id;
apply lemme3 b';
assume H2;
apply ExIntro g b' _ _;
apply and_i;
apply lemme31 b' b a (and_i _ _ (and_eg _ _ H) (lemme4 a b H2));
apply or_id;
apply lemme3 b';
end;

opaque symbol lemmeExt : Π (c d : Graph), π((∀ g (λ x, (x ∈ c) ⇔ (x ∈ d))) ⇒ (c simeq d))
≔ begin
assume c d H;
apply lemme41 zero one (orF (andF (eqF zero two) (eqF one three)) (eqF zero one)) c d (update (update (λ _, empty_set) two c) three d) (lemmeHypExt c d H);
end;