require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.lemmas1_6;
require open zf.theoriezf.lemmas7_13;
require open zf.theoriezf.lemmas14_18;
require open zf.theoriezf.lemmas19_21;
require open zf.theoriezf.lemmas28_34;
require open zf.theoriezf.nat;
require open zf.theoriezf.formulas;
require open zf.theoriezf.formulas_lemmas;

opaque symbol lemma32 : Π (z : El nat), Π (f : El formula), π(∀ g (λ a, ∀ g (λ b, (∀ valuation (λ σ, ((interpretation (update σ z a) f) ∧ (a simeq b)) ⇒ (interpretation (update σ z b) f))))))
≔ begin
assume z;
apply recF (λ f, ∀ g (λ a, ∀ g (λ b, ∀ valuation (λ σ, (interpretation (update σ z a) f ∧ (a simeq b)) ⇒ interpretation (update σ z b) f))));
assume x y a b σ Heq;
apply lemma5 (update σ z b x) (update σ z a x) (update σ z b y) (and_i _ _ _ _);
apply lemma4 (update σ z a x) (update σ z b x) (lemmaUp σ z a b (and_ed _ _ Heq) x);
apply lemma5 (update σ z a x) (update σ z a y) (update σ z b y) (and_i _ _ _ _);
apply and_eg _ _ Heq;
apply lemmaUp σ z a b (and_ed _ _ Heq) y;
assume x y a b σ Hin;
apply lemma31 (update σ z b x) (update σ z a y) (update σ z b y) (and_i _ _ _ _);
apply lemma30 (update σ z a x) (update σ z a y) (update σ z b x) (and_i _ _ _ _);
apply and_eg _ _ Hin;
apply lemmaUp σ z a b (and_ed _ _ Hin) x;
apply lemmaUp σ z a b (and_ed _ _ Hin) y;
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
apply lemma4 a b (and_ed _ _ Himp);
assume f Hf x a b σ Hall c;
apply lemmaInt f (update (update σ z a) x c) (update (update σ z b) x c) (and_i _ _ _ _);
apply (and_eg _ _ Hall) c;
apply (lemmaUp2 σ z x a b c) (and_ed _ _ Hall);
assume f Hf x a b σ Hex;
apply ExElim g _ (and_eg _ _ Hex) _;
assume c Hc;
apply ExIntro g c _ _;
apply lemmaInt f (update (update σ z a) x c) (update (update σ z b) x c) (and_i _ _ _ _);
apply Hc;
apply (lemmaUp2 σ z x a b c) (and_ed _ _ Hex);
assume a b σ H;
apply and_eg _ _ H;
assume a b σ H;
apply and_eg _ _ H;
end;

opaque symbol lemma41 : Π (x y : El nat), Π (f : El formula), Π (c d : Graph), π(∀ valuation (λ σ, ((interpretation (update (update σ x c) y d) f) 
∧ (∀ g (λ a, ∀ g (λ a', ∀ g (λ b, ((a' ∈ a) ∧ (interpretation (update (update σ x a) y b) f)) ⇒ (∃ g (λ b', ((b' ∈ b) ∧ (interpretation (update (update σ x a') y b') f))))))))
∧ (∀ g (λ b, ∀ g (λ b', ∀ g (λ a, ((b' ∈ b) ∧ (interpretation (update (update σ x a) y b) f)) ⇒ (∃ g (λ a', ((a' ∈ a) ∧ (interpretation (update (update σ x a') y b') f))))))))) ⇒ (c simeq d)))
≔ begin
assume x y f c d σ H;
apply ExIntro relat (λ u, λ v, interpretation (update (update σ x (cr c u)) y (cr d v)) f) _ _;
apply and_i;
apply and_i;
apply lemmaInt f (update (update σ x c) y (cr d (root d))) (update (update σ x (cr c (root c))) y (cr d (root d))) (and_i _ _ _ _);
apply lemma32 y f d (cr d (root d)) (update σ x c) (and_i _ _ _ _);
apply (and_eg _ _ (and_eg _ _ H));
apply lemma6 d;
apply lemmaUp2 σ x y c (cr c (root c)) (cr d (root d)) _;
apply lemma6 c;
assume u u' v Hu;
apply ExElim g _ ((and_ed _ _ (and_eg _ _ H)) (cr c u) (cr c u') (cr d v) (and_i _ _ _ _)) _;
apply lemma28 (cr c u) u' (and_eg _ _ Hu);
apply and_ed _ _ Hu;
assume b Hb;
apply ExElim n _ (and_eg _ _ Hb) _;
assume v' Hv';
apply ExIntro n v' _ _;
apply and_i;
apply and_eg _ _ Hv';
apply lemma32 y f b (cr d v') (update σ x (cr c u')) (and_i _ _ _ _);
apply and_ed _ _ Hb;
apply and_ed _ _ Hv';
assume v v' u Hv;
apply ExElim g _ ((and_ed _ _ H) (cr d v) (cr d v') (cr c u) (and_i _ _ _ _)) _;
apply lemma28 (cr d v) v' (and_eg _ _ Hv);
apply and_ed _ _ Hv;
assume b Hb;
apply ExElim n _ (and_eg _ _ Hb) _;
assume u' Hu';
apply ExIntro n u' _ _;
apply and_i;
apply and_eg _ _ Hu';
apply lemmaInt f (update (update σ x b) y (cr d v')) (update (update σ x (cr c u')) y (cr d v')) (and_i _ _ _ _);
apply and_ed _ _ Hb;
apply lemmaUp2 σ x y b (cr c u') (cr d v') _;
apply and_ed _ _ Hu';
end;

opaque symbol lemmaHypExt : Π (c d : Graph), π((∀ g (λ z, (z ∈ c) ⇔ (z ∈ d))) ⇒ ((((c simeq c) ∧ (d simeq d)) ∨ (c simeq d))
∧ (∀ g (λ a, ∀ g (λ a', ∀ g (λ b, ((a' ∈ a) ∧ (((a simeq c) ∧ (b simeq d)) ∨ (a simeq b))) ⇒ (∃ g (λ b', ((b' ∈ b) ∧ (((a' simeq c) ∧ (b' simeq d)) ∨ (a' simeq b')))))))))
∧ (∀ g (λ b, ∀ g (λ b', ∀ g (λ a, ((b' ∈ b) ∧ (((a simeq c) ∧ (b simeq d)) ∨ (a simeq b))) ⇒ (∃ g (λ a', ((a' ∈ a) ∧ (((a' simeq c) ∧ (b' simeq d)) ∨ (a' simeq b')))))))))))
≔ begin
assume c d Hext;
apply and_i;
apply and_i;
apply or_ig;
apply (and_i _ _ (lemma3 c) (lemma3 d));
assume a a' b H;
apply or_e _ _ _ (and_ed _ _ H);
assume H1;
apply ExIntro g a' _ _;
apply and_i;
apply lemma31 a' d b (and_i _ _ _ _);
apply (and_eg _ _ (Hext a')) (lemma31 a' a c (and_i _ _ (and_eg _ _ H) (and_eg _ _ H1)));
apply lemma4 b d (and_ed _ _ H1);
apply or_id;
apply lemma3 a';
assume H2;
apply ExIntro g a' _ _;
apply and_i;
apply lemma31 a' a b (and_i _ _ (and_eg _ _ H) H2);
apply or_id;
apply lemma3 a';
assume b b' a H;
apply or_e _ _ _ (and_ed _ _ H);
assume H1;
apply ExIntro g b' _ _;
apply and_i;
apply lemma31 b' c a (and_i _ _ _ _);
apply (and_ed _ _ (Hext b')) (lemma31 b' b d (and_i _ _ (and_eg _ _ H) (and_ed _ _ H1)));
apply lemma4 a c (and_eg _ _ H1);
apply or_id;
apply lemma3 b';
assume H2;
apply ExIntro g b' _ _;
apply and_i;
apply lemma31 b' b a (and_i _ _ (and_eg _ _ H) (lemma4 a b H2));
apply or_id;
apply lemma3 b';
end;

opaque symbol lemmaExt : Π (c d : Graph), π((∀ g (λ x, (x ∈ c) ⇔ (x ∈ d))) ⇒ (c simeq d))
≔ begin
assume c d H;
apply lemma41 zero one (orF (andF (eqF zero two) (eqF one three)) (eqF zero one)) c d (update (update (λ _, empty_set) two c) three d) (lemmaHypExt c d H);
end;
