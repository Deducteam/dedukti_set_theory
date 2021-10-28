require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.bisimilarity;
require open zf.theoriezf.injectivity;
require open zf.theoriezf.eta1;
require open zf.theoriezf.eta2;
require open zf.theoriezf.membership;
require open zf.theoriezf.lemma32;
require open zf.theoriezf.lemma41;
require open zf.theoriezf.nat;
require open zf.theoriezf.formulas;
require open zf.theoriezf.formulas_lemmas;
require open zf.theoriezf.language2;

opaque symbol lemmaHypExt : Π (c d : Graph), π((`∀ z, (z ∈ c) ⇔ (z ∈ d)) ⇒ ((((c simeq c) ∧ (d simeq d)) ∨ (c simeq d))
∧ (`∀ a, `∀ a', `∀ b, ((a' ∈ a) ∧ (((a simeq c) ∧ (b simeq d)) ∨ (a simeq b))) ⇒ (`∃ b', ((b' ∈ b) ∧ (((a' simeq c) ∧ (b' simeq d)) ∨ (a' simeq b')))))
∧ (`∀ b, `∀ b', `∀ a, ((b' ∈ b) ∧ (((a simeq c) ∧ (b simeq d)) ∨ (a simeq b))) ⇒ (`∃ a', ((a' ∈ a) ∧ (((a' simeq c) ∧ (b' simeq d)) ∨ (a' simeq b')))))))
≔ begin
assume c d Hext;
refine and_i _ _ _ _;
refine and_i _ _ _ _;
refine or_ig _ _ _;
refine (and_i _ _ (lemma3 c) (lemma3 d));
assume a a' b H;
refine or_e _ _ _ (and_ed _ _ H) _ _;
assume H1;
refine ExIntro g a' _ _;
refine and_i _ _ _ _;
refine lemma31 a' d b (and_i _ _ _ _);
refine (and_eg _ _ (Hext a')) (lemma31 a' a c (and_i _ _ (and_eg _ _ H) (and_eg _ _ H1)));
refine lemma4 b d (and_ed _ _ H1);
refine or_id _ _ _;
refine lemma3 a';
assume H2;
refine ExIntro g a' _ _;
refine and_i _ _ _ _;
refine lemma31 a' a b (and_i _ _ (and_eg _ _ H) H2);
refine or_id _ _ _;
refine lemma3 a';
assume b b' a H;
refine or_e _ _ _ (and_ed _ _ H) _ _;
assume H1;
refine ExIntro g b' _ _;
refine and_i _ _ _ _;
refine lemma31 b' c a (and_i _ _ _ _);
refine (and_ed _ _ (Hext b')) (lemma31 b' b d (and_i _ _ (and_eg _ _ H) (and_ed _ _ H1)));
refine lemma4 a c (and_eg _ _ H1);
refine or_id _ _ _;
refine lemma3 b';
assume H2;
refine ExIntro g b' _ _;
refine and_i _ _ _ _;
refine lemma31 b' b a (and_i _ _ (and_eg _ _ H) (lemma4 a b H2));
refine or_id _ _ _;
refine lemma3 b';
end;

opaque symbol lemmaExt : Π (c d : Graph), π((`∀ x, (x ∈ c) ⇔ (x ∈ d)) ⇒ (c simeq d))
≔ begin
assume c d H;
refine lemma41 zero one (orF (andF (eqF zero two) (eqF one three)) (eqF zero one)) c d (update (update (λ _, empty_set) two c) three d) (lemmaHypExt c d H);
end;