require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.bisimilarity;
require open zf.theoriezf.injectivity;
require open zf.theoriezf.eta1;
require open zf.theoriezf.eta2;
require open zf.theoriezf.membership;
require open zf.theoriezf.lemma32;
require open zf.theoriezf.nat;
require open zf.theoriezf.formulas;
require open zf.theoriezf.formulas_lemmas;

opaque symbol lemma41 : Π (x y : El nat), Π (f : El formula), Π (c d : Graph), π(∀ valuation (λ σ, ((interpretation (update (update σ x c) y d) f) 
∧ (∀ g (λ a, ∀ g (λ a', ∀ g (λ b, ((a' ∈ a) ∧ (interpretation (update (update σ x a) y b) f)) ⇒ (∃ g (λ b', ((b' ∈ b) ∧ (interpretation (update (update σ x a') y b') f))))))))
∧ (∀ g (λ b, ∀ g (λ b', ∀ g (λ a, ((b' ∈ b) ∧ (interpretation (update (update σ x a) y b) f)) ⇒ (∃ g (λ a', ((a' ∈ a) ∧ (interpretation (update (update σ x a') y b') f))))))))) ⇒ (c simeq d)))
≔ begin
assume x y f c d σ H;
refine ExIntro relat (λ u, λ v, interpretation (update (update σ x (cr c u)) y (cr d v)) f) _ _;
refine and_i _ _ _ _;
refine and_i _ _ _ _;
refine lemmaInt f (update (update σ x c) y (cr d (root d))) (update (update σ x (cr c (root c))) y (cr d (root d))) (and_i _ _ _ _);
refine lemma32 y f d (cr d (root d)) (update σ x c) (and_i _ _ _ _);
refine (and_eg _ _ (and_eg _ _ H));
refine lemma6 d;
refine lemmaUp2 σ x y c (cr c (root c)) (cr d (root d)) _;
refine lemma6 c;
assume u u' v Hu;
refine ExElim g _ ((and_ed _ _ (and_eg _ _ H)) (cr c u) (cr c u') (cr d v) (and_i _ _ _ _)) _ _;
refine lemma28 (cr c u) u' (and_eg _ _ Hu);
refine and_ed _ _ Hu;
assume b Hb;
refine ExElim n _ (and_eg _ _ Hb) _ _;
assume v' Hv';
refine ExIntro n v' _ _;
refine and_i _ _ _ _;
refine and_eg _ _ Hv';
refine lemma32 y f b (cr d v') (update σ x (cr c u')) (and_i _ _ _ _);
refine and_ed _ _ Hb;
refine and_ed _ _ Hv';
assume v v' u Hv;
refine ExElim g _ ((and_ed _ _ H) (cr d v) (cr d v') (cr c u) (and_i _ _ _ _)) _ _;
refine lemma28 (cr d v) v' (and_eg _ _ Hv);
refine and_ed _ _ Hv;
assume b Hb;
refine ExElim n _ (and_eg _ _ Hb) _ _;
assume u' Hu';
refine ExIntro n u' _ _;
refine and_i _ _ _ _;
refine and_eg _ _ Hu';
refine lemmaInt f (update (update σ x b) y (cr d v')) (update (update σ x (cr c u')) y (cr d v')) (and_i _ _ _ _);
refine and_ed _ _ Hb;
refine lemmaUp2 σ x y b (cr c u') (cr d v') _;
refine and_ed _ _ Hu';
end;

opaque symbol lemmaHypExt : Π (c d : Graph), π((∀ g (λ z, (z ∈ c) ⇔ (z ∈ d))) ⇒ ((((c simeq c) ∧ (d simeq d)) ∨ (c simeq d))
∧ (∀ g (λ a, ∀ g (λ a', ∀ g (λ b, ((a' ∈ a) ∧ (((a simeq c) ∧ (b simeq d)) ∨ (a simeq b))) ⇒ (∃ g (λ b', ((b' ∈ b) ∧ (((a' simeq c) ∧ (b' simeq d)) ∨ (a' simeq b')))))))))
∧ (∀ g (λ b, ∀ g (λ b', ∀ g (λ a, ((b' ∈ b) ∧ (((a simeq c) ∧ (b simeq d)) ∨ (a simeq b))) ⇒ (∃ g (λ a', ((a' ∈ a) ∧ (((a' simeq c) ∧ (b' simeq d)) ∨ (a' simeq b')))))))))))
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

opaque symbol lemmaExt : Π (c d : Graph), π((∀ g (λ x, (x ∈ c) ⇔ (x ∈ d))) ⇒ (c simeq d))
≔ begin
assume c d H;
refine lemma41 zero one (orF (andF (eqF zero two) (eqF one three)) (eqF zero one)) c d (update (update (λ _, empty_set) two c) three d) (lemmaHypExt c d H);
end;
