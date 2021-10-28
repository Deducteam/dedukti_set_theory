require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.bisimilarity;
require open zf.theoriezf.injectivity;
require open zf.theoriezf.eta1;
require open zf.theoriezf.eta2;
require open zf.theoriezf.eta3;
require open zf.theoriezf.membership;
require open zf.theoriezf.embedding;
require open zf.theoriezf.finitary;

opaque symbol lemma52 : π(`∀ a, `∀ c, (a ∈ c) ⇒ (a ∈ (Cl c)))
≔ begin
assume a c Hac;
refine ExElim n _ Hac _ _;
assume x Hx;
refine ExIntro n (i x) _ _;
refine and_i _ _ _ _;
refine (and_ed _ _ (lemma27 c (i x))) _;
refine ExIntro n x _ _;
refine and_i _ _ _ _;
refine refl n (i x);
assume P;
assume H;
refine (and_eg _ _ H) x (and_eg _ _ Hx);
refine lemma5 a (cr c x) (cr (Cl c) (i x)) (and_i _ _ (and_ed _ _ Hx) _);
refine lemma4 (cr (Cl c) (i x)) (cr c x) (lemma40 c x);
end;

opaque symbol lemma53 : π(`∀ a, `∀ b, `∀ c, ((a ∈ b) ∧ (b ∈ (Cl c))) ⇒ (a ∈ (Cl c)))
≔ begin
assume a b c H;
refine ExElim n _ (and_ed _ _ H) _ _;
assume u Hu;
refine ExElim n _ ((and_eg _ _ (lemma27 c u)) (and_eg _ _ Hu)) _ _;
assume x Hx;
refine ExElim n _ (and_eg _ _ H) _ _;
assume y Hy;
refine ExElim n _ ((lemma29 b (cr c x) _) y (and_eg _ _ Hy)) _ _;
refine lemma5 b (cr (Cl c) u) (cr c x) (and_i _ _ (and_ed _ _ Hu) _);
refine imp_i (u = i x) _ _ _;
assume H1;
refine imp_i (i x = u) _ _ _;
assume H2;
refine H2 (λ w, (cr (Cl c) w) simeq (cr c x)) (lemma40 c x);
refine lemmaSymEg n u (i x) H1;
refine and_eg _ _ Hx;
assume z Hz;
refine ExIntro n (i z) _ _;
refine and_i _ _ _ _;
refine (and_ed _ _ (lemma27 c (i z))) _;
refine ExIntro n z _ _;
refine and_i _ _ _ _;
refine refl n (i z);
assume e He;
refine ((and_ed _ _ He) z x (and_i _ _ (and_eg _ _ Hz) ((and_ed _ _ Hx) e He)));
refine lemma5 a (cr b y) (cr (Cl c) (i z)) (and_i _ _ (and_ed _ _ Hy) _);
refine lemma5 (cr b y) (cr c z) (cr (Cl c) (i z)) (and_i _ _ (and_ed _ _ Hz) _);
refine lemma4 (cr (Cl c) (i z)) (cr c z) (lemma40 c z);
end;
