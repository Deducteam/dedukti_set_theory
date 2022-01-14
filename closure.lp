require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.bisimilarity;
require open Logic.Z.injectivity;
require open Logic.Z.eta1;
require open Logic.Z.eta2;
require open Logic.Z.eta3;
require open Logic.Z.membership;
require open Logic.Z.embedding;
require open Logic.Z.finitary;

opaque symbol lemma52 : π(`∀ a, `∀ c, (a ∈ c) ⇒ (a ∈ (Cl c)))
≔ begin
assume a c Hac;
refine ExElim node _ Hac _ _;
assume x Hx;
refine ExIntro node (i x) _ _;
refine and_i _ _ _ _
{refine (and_ed _ _ (lemma27 c (i x))) _;
refine ExIntro node x _ _;
refine and_i _ _ _ _
{refine refl node (i x)}
{assume P;
assume H;
refine (and_eg _ _ H) x (and_eg _ _ Hx)}}
{refine lemma5 a (cr c x) (cr (Cl c) (i x)) (and_i _ _ (and_ed _ _ Hx) _);
refine lemma4 (cr (Cl c) (i x)) (cr c x) (lemma40 c x)}
end;

opaque symbol lemma53 : π(`∀ a, `∀ b, `∀ c, ((a ∈ b) ∧ (b ∈ (Cl c))) ⇒ (a ∈ (Cl c)))
≔ begin
assume a b c H;
refine ExElim node _ (and_ed _ _ H) _ _;
assume u Hu;
refine ExElim node _ ((and_eg _ _ (lemma27 c u)) (and_eg _ _ Hu)) _ _;
assume x Hx;
refine ExElim node _ (and_eg _ _ H) _ _;
assume y Hy;
refine ExElim node _ ((lemma29 b (cr c x) _) y (and_eg _ _ Hy)) _ _
{refine lemma5 b (cr (Cl c) u) (cr c x) (and_i _ _ (and_ed _ _ Hu) _);
refine imp_i (u = i x) _ _ _
{assume H1;
refine imp_i (i x = u) _ _ _
{assume H2;
refine H2 (λ w, (cr (Cl c) w) simeq (cr c x)) (lemma40 c x)}
{refine lemmaSymEg node u (i x) H1}}
{refine and_eg _ _ Hx}}
{assume z Hz;
refine ExIntro node (i z) _ _;
refine and_i _ _ _ _
{refine (and_ed _ _ (lemma27 c (i z))) _;
refine ExIntro node z _ _;
refine and_i _ _ _ _
{refine refl node (i z)}
{assume e He;
refine ((and_ed _ _ He) z x (and_i _ _ (and_eg _ _ Hz) ((and_ed _ _ Hx) e He)))}}
{refine lemma5 a (cr b y) (cr (Cl c) (i z)) (and_i _ _ (and_ed _ _ Hy) _);
refine lemma5 (cr b y) (cr c z) (cr (Cl c) (i z)) (and_i _ _ (and_ed _ _ Hz) _);
refine lemma4 (cr (Cl c) (i z)) (cr c z) (lemma40 c z)}}
end;
