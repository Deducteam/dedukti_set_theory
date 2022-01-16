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
refine ex_e node _ Hac _ _;
assume x Hx;
refine ex_i node (i x) _ _;
refine and_i _ _ _ _
{refine (and_er _ _ (lemma27 c (i x))) _;
refine ex_i node x _ _;
refine and_i _ _ _ _
{refine refl node (i x)}
{assume P;
assume H;
refine (and_el _ _ H) x (and_el _ _ Hx)}}
{refine lemma5 a (cr c x) (cr (Cl c) (i x)) (and_i _ _ (and_er _ _ Hx) _);
refine lemma4 (cr (Cl c) (i x)) (cr c x) (lemma40 c x)}
end;

opaque symbol lemma53 : π(`∀ a, `∀ b, `∀ c, ((a ∈ b) ∧ (b ∈ (Cl c))) ⇒ (a ∈ (Cl c)))
≔ begin
assume a b c H;
refine ex_e node _ (and_er _ _ H) _ _;
assume u Hu;
refine ex_e node _ ((and_el _ _ (lemma27 c u)) (and_el _ _ Hu)) _ _;
assume x Hx;
refine ex_e node _ (and_el _ _ H) _ _;
assume y Hy;
refine ex_e node _ ((lemma29 b (cr c x) _) y (and_el _ _ Hy)) _ _
{refine lemma5 b (cr (Cl c) u) (cr c x) (and_i _ _ (and_er _ _ Hu) _);
refine imp_i (u = i x) _ _ _
{assume H1;
refine imp_i (i x = u) _ _ _
{assume H2;
refine H2 (λ w, (cr (Cl c) w) simeq (cr c x)) (lemma40 c x)}
{refine sym node u (i x) H1}}
{refine and_el _ _ Hx}}
{assume z Hz;
refine ex_i node (i z) _ _;
refine and_i _ _ _ _
{refine (and_er _ _ (lemma27 c (i z))) _;
refine ex_i node z _ _;
refine and_i _ _ _ _
{refine refl node (i z)}
{assume e He;
refine ((and_er _ _ He) z x (and_i _ _ (and_el _ _ Hz) ((and_er _ _ Hx) e He)))}}
{refine lemma5 a (cr b y) (cr (Cl c) (i z)) (and_i _ _ (and_er _ _ Hy) _);
refine lemma5 (cr b y) (cr c z) (cr (Cl c) (i z)) (and_i _ _ (and_er _ _ Hz) _);
refine lemma4 (cr (Cl c) (i z)) (cr c z) (lemma40 c z)}}
end;
