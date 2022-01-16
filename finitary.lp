require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.bisimilarity;
require open Logic.Z.injectivity;
require open Logic.Z.eta1;
require open Logic.Z.eta2;
require open Logic.Z.eta3;
require open Logic.Z.membership;
require open Logic.Z.embedding;
require open Logic.Z.lemma32;
require open Logic.Z.relocation;
require open Logic.Z.formulas;
require open Logic.Z.formulas_lemmas;
require open Logic.Z.nat;
require open Logic.Z.language2;
require open Logic.Z.weak_extensionality;

opaque symbol lemma42 : π(`∀ a, `∀ c, (c ∈ (join a)) ⇔ (`∃ b, (c ∈ b) ∧ (b ∈ a)))
≔ begin
assume a c;
refine and_i _ _ _ _
{assume H;
refine ex_e node _ H _ _;
assume x Hx;
refine ex_e node _ ((and_el _ _ (lemma15 a x)) (and_el _ _ Hx)) _ _;
assume y Hy;
refine ex_e node _ Hy _ _;
assume z Hz;
refine ex_i graph (cr a z) _ _;
refine and_i _ _ _ _
{refine ex_i node y _ _;
refine and_i _ _ _ _
{refine and_er _ _ (and_el _ _ Hz)}
{refine lemma5 c (cr (join a) (i y)) (cr a y) _;
refine and_i _ _ _ _
{refine imp_i (i y = x) _ _ _
{assume H1;
refine imp_i (x = i y) _ _ _
{assume H2;
refine H2 (λ w, c simeq cr (join a) w) _;
refine and_er _ _ Hx}
{refine sym node (i y) x H1}}
{refine sym node x (i y) (and_el _ _ (and_el _ _ Hz))}}
{refine lemma35 a y}}}
{refine lemma28 a z (and_er _ _ Hz)}}
{assume H;
refine ex_e graph _ H _ _;
assume b Hb;
refine ex_e node _ (and_er _ _ Hb) _ _;
assume z Hz;
refine ex_e node _ (and_el _ _ Hb) _ _;
assume x Hx;
refine ex_e node _ ((lemma29 b (cr a z) (and_er _ _ Hz) x) (and_el _ _ Hx)) _ _;
assume y Hy;
refine ex_i node (i y) _ _;
refine and_i _ _ _ _
{refine (and_er _ _ (lemma15 a (i y))) _;
refine ex_i node y _ _;
refine ex_i node z _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine refl node (i y)}
{refine and_el _ _ Hy}}
{refine and_el _ _ Hz}}
{refine lemma5 c (cr a y) (cr (join a) (i y)) (and_i _ _ (lemma5 c (cr b x) (cr a y) (and_i _ _ (and_er _ _ Hx) (and_er _ _ Hy))) (lemma4 (cr (join a) (i y)) (cr a y) (lemma35 a y)))}}
end;

opaque symbol lemma43 : π(`∀ a, `∀ b, `∀ c, (c ∈ (pair a b)) ⇔ ((c simeq a) ∨ (c simeq b)))
≔ begin
assume a b c;
refine and_i _ _ _ _
{assume H;
refine ex_e node _ H _ _;
assume x Hx;
refine or_e _ _ _ ((and_el _ _ (lemma18 a b x)) (and_el _ _ Hx)) _ _
{assume H1;
refine or_il _ _ _;
refine lemma5 c (cr (pair a b) x) a (and_i _ _ (and_er _ _ Hx) (lemma4 a (cr (pair a b) x) (lemma33 a (cr (pair a b) x) _)));
refine and_i _ _ _ _
{refine H1}
{assume u v;
refine lemma16 a b v u}}
{assume H2;
refine or_ir _ _ _;
refine lemma5 c (cr (pair a b) x) b (and_i _ _ (and_er _ _ Hx) (lemma4 b (cr (pair a b) x) (lemma34 b (cr (pair a b) x) _)));
refine and_i _ _ _ _
{refine H2}
{assume u v;
refine lemma17 a b v u}}}
{assume H;
refine or_e _ _ _ H _ _
{assume H3;
refine ex_i node (i (root a)) _ _;
refine and_i _ _ _ _
{refine (and_er _ _ (lemma18 a b (i (root a)))) _;
refine or_il _ _ _;
refine refl node (i (root a))}
{refine lemma5 c a (cr (pair a b) (i (root a))) (and_i _ _ H3 (lemma4 (cr (pair a b) (i (root a))) a (lemma36 a b)))}}
{assume H4;
refine ex_i node (j (root b)) _ _;
refine and_i _ _ _ _
{refine (and_er _ _ (lemma18 a b (j (root b)))) _;
refine or_ir _ _ _;
refine refl node (j (root b))}
{refine lemma5 c b (cr (pair a b) (j (root b))) (and_i _ _ H4 (lemma4 (cr (pair a b) (j (root b))) b (lemma37 a b)))}}}
end;

opaque symbol lemma44 : π(`∀ a, `∀ b, (a ∈ (powerset b)) ⇔ (`∀ c, (c ∈ a) ⇒ (c ∈ b)))
≔ begin
assume a b;
refine and_i _ _ _ _
{assume H;
assume c Hc;
refine ex_e node _ H _ _;
assume x Hx;
refine ex_e graph _ ((and_el _ _ (lemma21 b x)) (and_el _ _ Hx)) _ _;
assume e He;
refine ex_e node _ Hc _ _;
assume y Hy;
refine ex_e node _ ((lemma29 a (cr (powerset b) x) (and_er _ _ Hx)) y (and_el _ _ Hy)) _ _;
assume z Hz;
refine ex_e node _ ((and_el _ _ (lemma20 b e z)) _) _ _
{refine imp_i (j (ρ e) = x) _ _ _
{assume H1;
refine imp_i (x = j (ρ e)) _ _ _
{assume H2;
refine H2 (λ w, eta (powerset b) z w) _;
refine and_el _ _ Hz}
{refine He}}
{refine sym node x (j (ρ e)) He}}
{assume z' Hz';
refine ex_i node z' _ _;
refine and_i _ _ _ _
{refine and_er _ _ (and_el _ _ Hz')}
{refine lemma5 c (cr a y) (cr b z') (and_i _ _ (and_er _ _ Hy) _);
refine lemma5 (cr a y) (cr (powerset b) (i z')) (cr b z') (and_i _ _ _ (lemma38 b z'));
refine imp_i (i z' = z) _ _ _
{assume H3;
refine imp_i (z = i z') _ _ _
{assume H4;
refine H4 (λ w, (cr a y) simeq (cr (powerset b) w)) _;
refine and_er _ _ Hz}
{refine sym node (i z') z H3}}
{refine sym node z (i z') (and_el _ _ (and_el _ _ Hz'))}}}}
{assume H;
refine imp_e (`∃ e, a simeq (cr (powerset b) (j (ρ e)))) _ _ _
{assume H';
refine ex_e graph _ H' _ _;
assume e He;
refine ex_i node (j (ρ e)) _ _;
refine and_i _ _ _ He;
refine and_er _ _ (lemma21 b (j (ρ e))) _;
refine ex_i graph e _ _ ;
refine (refl node (j (ρ e)))}
{refine imp_e (`∃ e, `∀ c, (c ∈ a) ⇔ (c ∈ (cr (powerset b) (j (ρ e))))) _ _ _
{assume H';
refine ex_e graph _ H' _ _;
assume e He;
refine ex_i graph e _ _;
refine lemmaExt a (cr (powerset b) (j (ρ e))) He}
{refine imp_e (`∃ e, `∀ c, (c ∈ a) ⇔ (`∃ y, (eta b y (root b) ∧ ((cr b y) ∈ e) ∧ (c simeq (cr b y))))) _ _ _
{assume H';
refine ex_e graph _ H' _ _;
assume e He;
refine ex_i graph e _ _;
assume c;
refine and_i _ _ _ _
{assume Hc;
refine ex_e node _ (and_el _ _ (He c) Hc) _ _;
assume y Hy;
refine ex_i node (i y) _ _;
refine and_i _ _ _ _
{refine and_er _ _ (lemma20 b e (i y)) _;
refine ex_i node y _ _;
refine and_i _ _ (and_i _ _ (refl node (i y)) (and_el _ _ (and_el _ _ Hy))) (and_er _ _ (and_el _ _ Hy))}
{refine lemma5 c (cr b y) (cr (powerset b) (i y)) (and_i _ _ (and_er _ _ Hy) (lemma4 (cr (powerset b) (i y)) (cr b y) (lemma38 b y)))}}
{assume Hc;
refine and_er _ _ (He c) _;
refine ex_e node _ Hc _ _;
assume z Hz;
refine ex_e node _ (and_el _ _ (lemma20 b e z) (and_el _ _ Hz)) _ _;
assume y Hy;
refine ex_i node y _ _;
refine and_i _ _ (and_i _ _ (and_er _ _ (and_el _ _ Hy)) (and_er _ _ Hy)) _;
refine lemma5 c (cr (powerset b) (i y)) (cr b y) (and_i _ _ _ (lemma38 b y));
refine imp_i (i y = z) _ _ _
{assume K;
refine imp_i (z = i y) _ _ _
{assume K';
refine K' (λ w, c simeq (cr (powerset b) w)) (and_er _ _ Hz)}
{refine sym node (i y) z K}}
{refine sym node z (i y) (and_el _ _ (and_el _ _ Hy))}}}
{refine imp_e (`∃ e, `∀ c, (c ∈ a) ⇔ (`∃ y, (eta b y (root b) ∧ (c ∈ e) ∧ (c simeq (cr b y))))) _ _ _
{assume H';
refine ex_e graph _ H' _ _;
assume e He;
refine ex_i graph e _ _;
assume c;
refine and_i _ _ _ _
{assume Hc;
refine ex_e node _ (and_el _ _ (He c) Hc) _ _;
assume y Hy;
refine ex_i node y _ _;
refine and_i _ _ (and_i _ _ (and_el _ _ (and_el _ _ Hy)) _) (and_er _ _ Hy);
refine lemma30 c e (cr b y) (and_i _ _ (and_er _ _ (and_el _ _ Hy)) (and_er _ _ Hy))}
{assume Hc;
refine ex_e node _ Hc _ _;
assume y Hy;
refine and_er _ _ (He c) _;
refine ex_i node y _ _;
refine and_i _ _ (and_i _ _ (and_el _ _ (and_el _ _ Hy)) _) (and_er _ _ Hy);
refine lemma30 (cr b y) e c (and_i _ _ (and_er _ _ (and_el _ _ Hy)) (lemma4 c (cr b y) (and_er _ _ Hy)))}}
{refine imp_e (`∃ e, `∀ c, (c ∈ a) ⇔ ((c ∈ b) ∧ (c ∈ e))) _ _ _
{assume H';
refine ex_e graph _ H' _ _;
assume e He;
refine ex_i graph e _ _;
assume c;
refine and_i _ _ _ _
{assume Hc;
refine ex_e node _ (and_el _ _ (and_el _ _ (He c) Hc)) _ _;
assume y Hy;
refine ex_i node y _ _;
refine and_i _ _ (and_i _ _ (and_el _ _ Hy) _) (and_er _ _ Hy);
refine and_er _ _ (and_el _ _ (He c) Hc)}
{assume Hc;
refine ex_e node _ Hc _ _;
assume y Hy;
refine and_er _ _ (He c) _;
refine and_i _ _ _ (and_er _ _ (and_el _ _ Hy));
refine ex_i node y _ _;
refine and_i _ _ (and_el _ _ (and_el _ _ Hy)) ((and_er _ _ Hy))}}
{refine ex_i graph a _ _;
assume c;
refine and_i _ _ _ _
{assume Hca;
refine and_i _ _ (H c Hca) Hca}
{assume Hba;
refine and_er _ _ Hba}}}}}}}
end;

opaque symbol lemma45 : Π (σ : (El nat → El graph)), Π (f : El formula), π(`∀ a, `∀ b, (a ∈ (comp b σ f)) ⇔ ((a ∈ b) ∧ (interpretation (update σ zero a) f)))
≔ begin
assume σ f a b;
refine and_i _ _ _ _
{assume H;
refine ex_e node _ H _ _;
assume x Hx;
refine ex_e node _ ((and_el _ _ (lemma23 σ f b x)) (and_el _ _ Hx)) _ _;
assume y Hy;
refine and_i _ _ _ _
{refine ex_i node y _ _;
refine and_i _ _ _ _
{refine and_er _ _ (and_el _ _ Hy)}
{refine lemma5 a (cr (comp b σ f) x) (cr b y) (and_i _ _ (and_er _ _ Hx) _);
refine imp_i (x = i y) _ _ _
{assume H1;
refine imp_i (i y = x) _ _ _
{assume H2;
refine H2 (λ w, (cr (comp b σ f) w) simeq (cr b y)) _;
refine lemma39 σ f b y}
{refine sym node x (i y) H1}}
{refine and_el _ _ (and_el _ _ Hy)}}}
{refine lemma32 zero f (cr b y) a σ (and_i _ _ (and_er _ _ Hy) _);
refine lemma4 a (cr b y) (lemma5 a (cr (comp b σ f) x) (cr b y) (and_i _ _ (and_er _ _ Hx) _));
refine imp_i (x = i y) _ _ _
{assume H1;
refine imp_i (i y = x) _ _ _
{assume H2;
refine H2 (λ w, (cr (comp b σ f) w) simeq (cr b y)) _;
refine lemma39 σ f b y}
{refine sym node x (i y) H1}}
{refine and_el _ _ (and_el _ _ Hy)}}}
{assume H;
refine ex_e node _ (and_el _ _ H) _ _;
assume y Hy;
refine ex_i node (i y) _ _;
refine and_i _ _ _ _
{refine and_er _ _ (lemma23 σ f b (i y)) _;
refine ex_i node y _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine refl node (i y)}
{refine and_el _ _ Hy}}
{refine lemma32 zero f a (cr b y) σ (and_i _ _ (and_er _ _ H) (and_er _ _ Hy))}}
{refine lemma5 a (cr b y) (cr (comp b σ f) (i y)) (and_i _ _ (and_er _ _ Hy) (lemma4 (cr (comp b σ f) (i y)) (cr b y) (lemma39 σ f b y)))}}
end;
