require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.bisimilarity;
require open Logic.Z.injectivity;
require open Logic.Z.eta1;
require open Logic.Z.eta2;
require open Logic.Z.eta3;
require open Logic.Z.membership;
require open Logic.Z.formulas;

opaque symbol lemma33 : π(`∀ a, `∀ b, (((root b) = i (root a)) ∧ (`∀ x, `∀ y', ((eta b y' (i x)) ⇔ (`∃ x', (y' = (i x')) ∧ (eta a x' x))))) ⇒ (a simeq b))
≔ begin
assume a b H;
refine ex_i (node arrow (node arrow prop)) (λ u, λ v, v = i u) _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_el _ _ H}
{assume x x' y H1;
refine ex_i node (i x') _ _;
refine and_i _ _ _ _
{refine imp_i (y = i x) _ _ _
{assume H2;
refine imp_i (i x = y) _ _ _
{assume H3;
refine H3 (λ w, eta b (i x') w) _;
refine (and_er _ _ ((and_er _ _ H) x (i x'))) (ex_i node x' _ (and_i _ _ (refl node (i x')) (and_el _ _ H1)))}
{refine sym node y (i x) H2}}
{refine and_er _ _ H1}}
{refine refl node (i x')}}}
{assume y y' x H4;
refine ex_e node _ ((and_el _ _ ((and_er _ _ H) x y')) _) _ _
{refine imp_i (i x = y) _ _ _
{assume H5;
refine imp_i (y = i x) _ _ _
{assume H6;
refine H6 (λ w, eta b y' w) _;
refine and_el _ _ H4}
{refine sym node (i x) y H5}}
{refine sym node y (i x) (and_er _ _ H4)}}
{assume x' Hx';
refine ex_i node x' _ _;
refine and_i _ _ (and_er _ _ Hx') (and_el _ _ Hx')}}
end;

opaque symbol lemma34 : π(`∀ a, `∀ b, (((root b) = j (root a)) ∧ (`∀ x, `∀ y', ((eta b y' (j x)) ⇔ (`∃ x', (y' = (j x')) ∧ (eta a x' x))))) ⇒ (a simeq b))
≔ begin
assume a b H;
refine ex_i (node arrow (node arrow prop)) (λ u, λ v, v = j u) _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_el _ _ H}
{assume x x' y H1;
refine ex_i node (j x') _ _;
refine and_i _ _ _ _
{refine imp_i (y = j x) _ _ _
{assume H2;
refine imp_i (j x = y) _ _ _
{assume H3;
refine H3 (λ w, eta b (j x') w) _;
refine (and_er _ _ ((and_er _ _ H) x (j x'))) (ex_i node x' _ (and_i _ _ (refl node (j x')) (and_el _ _ H1)))}
{refine sym node y (j x) H2}}
{refine and_er _ _ H1}}
{refine refl node (j x')}}}
{assume y y' x H4;
refine ex_e node _ ((and_el _ _ ((and_er _ _ H) x y')) _) _ _
{refine imp_i (j x = y) _ _ _
{assume H5;
refine imp_i (y = j x) _ _ _
{assume H6;
refine H6 (λ w, eta b y' w) _;
refine and_el _ _ H4}
{refine sym node (j x) y H5}}
{refine sym node y (j x) (and_er _ _ H4)}}
{assume x' Hx';
refine ex_i node x' _ _;
refine and_i _ _ (and_er _ _ Hx') (and_el _ _ Hx')}}
end;