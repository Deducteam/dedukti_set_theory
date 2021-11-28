require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.bisimilarity;
require open zf.theoriezf.injectivity;
require open zf.theoriezf.eta1;
require open zf.theoriezf.eta2;
require open zf.theoriezf.eta3;
require open zf.theoriezf.membership;
require open zf.theoriezf.formulas;

opaque symbol lemma33 : π(`∀ a, `∀ b, (((root b) = i (root a)) ∧ (`∀ x, `∀ y', ((eta b y' (i x)) ⇔ (`∃ x', (y' = (i x')) ∧ (eta a x' x))))) ⇒ (a simeq b))
≔ begin
assume a b H;
refine ExIntro (n arrow (n arrow omicron)) (λ u, λ v, v = i u) _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_eg _ _ H}
{assume x x' y H1;
refine ExIntro n (i x') _ _;
refine and_i _ _ _ _
{refine imp_i (y = i x) _ _ _
{assume H2;
refine imp_i (i x = y) _ _ _
{assume H3;
refine H3 (λ w, eta b (i x') w) _;
refine (and_ed _ _ ((and_ed _ _ H) x (i x'))) (ExIntro n x' _ (and_i _ _ (refl n (i x')) (and_eg _ _ H1)))}
{refine lemmaSymEg n y (i x) H2}}
{refine and_ed _ _ H1}}
{refine refl n (i x')}}}
{assume y y' x H4;
refine ExElim n _ ((and_eg _ _ ((and_ed _ _ H) x y')) _) _ _
{refine imp_i (i x = y) _ _ _
{assume H5;
refine imp_i (y = i x) _ _ _
{assume H6;
refine H6 (λ w, eta b y' w) _;
refine and_eg _ _ H4}
{refine lemmaSymEg n (i x) y H5}}
{refine lemmaSymEg n y (i x) (and_ed _ _ H4)}}
{assume x' Hx';
refine ExIntro n x' _ _;
refine and_i _ _ (and_ed _ _ Hx') (and_eg _ _ Hx')}}
end;

opaque symbol lemma34 : π(`∀ a, `∀ b, (((root b) = j (root a)) ∧ (`∀ x, `∀ y', ((eta b y' (j x)) ⇔ (`∃ x', (y' = (j x')) ∧ (eta a x' x))))) ⇒ (a simeq b))
≔ begin
assume a b H;
refine ExIntro (n arrow (n arrow omicron)) (λ u, λ v, v = j u) _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_eg _ _ H}
{assume x x' y H1;
refine ExIntro n (j x') _ _;
refine and_i _ _ _ _
{refine imp_i (y = j x) _ _ _
{assume H2;
refine imp_i (j x = y) _ _ _
{assume H3;
refine H3 (λ w, eta b (j x') w) _;
refine (and_ed _ _ ((and_ed _ _ H) x (j x'))) (ExIntro n x' _ (and_i _ _ (refl n (j x')) (and_eg _ _ H1)))}
{refine lemmaSymEg n y (j x) H2}}
{refine and_ed _ _ H1}}
{refine refl n (j x')}}}
{assume y y' x H4;
refine ExElim n _ ((and_eg _ _ ((and_ed _ _ H) x y')) _) _ _
{refine imp_i (j x = y) _ _ _
{assume H5;
refine imp_i (y = j x) _ _ _
{assume H6;
refine H6 (λ w, eta b y' w) _;
refine and_eg _ _ H4}
{refine lemmaSymEg n (j x) y H5}}
{refine lemmaSymEg n y (j x) (and_ed _ _ H4)}}
{assume x' Hx';
refine ExIntro n x' _ _;
refine and_i _ _ (and_ed _ _ Hx') (and_eg _ _ Hx')}}
end;