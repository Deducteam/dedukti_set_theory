require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.bisimilarity;
require open zf.theoriezf.injectivity;
require open zf.theoriezf.eta1;

opaque symbol lemma28 : π(`∀ a, `∀ x, (eta a x (root a)) ⇒ ((cr a x) ∈ a))
≔ begin
assume a x H;
refine ExIntro n x _ _;
refine and_i _ _ _ _
{refine H}
{refine ExIntro (n arrow (n arrow omicron)) (λ p, λ q, p = q) _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine refl n (root (cr a x))}
{assume u u' v H1;
refine ExIntro n u' _ _;
refine and_i _ _ _ _
{refine imp_i (v = u) _ _ _
{assume H2;
refine imp_i (u = v) _ _ _
{assume H3;
refine H3 (λ w, eta (cr a x) u' w) (and_eg _ _ H1)}
{refine lemmaSymEg n v u H2}}
{refine lemmaSymEg n u v (and_ed _ _ H1)}}
{refine refl n u'}}}
{assume v v' u H4;
refine ExIntro n v' _ _;
refine and_i _ _ _ _
{refine imp_i (u = v) _ _ _
{assume H5;
refine imp_i (v = u) _ _ _
{assume H6;
refine H6 (λ w, eta (cr a x) v' w) (and_eg _ _ H4)}
{refine lemmaSymEg n u v H5}}
{refine and_ed _ _ H4}}
{refine refl n v'}}}
end;

opaque symbol lemma29 : π(`∀ a, `∀ b, (a simeq b) ⇒ (`∀ x, (eta a x (root a)) ⇒ (`∃ y, ((eta b y (root b)) ∧ ((cr a x) simeq (cr b y))))))
≔ begin
assume a b H x Heta;
refine ExElim (n arrow (n arrow omicron)) _ H _ _;
assume r Hr;
refine ExElim n _ ((and_ed _ _ (and_eg _ _ Hr)) (root a) x (root b) (and_i _ _ Heta (and_eg _ _ (and_eg _ _ Hr)))) _ _;
assume y Hy;
refine ExIntro n y _ _;
refine and_i _ _ _ _
{refine and_eg _ _ Hy}
{refine ExIntro (n arrow (n arrow omicron)) r _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_ed _ _ Hy}
{refine and_ed _ _  (and_eg _ _ Hr)}}
{refine and_ed _ _ Hr}}
end;

opaque symbol lemma30 : π(`∀ a, `∀ b, `∀ c, ((a ∈ b) ∧ (a simeq c)) ⇒ (c ∈ b))
≔ begin
assume a b c H;
refine ExElim n _ (and_eg _ _ H) _ _;
assume x Hx;
refine ExIntro n x _ _;
refine and_i _ _ _ _
{refine and_eg _ _ Hx}
{refine lemma5 c a (cr b x) (and_i _ _ (lemma4 a c (and_ed _ _ H)) (and_ed _ _ Hx))}
end;

opaque symbol lemma31 : π(`∀ a, `∀ b, `∀ c, ((a ∈ b) ∧ (b simeq c)) ⇒ (a ∈ c))
≔ begin
assume a b c H;
refine ExElim n _ (and_eg _ _ H) _ _;
assume x Hx;
refine ExElim n _ (lemma29 b c (and_ed _ _ H) x (and_eg _ _ Hx)) _ _;
assume y Hy;
refine ExIntro n y _ _;
refine and_i _ _ _ _
{refine and_eg _ _ Hy}
{refine lemma5 a (cr b x) (cr c y) (and_i _ _ (and_ed _ _ Hx) (and_ed _ _ Hy))}
end;
