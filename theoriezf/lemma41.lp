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

opaque symbol lemma41 : Π (x y : El nat), Π (f : El formula), Π (c d : El graph), π(`∀ σ : (El nat → El graph), ((interpretation (update (update σ x c) y d) f)
∧ (`∀ a, `∀ a', `∀ b, ((a' ∈ a) ∧ (interpretation (update (update σ x a) y b) f)) ⇒ (`∃ b', ((b' ∈ b) ∧ (interpretation (update (update σ x a') y b') f))))
∧ (`∀ b, `∀ b', `∀ a, ((b' ∈ b) ∧ (interpretation (update (update σ x a) y b) f)) ⇒ (`∃ a', ((a' ∈ a) ∧ (interpretation (update (update σ x a') y b') f))))) ⇒ (c simeq d))
≔ begin
assume x y f c d σ H;
refine ExIntro (node arrow (node arrow prop)) (λ u, λ v, interpretation (update (update σ x (cr c u)) y (cr d v)) f) _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine lemmaInt f (update (update σ x c) y (cr d (root d))) (update (update σ x (cr c (root c))) y (cr d (root d))) (and_i _ _ _ _)
{refine lemma32 y f d (cr d (root d)) (update σ x c) (and_i _ _ _ _)
{refine (and_eg _ _ (and_eg _ _ H))}
{refine lemma6 d}}
{refine lemmaUp2 σ x y c (cr c (root c)) (cr d (root d)) _;
refine lemma6 c}}
{assume u u' v Hu;
refine ExElim graph _ ((and_ed _ _ (and_eg _ _ H)) (cr c u) (cr c u') (cr d v) (and_i _ _ _ _)) _ _
{refine lemma28 (cr c u) u' (and_eg _ _ Hu)}
{refine and_ed _ _ Hu}
{assume b Hb;
refine ExElim node _ (and_eg _ _ Hb) _ _;
assume v' Hv';
refine ExIntro node v' _ _;
refine and_i _ _ _ _
{refine and_eg _ _ Hv'}
{refine lemma32 y f b (cr d v') (update σ x (cr c u')) (and_i _ _ _ _)
{refine and_ed _ _ Hb}
{refine and_ed _ _ Hv'}}}}}
{assume v v' u Hv;
refine ExElim graph _ ((and_ed _ _ H) (cr d v) (cr d v') (cr c u) (and_i _ _ _ _)) _ _
{refine lemma28 (cr d v) v' (and_eg _ _ Hv)}
{refine and_ed _ _ Hv}
{assume b Hb;
refine ExElim node _ (and_eg _ _ Hb) _ _;
assume u' Hu';
refine ExIntro node u' _ _;
refine and_i _ _ _ _
{refine and_eg _ _ Hu'}
{refine lemmaInt f (update (update σ x b) y (cr d v')) (update (update σ x (cr c u')) y (cr d v')) (and_i _ _ _ _)
{refine and_ed _ _ Hb}
{refine lemmaUp2 σ x y b (cr c u') (cr d v') _;
refine and_ed _ _ Hu'}}}}
end;
