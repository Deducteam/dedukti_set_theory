require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.bisimilarity;
require open Logic.Z.injectivity;
require open Logic.Z.eta1;
require open Logic.Z.eta2;
require open Logic.Z.membership;
require open Logic.Z.lemma32;
require open Logic.Z.nat;
require open Logic.Z.formulas;
require open Logic.Z.formulas_lemmas;

opaque symbol lemma41 : Π (x y : El nat), Π (f : El formula), Π (c d : El graph), π(`∀ σ : (El nat → El graph), ((interpretation (update (update σ x c) y d) f)
∧ (`∀ a, `∀ a', `∀ b, ((a' ∈ a) ∧ (interpretation (update (update σ x a) y b) f)) ⇒ (`∃ b', ((b' ∈ b) ∧ (interpretation (update (update σ x a') y b') f))))
∧ (`∀ b, `∀ b', `∀ a, ((b' ∈ b) ∧ (interpretation (update (update σ x a) y b) f)) ⇒ (`∃ a', ((a' ∈ a) ∧ (interpretation (update (update σ x a') y b') f))))) ⇒ (c simeq d))
≔ begin
assume x y f c d σ H;
refine ex_i (node arrow (node arrow prop)) (λ u, λ v, interpretation (update (update σ x (cr c u)) y (cr d v)) f) _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine lemmaInt f (update (update σ x c) y (cr d (root d))) (update (update σ x (cr c (root c))) y (cr d (root d))) (and_i _ _ _ _)
{refine lemma32 y f d (cr d (root d)) (update σ x c) (and_i _ _ _ _)
{refine (and_el _ _ (and_el _ _ H))}
{refine lemma6 d}}
{refine lemmaUp3 σ x y c (cr c (root c)) (cr d (root d)) _;
refine lemma6 c}}
{assume u u' v Hu;
refine ex_e graph _ ((and_er _ _ (and_el _ _ H)) (cr c u) (cr c u') (cr d v) (and_i _ _ _ _)) _ _
{refine lemma28 (cr c u) u' (and_el _ _ Hu)}
{refine and_er _ _ Hu}
{assume b Hb;
refine ex_e node _ (and_el _ _ Hb) _ _;
assume v' Hv';
refine ex_i node v' _ _;
refine and_i _ _ _ _
{refine and_el _ _ Hv'}
{refine lemma32 y f b (cr d v') (update σ x (cr c u')) (and_i _ _ _ _)
{refine and_er _ _ Hb}
{refine and_er _ _ Hv'}}}}}
{assume v v' u Hv;
refine ex_e graph _ ((and_er _ _ H) (cr d v) (cr d v') (cr c u) (and_i _ _ _ _)) _ _
{refine lemma28 (cr d v) v' (and_el _ _ Hv)}
{refine and_er _ _ Hv}
{assume b Hb;
refine ex_e node _ (and_el _ _ Hb) _ _;
assume u' Hu';
refine ex_i node u' _ _;
refine and_i _ _ _ _
{refine and_el _ _ Hu'}
{refine lemmaInt f (update (update σ x b) y (cr d v')) (update (update σ x (cr c u')) y (cr d v')) (and_i _ _ _ _)
{refine and_er _ _ Hb}
{refine lemmaUp3 σ x y b (cr c u') (cr d v') _;
refine and_er _ _ Hu'}}}}
end;
