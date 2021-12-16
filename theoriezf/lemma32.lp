require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.bisimilarity;
require open zf.theoriezf.injectivity;
require open zf.theoriezf.eta1;
require open zf.theoriezf.eta2;
require open zf.theoriezf.membership;
require open zf.theoriezf.nat;
require open zf.theoriezf.formulas;
require open zf.theoriezf.formulas_lemmas;

opaque symbol lemma32 : Π (z : El nat), Π (f : El formula), π(`∀ a, `∀ b, (`∀ σ : (El nat → El graph), ((interpretation (update σ z a) f) ∧ (a simeq b)) ⇒ (interpretation (update σ z b) f)))
≔ begin
assume z;
refine recF (λ f, `∀ a, `∀ b, `∀ σ, (interpretation (update σ z a) f ∧ (a simeq b)) ⇒ interpretation (update σ z b) f) _ _ _ _ _ _ _ _ _
{assume x y a b σ Heq;
refine lemma5 (update σ z b x) (update σ z a x) (update σ z b y) (and_i _ _ _ _)
{refine lemma4 (update σ z a x) (update σ z b x) (lemmaUp σ z a b (and_ed _ _ Heq) x)}
{refine lemma5 (update σ z a x) (update σ z a y) (update σ z b y) (and_i _ _ _ _)
{refine and_eg _ _ Heq}
{refine lemmaUp σ z a b (and_ed _ _ Heq) y}}}
{assume x y a b σ Hin;
refine lemma31 (update σ z b x) (update σ z a y) (update σ z b y) (and_i _ _ _ _)
{refine lemma30 (update σ z a x) (update σ z a y) (update σ z b x) (and_i _ _ _ _)
{refine and_eg _ _ Hin}
{refine lemmaUp σ z a b (and_ed _ _ Hin) x}}
{refine lemmaUp σ z a b (and_ed _ _ Hin) y}}
{assume f graph Hfg a b σ Hand;
refine and_i _ _ _ _
{refine ((and_eg _ _ Hfg) a b σ) (and_i _ _ (and_eg _ _ (and_eg _ _ Hand)) (and_ed _ _ Hand))}
{refine ((and_ed _ _ Hfg) a b σ) (and_i _ _ (and_ed _ _ (and_eg _ _ Hand)) (and_ed _ _ Hand))}}
{assume f graph Hfg a b σ Hor;
refine or_e _ _ _ (and_eg _ _ Hor) _ _
{assume Hf;
refine or_ig _ _ _;
refine ((and_eg _ _ Hfg) a b σ) (and_i _ _ Hf (and_ed _ _ Hor))}
{assume Hg;
refine or_id _ _ _;
refine ((and_ed _ _ Hfg) a b σ) (and_i _ _ Hg (and_ed _ _ Hor))}}
{assume f graph Hfg a b σ Himp Hf;
refine (and_ed _ _ Hfg a b σ) (and_i _ _ _ (and_ed _ _ Himp));
refine and_eg _ _ Himp _;
refine (and_eg _ _ Hfg b a σ) (and_i _ _ Hf _);
refine lemma4 a b (and_ed _ _ Himp)}
{assume f Hf x a b σ Hall c;
refine lemmaInt f (update (update σ z a) x c) (update (update σ z b) x c) (and_i _ _ _ _)
{refine (and_eg _ _ Hall) c}
{refine (lemmaUp3 σ z x a b c) (and_ed _ _ Hall)}}
{assume f Hf x a b σ Hex;
refine ExElim graph _ (and_eg _ _ Hex) _ _;
assume c Hc;
refine ExIntro graph c _ _;
refine lemmaInt f (update (update σ z a) x c) (update (update σ z b) x c) (and_i _ _ _ _)
{refine Hc}
{refine (lemmaUp3 σ z x a b c) (and_ed _ _ Hex)}}
{assume a b σ H;
refine and_eg _ _ H}
{assume a b σ H;
refine and_eg _ _ H}
end;