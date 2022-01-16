require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.bisimilarity;
require open Logic.Z.injectivity;
require open Logic.Z.eta1;
require open Logic.Z.eta2;
require open Logic.Z.membership;
require open Logic.Z.nat;
require open Logic.Z.formulas;
require open Logic.Z.formulas_lemmas;

opaque symbol lemma32 : Π (z : El nat), Π (f : El formula), π(`∀ a, `∀ b, (`∀ σ : (El nat → El graph), ((interpretation (update σ z a) f) ∧ (a simeq b)) ⇒ (interpretation (update σ z b) f)))
≔ begin
assume z;
refine recF (λ f, `∀ a, `∀ b, `∀ σ, (interpretation (update σ z a) f ∧ (a simeq b)) ⇒ interpretation (update σ z b) f) _ _ _ _ _ _ _ _ _
{assume x y a b σ Heq;
refine lemma5 (update σ z b x) (update σ z a x) (update σ z b y) (and_i _ _ _ _)
{refine lemma4 (update σ z a x) (update σ z b x) (lemmaUp σ z a b (and_er _ _ Heq) x)}
{refine lemma5 (update σ z a x) (update σ z a y) (update σ z b y) (and_i _ _ _ _)
{refine and_el _ _ Heq}
{refine lemmaUp σ z a b (and_er _ _ Heq) y}}}
{assume x y a b σ Hin;
refine lemma31 (update σ z b x) (update σ z a y) (update σ z b y) (and_i _ _ _ _)
{refine lemma30 (update σ z a x) (update σ z a y) (update σ z b x) (and_i _ _ _ _)
{refine and_el _ _ Hin}
{refine lemmaUp σ z a b (and_er _ _ Hin) x}}
{refine lemmaUp σ z a b (and_er _ _ Hin) y}}
{assume f graph Hfg a b σ Hand;
refine and_i _ _ _ _
{refine ((and_el _ _ Hfg) a b σ) (and_i _ _ (and_el _ _ (and_el _ _ Hand)) (and_er _ _ Hand))}
{refine ((and_er _ _ Hfg) a b σ) (and_i _ _ (and_er _ _ (and_el _ _ Hand)) (and_er _ _ Hand))}}
{assume f graph Hfg a b σ Hor;
refine or_e _ _ _ (and_el _ _ Hor) _ _
{assume Hf;
refine or_il _ _ _;
refine ((and_el _ _ Hfg) a b σ) (and_i _ _ Hf (and_er _ _ Hor))}
{assume Hg;
refine or_ir _ _ _;
refine ((and_er _ _ Hfg) a b σ) (and_i _ _ Hg (and_er _ _ Hor))}}
{assume f graph Hfg a b σ Himp Hf;
refine (and_er _ _ Hfg a b σ) (and_i _ _ _ (and_er _ _ Himp));
refine and_el _ _ Himp _;
refine (and_el _ _ Hfg b a σ) (and_i _ _ Hf _);
refine lemma4 a b (and_er _ _ Himp)}
{assume f Hf x a b σ Hall c;
refine lemmaInt f (update (update σ z a) x c) (update (update σ z b) x c) (and_i _ _ _ _)
{refine (and_el _ _ Hall) c}
{refine (lemmaUp3 σ z x a b c) (and_er _ _ Hall)}}
{assume f Hf x a b σ Hex;
refine ex_e graph _ (and_el _ _ Hex) _ _;
assume c Hc;
refine ex_i graph c _ _;
refine lemmaInt f (update (update σ z a) x c) (update (update σ z b) x c) (and_i _ _ _ _)
{refine Hc}
{refine (lemmaUp3 σ z x a b c) (and_er _ _ Hex)}}
{assume a b σ H;
refine and_el _ _ H}
{assume a b σ H;
refine and_el _ _ H}
end;