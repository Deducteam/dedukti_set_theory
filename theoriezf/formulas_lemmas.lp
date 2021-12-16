require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.bisimilarity;
require open zf.theoriezf.injectivity;
require open zf.theoriezf.eta1;
require open zf.theoriezf.eta2;
require open zf.theoriezf.membership;
require open zf.theoriezf.formulas;
require open zf.theoriezf.nat;

opaque symbol lemmaUpdate1_1 : Π (σ : El nat → El graph), Π (a : El graph), Π (z x: El nat), π((update1 σ x a x z) simeq a)
≔ begin
assume σ a z;
refine recN _ _ _
{refine lemma3 a}
{assume x Hx;
simplify update1;
refine Hx}
end;

opaque symbol lemmaUpdate1_2 : Π (σ : El nat → El graph), Π (a : El graph), Π (z x y: El nat), π((¬ (eqNP x y)) ⇒ ((update1 σ x a y z) simeq (σ z)))
≔ begin
assume σ a z;
refine recN _ _ _
{refine recN _ _ _
//Cas x = 0, y = 0
{assume H0;
refine f_e _ _;
refine H0 _;
assume P P0;
refine P0}
//Cas x = 0, s y
{assume y Hrec Hy;
simplify update1;
refine lemma3 (σ z)}}
{assume x Hx;
refine recN _ _ _
//Cas s x, y = 0
{assume H0;
simplify update1;
refine lemma3 (σ z)}
//Cas s x, s y
{assume y Hrec Hy;
simplify update1;
refine Hx y _;
assume Hxy;
refine Hy _;
refine Hxy (λ z, eqNP (s x) (s z)) _;
refine lemmaNP (s x)}}
end;

opaque symbol lemmaUp1 : Π (σ : El nat → El graph), Π (x y z: El nat), Π (a : El graph), π(((eqNP x y) ⇒ (((update1 σ x a) y z) simeq a)) ∧ (¬(eqNP x y) ⇒ (((update1 σ x a) y z) simeq (σ z))))
≔ begin
assume σ x y z a;
refine and_i _ _ _ _
{assume H0;
refine imp_i (eqNP x y) _ _ _
{assume H;
refine imp_i (eqNP y x) _ _ _
{assume H';
refine H' (λ w, (update1 σ w a y z) simeq a) _;
refine lemmaUpdate1_1 σ a z y}
{refine lemmaSymNP x y H0}}
{refine H0}}
{assume H1;
refine lemmaUpdate1_2 σ a z x y H1}
end;

opaque symbol lemmaUp : Π (σ : El nat → El graph), Π (x : El nat), Π (a b : El graph), π((a simeq b) ⇒ (`∀ y, (update σ x a y) simeq (update σ x b y)))
≔ begin
assume σ x a b Hab y;
refine or_e _ _ _ (eqNPor x y) _ _
{assume H1;
refine lemma5 (update σ x a y) b (update σ x b y) (and_i _ _ _ _)
{refine lemma5 (update σ x a y) a b (and_i _ _ _ Hab);
simplify update;
refine (and_eg _ _ (lemmaUp1 σ x y y a)) H1}
{refine lemma4 (update σ x b y) b ((and_eg _ _ (lemmaUp1 σ x y y b)) H1)}}
{assume H0;
refine lemma5 (update σ x a y) (σ y) (update σ x b y) (and_i _ _ _ _)
{refine (and_ed _ _ (lemmaUp1 σ x y y a)) H0}
{refine lemma4 (update σ x b y) (σ y) ((and_ed _ _ (lemmaUp1 σ x y y b)) H0)}}
end;

opaque symbol lemmaUp3 : Π (σ : El nat → El graph), Π (x y : El nat), Π (a b c : El graph), π((a simeq b) ⇒ (`∀ z, (update (update σ x a) y c z) simeq (update (update σ x b) y c z)))
≔ begin
assume σ x y a b c Hab z;
refine or_e _ _ _ (eqNPor y z) _ _
{assume H1;
refine lemma5 (update (update σ x a) y c z) c (update (update σ x b) y c z) (and_i _ _ _ _)
{simplify update;
refine (and_eg _ _ (lemmaUp1 (update σ x a) y z z c)) H1}
{refine lemma4 (update (update σ x b) y c z) c ((and_eg _ _ (lemmaUp1 (update σ x b) y z z c)) H1)}}
{assume H0;
refine lemma5 (update (update σ x a) y c z) (update σ x a z ) (update (update σ x b) y c z) (and_i _ _ _ _)
{simplify update;
refine (and_ed _ _ (lemmaUp1 (update σ x a) y z z c)) H0}
{refine lemma5 (update σ x a z) (update σ x b z) (update (update σ x b) y c z) (and_i _ _ _ _)
{refine lemmaUp σ x a b Hab z}
{refine lemma4 (update (update σ x b) y c z) (update σ x b z) ((and_ed _ _ (lemmaUp1 (update σ x b) y z z c)) H0)}}}
end;

opaque symbol lemmaVal : Π (σ σ' : El nat → El graph), Π (x : El nat), Π (c : El graph), π ((`∀ y, σ y simeq σ' y) ⇒ (`∀ z, (update σ x c z) simeq (update σ' x c z)))
≔ begin
assume σ σ' x c H z;
refine or_e _ _ _ (eqNPor x z) _ _
{assume H1;
refine imp_i (eqNP z x) _ _ _
{assume H';
refine H' (λ w, (update1 σ w c z z) simeq (update1 σ' w c z z)) _;
refine lemma5 (update1 σ z c z z) c (update1 σ' z c z z) (and_i _ _ _ _)
{refine (and_eg _ _ (lemmaUp1 σ z z z c)) (lemmaNP z)}
{refine lemma4 (update1 σ' z c z z) c ((and_eg _ _ (lemmaUp1 σ' z z z c)) (lemmaNP z))}}
{refine lemmaSymNP x z H1}}
{assume H0;
simplify update;
refine lemma5 (update1 σ x c z z) (σ z) (update1 σ' x c z z) (and_i _ _ _ _)
{refine (and_ed _ _ (lemmaUp1 σ x z z c)) H0}
{refine lemma5 (σ z) (σ' z) (update1 σ' x c z z) (and_i _ _ _ _)
{refine H z}
{refine lemma4 (update1 σ' x c z z) (σ' z) ((and_ed _ _ (lemmaUp1 σ' x z z c)) H0)}}}
end;

opaque symbol lemmaInt : Π (f : El formula), π(`∀ σ : (El nat → El graph), `∀ σ' : (El nat → El graph), ((interpretation σ f) ∧ (`∀ x, (σ x) simeq (σ' x))) ⇒ (interpretation σ' f))
≔ begin
refine recF (λ f, `∀ σ, `∀ σ', ((interpretation σ f) ∧ (`∀ x, (σ x) simeq (σ' x))) ⇒ (interpretation σ' f)) _ _ _ _ _ _ _ _ _
{assume x y σ σ' Heq;
simplify interpretation;
refine lemma5 (σ' x) (σ y) (σ' y) (and_i _ _ _ (and_ed _ _ Heq y));
refine lemma5 (σ' x) (σ x) (σ y) (and_i _ _ _ (and_eg _ _ Heq));
refine lemma4 (σ x) (σ' x) (and_ed _ _ Heq x)}
{assume x y σ σ' Hin;
refine lemma31 (σ' x) (σ y) (σ' y) (and_i _ _ _ (and_ed _ _ Hin y));
refine lemma30 (σ x) (σ y) (σ' x) (and_i _ _ (and_eg _ _ Hin) (and_ed _ _ Hin x))}
{assume f graph Hfg σ σ' Hand;
refine and_i _ _ _ _
{refine (and_eg _ _ Hfg σ σ') (and_i _ _ (and_eg _ _ (and_eg _ _ Hand)) (and_ed _ _ Hand))}
{refine (and_ed _ _ Hfg σ σ') (and_i _ _ (and_ed _ _ (and_eg _ _ Hand)) (and_ed _ _ Hand))}}
{assume f graph Hfg σ σ' Hor;
refine or_e _ _ _ (and_eg _ _ Hor) _ _
{assume Hf;
refine or_ig _ _ _;
refine (and_eg _ _ Hfg σ σ') (and_i _ _ Hf (and_ed _ _ Hor))}
{assume Hg;
refine or_id _ _ _;
refine (and_ed _ _ Hfg σ σ') (and_i _ _ Hg (and_ed _ _ Hor))}}
{assume f graph Hfg σ σ' Himp Hf;
refine (and_ed _ _ Hfg σ σ') (and_i _ _ _ (and_ed _ _ Himp));
refine and_eg _ _ Himp _;
refine (and_eg _ _ Hfg σ' σ) (and_i _ _ Hf _);
assume x;
refine lemma4 (σ x) (σ' x) (and_ed _ _ Himp x)}
{assume f Hf x σ σ' Hall c;
refine Hf (update σ x c) (update σ' x c) (and_i _ _ (and_eg _ _ Hall c) _);
refine lemmaVal σ σ' x c (and_ed _ _ Hall)}
{assume f Hf x σ σ' Hex;
refine ExElim graph _ (and_eg _ _ Hex) _ _;
assume c Hc;
refine ExIntro graph c _ _;
refine Hf (update σ x c) (update σ' x c) (and_i _ _ Hc _);
refine lemmaVal σ σ' x c (and_ed _ _ Hex)}
{assume σ σ' H;
refine and_eg _ _ H}
{assume σ σ' H;
refine and_eg _ _ H}
end;
