require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.nat;
require open Logic.Z.bisimilarity;
require open Logic.Z.injectivity;
require open Logic.Z.eta1;
require open Logic.Z.eta2;
require open Logic.Z.eta3;
require open Logic.Z.relocation;
require open Logic.Z.membership;
require open Logic.Z.formulas;
require open Logic.Z.language2;

opaque symbol lemma35 : π(`∀ a, `∀ y, (cr (join a) (i y)) simeq (cr a y))
≔ begin
assume a y;
refine lemma4 (cr a y) (cr (join a) (i y)) (lemma33 (cr a y) (cr (join a) (i y)) _);
refine and_i _ _ _ _
{refine refl node (i y)}
{assume x y';
refine lemma14 a y' x}
end;

opaque symbol lemma36 : π(`∀ a, `∀ b, (cr (pair a b) (i (root a))) simeq a)
≔ begin
assume a b;
refine lemma4 a (cr (pair a b) (i (root a))) (lemma33 a (cr (pair a b) (i (root a))) _);
refine and_i _ _ _ _
{refine refl node (i (root a))}
{assume x y';
refine lemma16 a b y' x}
end;

opaque symbol lemma37 : π(`∀ a, `∀ b, (cr (pair a b) (j (root b))) simeq b)
≔ begin
assume a b;
refine lemma4 b (cr (pair a b) (j (root b))) (lemma34 b (cr (pair a b) (j (root b))) _);
refine and_i _ _ _ _
{refine refl node (j (root b))}
{assume x y';
refine lemma17 a b y' x}
end;

opaque symbol lemma38 : π(`∀ a, `∀ y, (cr (powerset a) (i y)) simeq (cr a y))
≔ begin
assume a y;
refine lemma4 (cr a y) (cr (powerset a) (i y)) (lemma33 (cr a y) (cr (powerset a) (i y)) _);
refine and_i _ _ _ _
{refine refl node (i y)}
{assume x y';
refine lemma19 a y' x}
end;

opaque symbol lemma39 : Π (σ : (El nat → El graph)), Π (f : El formula), π(`∀ a, `∀ y, (cr (comp a σ f) (i y)) simeq (cr a y))
≔ begin
assume σ f a y;
refine lemma4 (cr a y) (cr (comp a σ f) (i y)) (lemma33 (cr a y) (cr (comp a σ f) (i y)) _);
refine and_i _ _ _ _
{refine refl node (i y)}
{assume x y';
refine lemma22 σ f a y' x}
end;

opaque symbol lemma40 : π(`∀ a, `∀ y, (cr (closure a) (i y)) simeq (cr a y))
≔ begin
assume a y;
refine lemma4 (cr a y) (cr (closure a) (i y)) (lemma33 (cr a y) (cr (closure a) (i y)) _);
refine and_i _ _ _ _
{refine refl node (i y)}
{assume x y';
refine lemma26 a y' x}
end;
