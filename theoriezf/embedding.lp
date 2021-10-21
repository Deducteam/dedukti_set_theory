require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.bisimilarity;
require open zf.theoriezf.injectivity;
require open zf.theoriezf.eta1;
require open zf.theoriezf.eta2;
require open zf.theoriezf.eta3;
require open zf.theoriezf.relocation;
require open zf.theoriezf.membership;
require open zf.theoriezf.formulas;

opaque symbol lemma35 : π(`∀ a, `∀ y, (cr (join a) (i y)) simeq (cr a y))
≔ begin
assume a y;
refine lemma4 (cr a y) (cr (join a) (i y)) (lemma33 (cr a y) (cr (join a) (i y)) _);
refine and_i _ _ _ _;
refine refl n (i y);
assume x y';
refine lemma14 a y' x;
end;

opaque symbol lemma36 : π(`∀ a, `∀ b, (cr (pair a b) (i (root a))) simeq a)
≔ begin
assume a b;
refine lemma4 a (cr (pair a b) (i (root a))) (lemma33 a (cr (pair a b) (i (root a))) _);
refine and_i _ _ _ _;
refine refl n (i (root a));
assume x y';
refine lemma16 a b y' x;
end;

opaque symbol lemma37 : π(`∀ a, `∀ b, (cr (pair a b) (j (root b))) simeq b)
≔ begin
assume a b;
refine lemma4 b (cr (pair a b) (j (root b))) (lemma34 b (cr (pair a b) (j (root b))) _);
refine and_i _ _ _ _;
refine refl n (j (root b));
assume x y';
refine lemma17 a b y' x;
end;

opaque symbol lemma38 : π(`∀ a, `∀ y, (cr (powerset a) (i y)) simeq (cr a y))
≔ begin
assume a y;
refine lemma4 (cr a y) (cr (powerset a) (i y)) (lemma33 (cr a y) (cr (powerset a) (i y)) _);
refine and_i _ _ _ _;
refine refl n (i y);
assume x y';
refine lemma19 a y' x;
end;

opaque symbol lemma39 : Π (σ : El valuation), Π (f : El formula), π(`∀ a, `∀ y, (cr (comp a σ f) (i y)) simeq (cr a y))
≔ begin
assume σ f a y;
refine lemma4 (cr a y) (cr (comp a σ f) (i y)) (lemma33 (cr a y) (cr (comp a σ f) (i y)) _);
refine and_i _ _ _ _;
refine refl n (i y);
assume x y';
refine lemma22 σ f a y' x;
end;

opaque symbol lemma40 : π(`∀ a, `∀ y, (cr (Cl a) (i y)) simeq (cr a y))
≔ begin
assume a y;
refine lemma4 (cr a y) (cr (Cl a) (i y)) (lemma33 (cr a y) (cr (Cl a) (i y)) _);
refine and_i _ _ _ _;
refine refl n (i y);
assume x y';
refine lemma26 a y' x;
end;
