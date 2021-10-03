require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.lemmas1_6;
require open zf.theoriezf.lemmas7_13;
require open zf.theoriezf.lemmas14_18;
require open zf.theoriezf.lemmas19_21;
require open zf.theoriezf.lemmas22_27;
require open zf.theoriezf.lemmas28_34;
require open zf.theoriezf.formulas;

opaque symbol lemma35 : π(∀ g (λ a, ∀ n (λ y, (cr (join a) (i y)) simeq (cr a y))))
≔ begin
assume a y;
apply lemma4 (cr a y) (cr (join a) (i y)) (lemma33 (cr a y) (cr (join a) (i y)) _);
apply and_i;
apply lemma1 (i y);
assume x y';
apply lemma14 a y' x;
end;

opaque symbol lemma36 : π(∀ g (λ a, ∀ g (λ b, (cr (pair a b) (i (root a))) simeq a)))
≔ begin
assume a b;
apply lemma4 a (cr (pair a b) (i (root a))) (lemma33 a (cr (pair a b) (i (root a))) _);
apply and_i;
apply lemma1 (i (root a));
assume x y';
apply lemma16 a b y' x;
end;

opaque symbol lemma37 : π(∀ g (λ a, ∀ g (λ b, (cr (pair a b) (j (root b))) simeq b)))
≔ begin
assume a b;
apply lemma4 b (cr (pair a b) (j (root b))) (lemma34 b (cr (pair a b) (j (root b))) _);
apply and_i;
apply lemma1 (j (root b));
assume x y';
apply lemma17 a b y' x;
end;

opaque symbol lemma38 : π(∀ g (λ a, ∀ n (λ y, (cr (powerset a) (i y)) simeq (cr a y))))
≔ begin
assume a y;
apply lemma4 (cr a y) (cr (powerset a) (i y)) (lemma33 (cr a y) (cr (powerset a) (i y)) _);
apply and_i;
apply lemma1 (i y);
assume x y';
apply lemma19 a y' x;
end;

opaque symbol lemma39 : Π (σ : El valuation), Π (f : El formula), π(∀ g (λ a, ∀ n (λ y, (cr (comp a σ f) (i y)) simeq (cr a y))))
≔ begin
assume σ f a y;
apply lemma4 (cr a y) (cr (comp a σ f) (i y)) (lemma33 (cr a y) (cr (comp a σ f) (i y)) _);
apply and_i;
apply lemma1 (i y);
assume x y';
apply lemma22 σ f a y' x;
end;

opaque symbol lemma40 : π(∀ g (λ a, ∀ n (λ y, (cr (Cl a) (i y)) simeq (cr a y))))
≔ begin
assume a y;
apply lemma4 (cr a y) (cr (Cl a) (i y)) (lemma33 (cr a y) (cr (Cl a) (i y)) _);
apply and_i;
apply lemma1 (i y);
assume x y';
apply lemma26 a y' x;
end;
