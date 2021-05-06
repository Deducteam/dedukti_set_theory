require open zf.theoriezf.logique;
require open zf.theoriezf.lemme1_6;
require open zf.theoriezf.lemme7_13;
require open zf.theoriezf.lemme14_18;
require open zf.theoriezf.lemme19_21;
require open zf.theoriezf.lemme22_27;
require open zf.theoriezf.lemme28_34;
require open zf.theoriezf.extension;

opaque symbol lemme35 : π(∀ g (λ a, ∀ n (λ y, (cr (join a) (i y)) simeq (cr a y))))
≔ begin
assume a y;
apply lemme4 (cr a y) (cr (join a) (i y)) (lemme33 (cr a y) (cr (join a) (i y)) _);
apply and_i;
apply lemme1 (i y);
assume x y';
apply lemme14 a y' x;
end;

opaque symbol lemme36 : π(∀ g (λ a, ∀ g (λ b, (cr (pair a b) (i (root a))) simeq a)))
≔ begin
assume a b;
apply lemme4 a (cr (pair a b) (i (root a))) (lemme33 a (cr (pair a b) (i (root a))) _);
apply and_i;
apply lemme1 (i (root a));
assume x y';
apply lemme16 a b y' x;
end;

opaque symbol lemme37 : π(∀ g (λ a, ∀ g (λ b, (cr (pair a b) (j (root b))) simeq b)))
≔ begin
assume a b;
apply lemme4 b (cr (pair a b) (j (root b))) (lemme34 b (cr (pair a b) (j (root b))) _);
apply and_i;
apply lemme1 (j (root b));
assume x y';
apply lemme17 a b y' x;
end;

opaque symbol lemme38 : π(∀ g (λ a, ∀ n (λ y, (cr (powerset a) (i y)) simeq (cr a y))))
≔ begin
assume a y;
apply lemme4 (cr a y) (cr (powerset a) (i y)) (lemme33 (cr a y) (cr (powerset a) (i y)) _);
apply and_i;
apply lemme1 (i y);
assume x y';
apply lemme19 a y' x;
end;

opaque symbol lemme39 : Π (σ : El valuation), Π (f : El formula), π(∀ g (λ a, ∀ n (λ y, (cr (comp a σ f) (i y)) simeq (cr a y))))
≔ begin
assume σ f a y;
apply lemme4 (cr a y) (cr (comp a σ f) (i y)) (lemme33 (cr a y) (cr (comp a σ f) (i y)) _);
apply and_i;
apply lemme1 (i y);
assume x y';
apply lemme22 σ f a y' x;
end;

opaque symbol lemme40 : π(∀ g (λ a, ∀ n (λ y, (cr (Cl a) (i y)) simeq (cr a y))))
≔ begin
assume a y;
apply lemme4 (cr a y) (cr (Cl a) (i y)) (lemme33 (cr a y) (cr (Cl a) (i y)) _);
apply and_i;
apply lemme1 (i y);
assume x y';
apply lemme26 a y' x;
end;
