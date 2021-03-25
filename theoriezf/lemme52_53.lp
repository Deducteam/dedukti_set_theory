require open zf.theoriezf.logique;
require open zf.theoriezf.lemme1_6;
require open zf.theoriezf.lemme7_13;
require open zf.theoriezf.lemme14_18;
require open zf.theoriezf.lemme19_21;
require open zf.theoriezf.lemme22_27;
require open zf.theoriezf.lemme28_34;
require open zf.theoriezf.lemme35_41;
require open zf.theoriezf.lemme42_45;
//require open zf.theoriezf.lemme46_51;

opaque symbol lemme52 : π(∀ g (λ a, ∀ g (λ c, (a ∈ c) ⇒ (a ∈ (Cl c)))))
≔ begin
assume a c Hac;
apply ExElim n _ Hac _;
assume x Hx;
apply ExIntro n (i x) _ _;
apply and_i;
apply (and_ed _ _ (lemme27 c (i x))) _;
apply ExIntro n x _ _;
apply and_i;
apply lemme1 (i x);
assume P;
assume H;
apply (and_eg _ _ H) x (and_eg _ _ Hx);
apply lemme5 a (cr c x) (cr (Cl c) (i x)) (and_i _ _ (and_ed _ _ Hx) _);
apply lemme4 (cr (Cl c) (i x)) (cr c x) (lemme40 c x);
end;

opaque symbol lemme53 : π(∀ g (λ a, ∀ g (λ b, ∀ g (λ c, ((a ∈ b) ∧ (b ∈ (Cl c))) ⇒ (a ∈ (Cl c))))))
≔ begin
assume a b c H;
apply ExElim n _ (and_ed _ _ H) _;
assume u Hu;
apply ExElim n _ ((and_eg _ _ (lemme27 c u)) (and_eg _ _ Hu)) _;
assume x Hx;
apply ExElim n _ (and_eg _ _ H) _;
assume y Hy;
apply ExElim n _ ((lemme29 b (cr c x) _) y (and_eg _ _ Hy)) _;
apply lemme5 b (cr (Cl c) u) (cr c x) (and_i _ _ (and_ed _ _ Hu) _);
apply imp_i (u = i x) _ _ _;
assume H1;
apply imp_i (i x = u) _ _ _;
assume H2;
apply H2 (λ w, (cr (Cl c) w) simeq (cr c x)) (lemme40 c x);
apply lemmeSymEg u (i x) H1;
apply and_eg _ _ Hx;
assume z Hz;
apply ExIntro n (i z) _ _;
apply and_i;
apply (and_ed _ _ (lemme27 c (i z))) _;
apply ExIntro n z _ _;
apply and_i;
apply lemme1 (i z);
assume e He;
apply ((and_ed _ _ He) z x (and_i _ _ (and_eg _ _ Hz) ((and_ed _ _ Hx) e He)));
apply lemme5 a (cr b y) (cr (Cl c) (i z)) (and_i _ _ (and_ed _ _ Hy) _);
apply lemme5 (cr b y) (cr c z) (cr (Cl c) (i z)) (and_i _ _ (and_ed _ _ Hz) _);
apply lemme4 (cr (Cl c) (i z)) (cr c z) (lemme40 c z);
end;