require open zf.theoriezf.logique;
require open zf.theoriezf.lemme1_6;
require open zf.theoriezf.lemme7_13;
require open zf.theoriezf.lemme14_18;
require open zf.theoriezf.lemme19_21;
require open zf.theoriezf.lemme22_27;
require open zf.theoriezf.lemme28_34;
require open zf.theoriezf.lemme35_41;
require open zf.theoriezf.lemme42_45;

symbol empty_set : Graph;
symbol Ind : Graph → Prop;

rule empty_set ↪ comp omega (λ x, ⊥);
rule root empty_set ↪ o;
rule Ind $c ↪ (empty_set ∈ $c) ∧ (∀ g (λ a, (a ∈ $c) ⇒ ((join (pair a (pair a a))) ∈ $c)));

opaque symbol lemme46 : π(∀ g (λ a, ¬ (a ∈ empty_set)))
≔ begin
assume a;
simpl π;
assume H;
apply ExElim n _ H _;
assume x Hx;
apply ExElim n _ ((and_eg _ _ (lemme23 (λ x, ⊥) omega x)) (and_eg _ _ Hx)) _;
assume y Hy;
apply and_ed _ _ Hy;
end;

opaque symbol lemme47 : π(empty_set simeq (cr omega (i O)))
≔ begin
admitted;

opaque symbol lemme48 : π(∀ g (λ a, ∀ n (λ y, (a simeq (cr omega (i y))) ⇒ ((join (pair a (pair a a))) simeq (cr omega (i (Succ y)))))))
≔ begin
assume a y H;
admitted;

opaque symbol lemme49 : π(empty_set ∈ omega)
≔ begin
apply ExIntro n (i O) _ _;
apply and_i;
apply (and_ed _ _ (lemme25 (i O))) _;
apply ExIntro n O _ _;
apply and_i;
apply lemme1 (i O);
apply Vrai;
apply lemme47;
end;

opaque symbol lemme50 : π(∀ g (λ a, (a ∈ omega) ⇒ ((join (pair a (pair a a))) ∈ omega)))
≔ begin
assume a Ha;
apply ExElim n _ Ha _;
assume x Hx;
apply ExElim n _ ((and_eg _ _ (lemme25 x)) (and_eg _ _ Hx));
assume y Hy;
apply ExIntro n (i (Succ y)) _ _;
apply and_i;
apply (and_ed _ _ (lemme25 (i (Succ y)))) _;
apply ExIntro n (Succ y) _ _;
apply and_i;
apply lemme1 (i (Succ y));
apply and_ed _ _ Hy;
apply lemme48 a y _;
apply imp_i (i y = x) _ _ _;
assume H1;
apply imp_i (x = i y) _ _ _;
assume H2;
apply H2 (λ w, a simeq (cr omega w)) (and_ed _ _ Hx);
apply lemmeSymEg (i y) x H1;
apply lemmeSymEg x (i y) (and_eg _ _ Hy);
end;

opaque symbol lemme51 : π(Ind omega)
≔ begin
apply and_i;
apply lemme49;
apply lemme50;
end;