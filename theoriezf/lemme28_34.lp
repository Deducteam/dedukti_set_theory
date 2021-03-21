require open zf.theoriezf.logique;
require open zf.theoriezf.lemme1_6;
require open zf.theoriezf.lemme7_13;
require open zf.theoriezf.lemme14_18;
//require open zf.theoriezf.lemme19_21;
//require open zf.theoriezf.lemme22_27;

opaque symbol lemme28 : π(∀ g (λ a, ∀ n (λ x, (eta a x (root a)) ⇒ ((cr a x) ∈ a))))
≔ begin
assume a x H;
apply ExIntro n x _ _;
apply and_i;
apply H;
apply ExIntro relat (λ p, λ q, p = q) _ _;
apply and_i;
apply and_i;
apply lemme1 (root (cr a x));
assume u u' v H1;
apply ExIntro n u' _ _;
apply and_i;
apply imp_i (v = u) _ _ _;
assume H2;
apply imp_i (u = v) _ _ _;
assume H3;
apply H3 (λ w, eta (cr a x) u' w) (and_eg _ _ H1);
apply lemmeSymEg v u H2;
apply lemmeSymEg u v (and_ed _ _ H1);
apply lemme1 u';
assume v v' u H4;
apply ExIntro n v' _ _;
apply and_i;
apply imp_i (u = v) _ _ _;
assume H5;
apply imp_i (v = u) _ _ _;
assume H6;
apply H6 (λ w, eta (cr a x) v' w) (and_eg _ _ H4);
apply lemmeSymEg u v H5;
apply and_ed _ _ H4;
apply lemme1 v';
end;

opaque symbol lemme29 : π(∀ g (λ a, ∀ g (λ b, (a simeq b) ⇒ (∀ n (λ x, (eta a x (root a)) ⇒ (∃ n (λ y, ((eta b y (root b)) ∧ ((cr a x) simeq (cr b y))))))))))
≔ begin
assume a b H x Heta;
apply ExElim relat _ H _;
assume r Hr;
apply ExElim n _ ((and_ed _ _ (and_eg _ _ Hr)) (root a) x (root b) (and_i _ _ Heta (and_eg _ _ (and_eg _ _ Hr)))) _;
assume y Hy;
apply ExIntro n y _ _;
apply and_i;
apply and_eg _ _ Hy;
apply ExIntro relat r _ _;
apply and_i;
apply and_i;
apply and_ed _ _ Hy;
apply and_ed _ _  (and_eg _ _ Hr);
apply and_ed _ _ Hr;
end;

opaque symbol lemme30 : π(∀ g (λ a, ∀ g (λ b, ∀ g (λ c, ((a ∈ b) ∧ (a simeq c)) ⇒ (c ∈ b)))))
≔ begin
assume a b c H;
apply ExElim n _ (and_eg _ _ H) _;
assume x Hx;
apply ExIntro n x _ _;
apply and_i;
apply and_eg _ _ Hx;
apply lemme5 c a (cr b x) (and_i _ _ (lemme4 a c (and_ed _ _ H)) (and_ed _ _ Hx));
end;

opaque symbol lemme31 : π(∀ g (λ a, ∀ g (λ b, ∀ g (λ c, ((a ∈ b) ∧ (b simeq c)) ⇒ (a ∈ c)))))
≔ begin
assume a b c H;
apply ExElim n _ (and_eg _ _ H) _;
assume x Hx;
apply ExElim n _ (lemme29 b c (and_ed _ _ H) x (and_eg _ _ Hx)) _;
assume y Hy;
apply ExIntro n y _ _;
apply and_i;
apply and_eg _ _ Hy;
apply lemme5 a (cr b x) (cr c y) (and_i _ _ (and_ed _ _ Hx) (and_ed _ _ Hy));
end;

opaque symbol lemme33 : π(∀ g (λ a, ∀ g (λ b, (((root b) = i (root a)) ∧ (∀ n (λ x, ∀ n (λ y', ((eta b y' (i x)) ⇔ (∃ n (λ x', (y' = (i x')) ∧ (eta a x' x)))))))) ⇒ (a simeq b))))
≔ begin
assume a b H;
apply ExIntro relat (λ u, λ v, v = i u) _ _;
apply and_i;
apply and_i;
apply and_eg _ _ H;
assume x x' y H1;
apply ExIntro n (i x') _ _;
apply and_i;
apply imp_i (y = i x) _ _ _;
assume H2;
apply imp_i (i x = y) _ _ _;
assume H3;
apply H3 (λ w, eta b (i x') w);
apply (and_ed _ _ ((and_ed _ _ H) x (i x'))) (ExIntro n x' _ (and_i _ _ (lemme1 (i x')) (and_eg _ _ H1)));
apply lemmeSymEg y (i x) H2;
apply and_ed _ _ H1;
apply lemme1 (i x');
assume y y' x H4;
apply ExElim n _ ((and_eg _ _ ((and_ed _ _ H) x y')) _) _;
apply imp_i (i x = y) _ _ _;
assume H5;
apply imp_i (y = i x) _ _ _;
assume H6;
apply H6 (λ w, eta b y' w);
apply and_eg _ _ H4;
apply lemmeSymEg (i x) y H5;
apply lemmeSymEg y (i x) (and_ed _ _ H4);
assume x' Hx';
apply ExIntro n x' _ _;
apply and_i _ _ (and_ed _ _ Hx') (and_eg _ _ Hx');
end;

opaque symbol lemme34 : π(∀ g (λ a, ∀ g (λ b, (((root b) = j (root a)) ∧ (∀ n (λ x, ∀ n (λ y', ((eta b y' (j x)) ⇔ (∃ n (λ x', (y' = (j x')) ∧ (eta a x' x)))))))) ⇒ (a simeq b))))
≔ begin
assume a b H;
apply ExIntro relat (λ u, λ v, v = j u) _ _;
apply and_i;
apply and_i;
apply and_eg _ _ H;
assume x x' y H1;
apply ExIntro n (j x') _ _;
apply and_i;
apply imp_i (y = j x) _ _ _;
assume H2;
apply imp_i (j x = y) _ _ _;
assume H3;
apply H3 (λ w, eta b (j x') w);
apply (and_ed _ _ ((and_ed _ _ H) x (j x'))) (ExIntro n x' _ (and_i _ _ (lemme1 (j x')) (and_eg _ _ H1)));
apply lemmeSymEg y (j x) H2;
apply and_ed _ _ H1;
apply lemme1 (j x');
assume y y' x H4;
apply ExElim n _ ((and_eg _ _ ((and_ed _ _ H) x y')) _) _;
apply imp_i (j x = y) _ _ _;
assume H5;
apply imp_i (y = j x) _ _ _;
assume H6;
apply H6 (λ w, eta b y' w);
apply and_eg _ _ H4;
apply lemmeSymEg (j x) y H5;
apply lemmeSymEg y (j x) (and_ed _ _ H4);
assume x' Hx';
apply ExIntro n x' _ _;
apply and_i _ _ (and_ed _ _ Hx') (and_eg _ _ Hx');
end;