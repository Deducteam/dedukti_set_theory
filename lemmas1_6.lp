require open zf.theoriezf.logic;
require open zf.theoriezf.language;

opaque symbol lemma1 : π(∀ n (λ x, x = x)) ≔
begin
assume y P Py;
apply Py;
end;

opaque symbol lemmaSymEg : π(∀ n (λ x, ∀ n (λ y, (x = y) ⇒ (y = x)))) 
≔ begin
assume x y Pxy P;
apply Pxy (λ z, (P z) ⇒ (P x));
assume Px;
apply lemma1 x P Px;
end;

opaque symbol lemma3 : π(∀ g (λ a, a simeq a))
≔ begin
assume a;
apply ExIntro relat (λ a, λ b, a = b) _ _;
apply and_i;
apply and_i;
apply lemma1 (root a);
assume x x' y H;
apply ExIntro n x' _ _;
apply and_i;
apply imp_e (x = y) (eta a x' y);
assume Heq;
apply Heq (λ w, eta a x' w);
apply and_eg _ _ H;
apply and_ed _ _ H;
apply lemma1 x';
assume y y' x H;
apply ExIntro n y' _ _;
apply and_i;
apply imp_e (y = x) (eta a y' x);
assume Heq;
apply Heq (λ w, eta a y' w);
apply and_eg _ _ H;
apply lemmaSymEg x y (and_ed (eta a y' y) (x = y) H);
apply lemma1 y';
end;

opaque symbol lemma4 : π(∀ g (λ a, ∀ g (λ b, (a simeq b) ⇒ (b simeq a))))
≔ begin
assume a b H;
apply ExElim relat _ H _;
assume r Hr;
apply ExIntro relat (λ x, λ y, r y x) _ _;
apply and_i;
apply and_i;
apply and_eg _ _ (and_eg _ _ Hr);
assume y y' x H1;
apply ((and_ed _ _ Hr) y y' x) H1; 
assume x x' y H2;
apply and_ed _ _ (and_eg _ _ Hr) x x' y H2;
end;

opaque symbol lemma5 : π(∀ g (λ a, ∀ g (λ b, ∀ g (λ c, ((a simeq b) ∧ (b simeq c)) ⇒ (a simeq c)))))
≔ begin
assume a b c H;
apply ExElim relat _ (and_eg _ _ H) _;
assume rab Hab;
apply ExElim relat _ (and_ed _ _ H) _;
assume rbc Hbc;
apply ExIntro relat (λ x, λ z, ∃ n (λ y, rab x y ∧ rbc y z)) _ _;
apply and_i;
apply and_i;
apply ExIntro n (root b) _ _;
apply and_i _ _ (and_eg _ _ (and_eg _ _ Hab)) (and_eg _ _ (and_eg _ _ Hbc));
assume x x' y H1;
apply ExElim n _ (and_ed _ _ H1);
assume u Hu;
apply ExElim n _ (imp_e _ _ ((and_ed _ _ (and_eg _ _ Hab)) x x' u) (and_i _ _ (and_eg _ _ H1) (and_eg _ _ Hu))) _;
assume v Hv;
apply ExElim n _ (imp_e _ _ ((and_ed _ _ (and_eg _ _ Hbc)) u v y) (and_i _ _ (and_eg _ _ Hv) (and_ed _ _ Hu))) _;
assume y' H2;
apply ExIntro n y' _ _;
apply and_i;
apply (and_eg _ _ H2);
apply ExIntro n v _ _;
apply (and_i _ _ (and_ed _ _ Hv) (and_ed _ _ H2));
assume y y' x H3;
apply ExElim n _ (and_ed _ _ H3);
assume u Hu;
apply ExElim n _ (imp_e _ _ ((and_ed _ _ Hbc) y y' u) (and_i _ _ (and_eg _ _ H3) (and_ed _ _ Hu))) _;
assume v Hv;
apply ExElim n _ (imp_e _ _ ((and_ed _ _ Hab) u v x) (and_i _ _ (and_eg _ _ Hv) (and_eg _ _ Hu))) _;
assume x' H4;
apply ExIntro n x' _ _;
apply and_i;
apply (and_eg _ _ H4);
apply ExIntro n v _ _;
apply (and_i _ _ (and_ed _ _ H4) (and_ed _ _ Hv));
end;

opaque symbol lemma6 : π(∀ g (λ a, a simeq (cr a (root a))))
≔ begin
assume a;
apply ExIntro relat (λ x, λ y, x = y) _ _;
apply and_i;
apply and_i;
apply lemma1 _;
assume x x' y H;
apply ExIntro n x' _ _;
apply and_i;
apply imp_e (eta a x' x) _;
assume H1;
apply imp_e (x = y) _;
assume H2;
apply H2 (λ z, eta a x' z) H1;
apply and_ed _ _ H;
apply and_eg _ _ H;
apply lemma1 _;
assume y y' x H;
apply ExIntro n y' _ _;
apply and_i;
apply imp_e (eta a y' y) _;
assume H1;
apply imp_e (x = y) _;
assume H2;
apply imp_e (y = x) _;
assume H3;
apply H3 (λ z, eta a y' z) H1;
apply lemmaSymEg _ _ H2;
apply and_ed _ _ H;
apply and_eg _ _ H;
apply lemma1 _;
end;
