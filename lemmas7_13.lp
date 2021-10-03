require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.lemmas1_6;

opaque symbol lemmaPred : π(∀ n (λ a, ∀ n (λ b, (a = b) ⇒ (Pred a = Pred b))))
≔ begin
assume a b Pegal;
apply Pegal (λ x, Pred a = Pred x);
assume P Pa;
apply Pa;
end;

opaque symbol lemma7 : π(∀ n (λ x, ∀ n (λ y, (Succ x = Succ y) ⇒ (x = y))))
≔ begin
assume x y Pegal ;
apply lemmaPred (Succ x) (Succ y) Pegal;
end;

opaque symbol lemma8 : π(∀ n (λ x, ¬(O = Succ x)))
≔ begin
assume x Pegal;
apply Pegal Null Vrai;
end;


opaque symbol lemmaI : π(∀ n (λ a, ∀ n (λ b, (a = b) ⇒ (i' a = i' b))))
≔ begin
assume a b Pegal;
apply Pegal (λ x, i' a = i' x);
assume P Pa;
apply Pa;
end;

opaque symbol lemma9 : π(∀ n (λ x, ∀ n (λ y, (i x = i y) ⇒ (x = y))))
≔ begin
assume x y Pegal;
apply lemmaI (i x) (i y) Pegal;
end;

opaque symbol lemmaJ : π(∀ n (λ a, ∀ n (λ b, (a = b) ⇒ (j' a = j' b))))
≔ begin
assume a b Pegal;
apply Pegal (λ x, j' a = j' x);
assume P Pa;
apply Pa;
end;

opaque symbol lemma10 : π(∀ n (λ x, ∀ n (λ y, (j x = j y) ⇒ (x = y))))
≔ begin
assume x y Pegal;
apply lemmaJ (j x) (j y) Pegal;
end;

opaque symbol lemma11 : π(∀ n (λ x, ¬(i x = o)))
≔ begin
assume x Pegal;
apply Pegal I Vrai;
end;

opaque symbol lemma12 : π(∀ n (λ x, ¬(j x = o)))
≔ begin
assume x Pegal;
apply Pegal J Vrai;
end;

opaque symbol lemma13 : π(∀ n (λ x, ∀ n (λ y, ¬(i x = j y))))
≔ begin
assume x y Pegal;
apply Pegal I Vrai;
end;
