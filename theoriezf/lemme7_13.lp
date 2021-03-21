require open zf.theoriezf.logique;
require open zf.theoriezf.lemme1_6;

opaque symbol lemmePred : π(∀ n (λ a, ∀ n (λ b, (a = b) ⇒ (Pred a = Pred b))))
≔ begin
assume a b Pegal;
apply Pegal (λ x, Pred a = Pred x);
assume P Pa;
apply Pa;
end;

opaque symbol lemme7 : π(∀ n (λ x, ∀ n (λ y, (Succ x = Succ y) ⇒ (x = y))))
≔ begin
assume x y Pegal ;
apply lemmePred (Succ x) (Succ y) Pegal;
end;

opaque symbol lemme8 : π(∀ n (λ x, ¬(O = Succ x)))
≔ begin
assume x Pegal;
apply Pegal Null Vrai;
end;


opaque symbol lemmeI : π(∀ n (λ a, ∀ n (λ b, (a = b) ⇒ (i' a = i' b))))
≔ begin
assume a b Pegal;
apply Pegal (λ x, i' a = i' x);
assume P Pa;
apply Pa;
end;

opaque symbol lemme9 : π(∀ n (λ x, ∀ n (λ y, (i x = i y) ⇒ (x = y))))
≔ begin
assume x y Pegal;
apply lemmeI (i x) (i y) Pegal;
end;

opaque symbol lemmeJ : π(∀ n (λ a, ∀ n (λ b, (a = b) ⇒ (j' a = j' b))))
≔ begin
assume a b Pegal;
apply Pegal (λ x, j' a = j' x);
assume P Pa;
apply Pa;
end;

opaque symbol lemme10 : π(∀ n (λ x, ∀ n (λ y, (j x = j y) ⇒ (x = y))))
≔ begin
assume x y Pegal;
apply lemmeJ (j x) (j y) Pegal;
end;

opaque symbol lemme11 : π(∀ n (λ x, ¬(i x = o)))
≔ begin
assume x Pegal;
apply Pegal I Vrai;
end;

opaque symbol lemme12 : π(∀ n (λ x, ¬(j x = o)))
≔ begin
assume x Pegal;
apply Pegal J Vrai;
end;

opaque symbol lemme13 : π(∀ n (λ x, ∀ n (λ y, ¬(i x = j y))))
≔ begin
assume x y Pegal;
apply Pegal I Vrai;
end;