require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.bisimilarity;

opaque symbol lemmaPred : π(`∀ a, `∀ b, (a = b) ⇒ (Pred a = Pred b))
≔ begin
assume a b Pegal;
refine Pegal (λ x, Pred a = Pred x) _;
assume P Pa;
refine Pa
end;

opaque symbol lemma7 : π(`∀ x, `∀ y, (Succ x = Succ y) ⇒ (x = y))
≔ begin
assume x y Pegal ;
refine lemmaPred (Succ x) (Succ y) Pegal
end;

opaque symbol lemma8 : π(`∀ x, ¬(O = Succ x))
≔ begin
assume x Pegal;
refine Pegal Null top_i
end;


opaque symbol lemmaI : π(`∀ a, `∀ b, (a = b) ⇒ (i' a = i' b))
≔ begin
assume a b Pegal;
refine Pegal (λ x, i' a = i' x) _;
assume P Pa;
refine Pa
end;

opaque symbol lemma9 : π(`∀ x, `∀ y, (i x = i y) ⇒ (x = y))
≔ begin
assume x y Pegal;
refine lemmaI (i x) (i y) Pegal
end;

opaque symbol lemmaJ : π(`∀ a, `∀ b, (a = b) ⇒ (j' a = j' b))
≔ begin
assume a b Pegal;
refine Pegal (λ x, j' a = j' x) _;
assume P Pa;
refine Pa
end;

opaque symbol lemma10 : π(`∀ x, `∀ y, (j x = j y) ⇒ (x = y))
≔ begin
assume x y Pegal;
refine lemmaJ (j x) (j y) Pegal
end;

opaque symbol lemma11 : π(`∀ x, ¬(i x = o))
≔ begin
assume x Pegal;
refine Pegal I top_i
end;

opaque symbol lemma12 : π(`∀ x, ¬(j x = o))
≔ begin
assume x Pegal;
refine Pegal J top_i
end;

opaque symbol lemma13 : π(`∀ x, `∀ y, ¬(i x = j y))
≔ begin
assume x y Pegal;
refine Pegal I top_i
end;
