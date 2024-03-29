symbol Set : TYPE;

injective symbol El : Set → TYPE;

constant symbol prop : Set;

injective symbol π : El prop → TYPE;

constant symbol ∧ : El prop → El prop → El prop;
notation ∧ infix left 8;
rule π ($A ∧ $B) ↪ Π P, (π $A → π $B → π P) → π P;

opaque symbol and_i A B : π A → π B → π (A ∧ B)
≔ begin
assume A B pA pB;
simplify;
assume P H;
apply H pA pB
end;

opaque symbol and_el A B : π (A ∧ B) → π A
≔ begin
assume A B;
simplify;
assume H;
apply H A;
assume pA pB;
apply pA
end;

opaque symbol and_er A B : π (A ∧ B) → π B
≔ begin
assume A B;
simplify;
assume H;
apply H B;
assume pA pB;
apply pB
end;

constant symbol ∨ : El prop → El prop → El prop;
notation ∨ infix left 7;
rule π ($A ∨ $B) ↪ Π P, (π $A → π P) → (π $B → π P) → π P;

opaque symbol or_il A B : π A → π (A ∨ B)
≔ begin
assume A B pA;
simplify;
assume P pAP pBP;
apply pAP pA
end;

opaque symbol or_ir A B : π B → π (A ∨ B)
≔ begin
assume A B pA;
simplify;
assume P pAP pBP;
apply pBP pA
end;

opaque symbol or_e A B C : π (A ∨ B) → (π A → π C) → (π B → π C) → π C
≔ begin
assume A B C;
simplify;
assume H pAC pBC;
apply H C pAC pBC
end;

constant symbol ⇒ : El prop → El prop → El prop;
notation ⇒ infix right 6;
rule π ($A ⇒ $B) ↪ π $A → π $B;

opaque symbol imp_i A B : (π A → π B) → π (A ⇒ B)
≔ begin
assume A B pAB;
simplify;
assume pA;
apply pAB pA
end;

opaque symbol imp_e A B : π (A ⇒ B) → π A → π B
≔ begin
assume A B;
simplify;
assume pAB;
assume pA;
apply pAB pA
end;

symbol ⇔ : El prop → El prop → El prop;
notation ⇔ infix right 5;
rule ($A ⇔ $B) ↪ ($A ⇒ $B) ∧ ($B ⇒ $A);

constant symbol ⊥ : El prop;
rule π ⊥ ↪ Π (P : El prop), π P;

opaque symbol bottom_e A : π ⊥ → π A
≔ begin
assume A P;
apply P A
end;

constant symbol ¬ : El prop → El prop;
rule π (¬ $A) ↪ π $A → π ⊥;

constant symbol ⊤ : El prop;
rule π ⊤ ↪ Π (P : El prop), π P → π P;

opaque symbol top_i : π ⊤ ≔
begin
assume P pP;
apply pP
end;

constant symbol ∀ [s] : (El s → El prop) → El prop; 
notation ∀ quantifier;
rule π (@∀ $x $A) ↪ Π (y : El $x), π ($A y);

constant symbol ∃ [s] : (El s → El prop) → El prop;
notation ∃ quantifier;
rule π (@∃ $x $A) ↪ Π P, (Π (y : El $x), π ($A y) → π P) → π P;

opaque symbol all_e : Π (x : Set), Π (P : El x → El prop), π(`∀ y, P y) → Π (y : El x), π(P y)
≔ begin
simplify;
assume x P H y;
apply H y
end;

opaque symbol ex_e : Π (x : Set), Π (P : El x → El prop), π(`∃ y, P y) → Π Q : El prop, π((`∀ y : El x, P y ⇒ Q)) → π(Q)
≔ begin
simplify;
assume x P H P' H';
apply H P' H'
end;

opaque symbol all_i : Π (x : Set), Π (P : El x → El prop), (Π y : El x, π(P y)) → π(`∀ x, P x)
≔ begin
assume x P;
simplify;
assume H y;
apply H y
end;

opaque symbol ex_i : Π (x : Set), Π (a : El x), Π (P : El x → El prop), π(P a ⇒ `∃ y, P y)
≔ begin
assume x a P Pa P0 Py0;
apply Py0 a Pa
end;

constant symbol = [s] : El s → El s → El prop;
notation = infix 4;
rule π (@= $s $x $y) ↪ Π (P : El $s → El prop), π(P $x) → π(P $y);

opaque symbol refl : Π (s : Set), π(`∀ x : El s, x = x) ≔
begin
assume s y P Py;
refine Py
end;

opaque symbol sym : Π (s : Set), π(`∀ x : El s, `∀ y : El s, (x = y) ⇒ (y = x)) 
≔ begin
assume s x y;
simplify;
assume Pxy P;
refine Pxy (λ z, (P z) ⇒ (P x)) _;
assume Px;
refine refl s x P Px
end;

opaque symbol trans : Π (s : Set), π(`∀ x : El s, `∀ y : El s, `∀ z : El s, ((x = y) ∧ (y = z)) ⇒ (x = z))
≔ begin
assume s x y z Pxyz P Px;
refine (and_er _ _ Pxyz) P ((and_el _ _ Pxyz) P Px)
end;

symbol arrow : Set → Set → Set;
notation arrow infix 4;
rule El($x arrow $y) ↪ El $x → El $y;
