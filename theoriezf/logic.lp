constant symbol Prop : TYPE;

injective symbol π : Prop → TYPE;

constant symbol ∧ : Prop → Prop → Prop;
notation ∧ infix left 5;
rule π ($A ∧ $B) ↪ Π P, (π $A → π $B → π P) → π P;

opaque symbol and_i A B : π A → π B → π (A ∧ B)
≔ begin
assume A B pA pB;
simplify;
assume P H;
apply H pA pB;
end;

opaque symbol and_eg A B : π (A ∧ B) → π A
≔ begin
assume A B;
simplify;
assume H;
apply H A;
assume pA pB;
apply pA;
end;

opaque symbol and_ed A B : π (A ∧ B) → π B
≔ begin
assume A B;
simplify;
assume H;
apply H B;
assume pA pB;
apply pB;
end;

constant symbol ∨ : Prop → Prop → Prop;
notation ∨ infix left 7;
rule π ($A ∨ $B) ↪ Π P, (π $A → π P) → (π $B → π P) → π P;

opaque symbol or_ig A B : π A → π (A ∨ B)
≔ begin
assume A B pA;
simplify;
assume P pAP pBP;
apply pAP pA;
end;

opaque symbol or_id A B : π B → π (A ∨ B)
≔ begin
assume A B pA;
simplify;
assume P pAP pBP;
apply pBP pA;
end;

opaque symbol or_e A B C : π (A ∨ B) → (π A → π C) → (π B → π C) → π C
≔ begin
assume A B C;
simplify;
assume H pAC pBC;
apply H C pAC pBC;
end;

constant symbol ⇒ : Prop → Prop → Prop;
notation ⇒ infix right 6;
rule π ($A ⇒ $B) ↪ π $A → π $B;

opaque symbol imp_i A B : (π A → π B) → π (A ⇒ B)
≔ begin
assume A B pAB;
simplify;
assume pA;
apply pAB pA;
end;

opaque symbol imp_e A B : π (A ⇒ B) → π A → π B
≔ begin
assume A B;
simplify;
assume pAB;
assume pA;
apply pAB pA;
end;

symbol ⇔ : Prop → Prop → Prop;
notation ⇔ infix right 6;
rule ($A ⇔ $B) ↪ ($A ⇒ $B) ∧ ($B ⇒ $A);

constant symbol ⊥ : Prop;
rule π ⊥ ↪ Π (P : Prop), π P;

opaque symbol f_e A : π ⊥ → π A
≔ begin
assume A P;
apply P A;
end;

constant symbol ¬ : Prop → Prop;
rule π (¬ $A) ↪ π $A → π ⊥;

constant symbol ⊤ : Prop;
rule π ⊤ ↪ Π (P : Prop), π P → π P;

opaque symbol Vrai : π ⊤ ≔
begin
assume P pP;
apply pP;
end;

symbol Set : TYPE;

injective symbol El : Set → TYPE;
/*
constant symbol ∀ {X} : (El X → Prop) → Prop; 
notation ∀ quantifier;
rule π (@∀ $x $A) ↪ Π (y : El $x), π ($A y);

constant symbol ∃ {X} : (El X → Prop) → Prop;
notation ∃ quantifier;
rule π (@∃ $x $A) ↪ Π P, (Π (y : El $x), π ($A y) → π P) → π P;

opaque symbol AllElim : Π (x : Set), Π (P : El x → Prop), π(`∀ y, P y) → Π (y : El x), π(P y)
≔ begin
simplify;
assume x P H y;
apply H y;
end;

opaque symbol AllIntro : Π (x : Set), Π (P : El x → Prop), (Π y : El x, π(P y)) → π(`∀ x, P x)
≔ begin
assume x P;
simplify;
assume H y;
apply H y;
end;

opaque symbol ExIntro : Π (x : Set), Π (a : El x), Π (P : El x → Prop), π(P a ⇒ `∃ y, P y)
≔ begin
assume x a P Pa P0 Py0;
apply Py0 a Pa;
end;

opaque symbol ExElim : Π (x : Set), Π (P : El x → Prop), π(`∃ y, P y) → Π Q : Prop, π((`∀ y : El x, P y ⇒ Q)) → π(Q)
≔ begin
simplify;
assume x P H P' H';
apply H P' H';
end;*/

constant symbol ∀ : Π (x : Set), (El x → Prop) → Prop;
notation ∀ quantifier;
rule π (∀ $x $A) ↪ Π (y : El $x), π ($A y);

constant symbol ∃ : Π (x : Set), (El x → Prop) → Prop;
notation ∃ quantifier;
rule π (∃ $x $A) ↪ Π P, (Π (y : El $x), π ($A y) → π P) → π P;

opaque symbol AllElim : Π x : Set, Π P : El x → Prop, π(∀ x P) → Π y : El x, π(P y)
≔ begin
simplify;
assume x P H y;
apply H y;
end;

opaque symbol AllIntro : Π x : Set, Π P : El x → Prop, (Π y : El x, π(P y)) → π(∀ x P)
≔ begin
assume x P;
simplify;
assume H y;
apply H y;
end;

opaque symbol ExIntro : Π x : Set, Π a : El x, Π P : El x → Prop, π(P a ⇒ ∃ x (λ y, P y))
≔ begin
assume x a P Pa P0 Py0;
apply Py0 a Pa;
end;

opaque symbol ExElim : Π x : Set, Π P : El x → Prop, π(∃ x P) → Π Q : Prop, π((∀ x (λ y : El x, P y ⇒ Q))) → π(Q)
≔ begin
simplify;
assume x P H P' H';
apply H P' H';
end;

constant symbol = {s} : El s → El s → Prop;
notation = infix 4;
rule π (@= $s $x $y) ↪ Π (P : El $s → Prop), π(P $x) → π(P $y);

opaque symbol refl : Π (s : Set), π(∀ s (λ x, x = x)) ≔
begin
assume s y P Py;
refine Py;
end;