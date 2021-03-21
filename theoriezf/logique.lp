// Logical operators

constant symbol Prop : TYPE;

injective symbol π : Prop → TYPE;

constant symbol ∧ : Prop → Prop → Prop;
notation ∧ infix left 5;
rule π ($A ∧ $B) ↪ Π P, (π $A → π $B → π P) → π P;

opaque symbol and_i A B : π A → π B → π (A ∧ B)
≔ begin
assume A B pA pB;
simpl;
assume P H;
apply H pA pB;
end;

opaque symbol and_eg A B : π (A ∧ B) → π A
≔ begin
assume A B;
simpl;
assume H;
apply H A;
assume pA pB;
apply pA;
end;

opaque symbol and_ed A B : π (A ∧ B) → π B
≔ begin
assume A B;
simpl;
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
simpl;
assume P pAP pBP;
apply pAP pA;
end;

opaque symbol or_id A B : π B → π (A ∨ B)
≔ begin
assume A B pA;
simpl;
assume P pAP pBP;
apply pBP pA;
end;

opaque symbol or_e A B C : π (A ∨ B) → (π A → π C) → (π B → π C) → π C
≔ begin
assume A B C;
simpl;
assume H pAC pBC;
apply H C pAC pBC;
end;

constant symbol ⇒ : Prop → Prop → Prop;
notation ⇒ infix right 6;
rule π ($A ⇒ $B) ↪ π $A → π $B;

opaque symbol imp_i A B : (π A → π B) → π (A ⇒ B)
≔ begin
assume A B pAB;
simpl;
assume pA;
apply pAB pA;
end;

opaque symbol imp_e A B : π (A ⇒ B) → π A → π B
≔ begin
assume A B;
simpl;
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

// Theory of graph;

constant symbol Graph : TYPE;

constant symbol Node : TYPE;

symbol Set : TYPE;

symbol El : Set → TYPE;

constant symbol ∀ : Π (x : Set), (El x → Prop) → Prop;
notation ∀ quantifier;
rule π (∀ $x $A) ↪ Π (y : El $x), π ($A y);

constant symbol ∃ : Π (x : Set), (El x → Prop) → Prop;
notation ∃ quantifier;
rule π (∃ $x $A) ↪ Π P, (Π (y : El $x), π ($A y) → π P) → π P;

symbol g : Set;
rule El g ↪ Graph;

symbol n : Set;
rule El n ↪ Node;

symbol relat : Set;
rule El relat ↪ Node → Node → Prop;

symbol class : Set;
rule El class ↪ Node → Prop;

opaque symbol AllElim : Π x : Set, Π P : El x → Prop, π(∀ x P) → Π y : El x, π(P y)
≔ begin
simpl;
assume x P H y;
apply H y;
end;

opaque symbol AllIntro : Π x : Set, Π P : El x → Prop, (Π y : El x, π(P y)) → π(∀ x P)
≔ begin
assume x P;
simpl;
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
simpl;
assume x P H P' H';
apply H P' H';
end;

symbol eta : Graph → Node → Node → Prop;

symbol root : Graph → Node;

symbol cr : Graph → Node → Graph;
//cr = change root;
rule eta (cr $a $z) $x $y ↪ eta $a $x $y;
rule root (cr $a $x) ↪ $x;
rule (cr (cr $a $x) $y) ↪ cr $a $y;

constant symbol = : Node → Node → Prop;
notation = infix 4;
rule π ($x = $y) ↪ Π (P : Node → Prop), π(P $x) → π(P $y);

constant symbol o : Node;
constant symbol O : Node;

symbol i : Node → Node;
symbol i' : Node → Node;
symbol j : Node → Node;
symbol j' : Node → Node;
symbol I : Node → Prop;
symbol J : Node → Prop;

// ρ^ car ρ' affiche un message d'erreur ;
symbol ρ : Graph → Node;
symbol ρ^ : Node → Graph;

symbol Succ : Node → Node;
symbol Pred : Node → Node;
symbol Null : Node → Prop;
symbol Nat : Node → Prop;

symbol < : Node → Node → Prop;
notation < infix 5;

rule i' (i $x) ↪ $x;
rule j' (j $x) ↪ $x;
rule ρ^ (ρ $x) ↪ $x;
rule I (i $x) ↪ ⊤;
rule J (j $x) ↪ ⊤;
rule I (j $x) ↪ ⊥;
rule J (i $x) ↪ ⊥;
rule I (o) ↪ ⊥;
rule J (o) ↪ ⊥;

rule Pred (Succ $x) ↪ $x ;
rule Null O ↪ ⊤;
rule Nat O ↪ ⊤;
rule Null (Succ $x) ↪ ⊥;
rule Nat (Succ $x) ↪ Nat $x;

rule $x < O ↪ ⊥;
rule $x < (Succ $y) ↪ ($x < $y) ∨ ($x = $y);

symbol simeq : Graph → Graph → Prop;
notation simeq infix 5;
rule $a simeq $b ↪ ∃ relat (λ r, ((r (root $a) (root $b)) ∧ (∀ n (λ x, (∀ n (λ x', (∀ n (λ y, (((eta $a x' x) ∧ (r x y)) ⇒ (∃ n (λ y', ((eta $b y' y) ∧ (r x' y'))))))))))) ∧ (∀ n (λ y, (∀ n (λ y', (∀ n (λ x, (((eta $b y' y) ∧ (r x y)) ⇒ (∃ n (λ x', ((eta $a x' x) ∧ (r x' y')))))))))))));

symbol ∈ : Graph → Graph → Prop;
notation ∈ infix 7;
rule $a ∈ $b ↪ ∃ n (λ x, ((eta $b x (root $b)) ∧ ($a simeq cr $b x)));

symbol join : Graph → Graph;
rule eta (join $a) $x $x' ↪ (∃ n (λ y, ∃ n (λ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y')))) ∨ (∃ n (λ y, ∃ n (λ z, (($x = i y) ∧ ($x' = o) ∧ eta $a y z ∧ eta $a z (root $a)))));
rule root (join $a) ↪ o;

symbol pair : Graph → Graph → Graph;
rule eta (pair $a $b) $x $x' ↪ (∃ n (λ y, ∃ n (λ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y')))) ∨ (∃ n (λ y, ∃ n (λ y', (($x = j y) ∧ ($x' = j y') ∧ eta $b y y')))) ∨ (($x = i (root $a)) ∧ ($x' = o)) ∨ (($x = j (root $b)) ∧ ($x' = o));
rule root (pair $a $b) ↪ o;

symbol powerset : Graph → Graph;
rule eta (powerset $a) $x $x' ↪ (∃ n (λ y, ∃ n (λ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y')))) ∨ (∃ n (λ y, ∃ g (λ c, (($x = i y) ∧ ($x' = j (ρ c)) ∧ (eta $a y (root $a)) ∧ ((cr $a y) ∈ c))))) ∨ (∃ g (λ c, (($x = j (ρ c)) ∧ ($x' = o))));
rule root (powerset $a) ↪ o;

symbol comp : Graph → (Graph → Prop) → Graph;
rule eta (comp $a $P) $x $x' ↪ (∃ n (λ y, ∃ n (λ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y')))) ∨ (∃ n (λ y, ($x = i y) ∧ ($x' = o) ∧ (eta $a y (root $a)) ∧ ($P (cr $a y))));
rule root (comp $a $P) ↪ o;

symbol omega : Graph;
rule eta omega $x $x' ↪ (∃ n (λ y, ∃ n (λ y', (($x = i y) ∧ ($x' = i y') ∧ (y < y'))))) ∨ (∃ n (λ y, (($x = i y) ∧ ($x' = o) ∧ Nat y)));
rule root omega ↪ o;

symbol Cl : Graph → Graph;
rule eta (Cl $a) $x $x' ↪ (∃ n (λ y, ∃ n (λ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y')))) ∨ (∃ n (λ y, (($x = i y) ∧ ($x' = o) ∧ (∀ class (λ c, (∀ n (λ z, (eta $a z (root $a)) ⇒ (c z))) ∧ (∀ n (λ z, ∀ n (λ z', (((eta $a z z') ∧ (c z') ⇒ (c z)) ⇒ c y)))))))));
rule root (Cl $a) ↪ o;