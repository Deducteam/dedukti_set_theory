constant symbol Prop : TYPE;
injective symbol π : Prop → TYPE;

constant symbol ∧ : Prop → Prop → Prop;
notation ∧ infix left 5;
rule π ($A ∧ $B) ↪ Π P, (π $A → π $B → π P) → π P;

constant symbol and_i A B : π A → π B → π (A ∧ B);
constant symbol and_eg A B : π (A ∧ B) → π A;
constant symbol and_ed A B : π (A ∧ B) → π B;

constant symbol ⇒ : Prop → Prop → Prop;
notation ⇒ infix right 6;
rule π ($A ⇒ $B) ↪ π $A → π $B;

constant symbol imp_e A B : π (A ⇒ B) → π A → π B;

symbol P : Prop;
symbol R : Prop;

opaque symbol test : π(((P ⇒ R) ∧ (R ⇒ P)) ⇒ ((R ⇒ P) ∧ (P ⇒ R)))
≔ begin
assume H;
apply and_i;
assume Hr;
//apply (and_ed _ _ H) Hr; //Ancienne écriture
//apply imp_e _ _ (and_ed _ _ H) Hr; 
//apply (and_ed (P ∧ (P ⇒ R)) (R ⇒ P) H) Hr; 
end;
