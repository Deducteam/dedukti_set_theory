constant symbol Prop : TYPE;
injective symbol π : Prop → TYPE;
symbol ∧ : Prop → Prop → Prop;
notation ∧ infix left 5;
rule π ($A ∧ $B) ↪ Π P, (π $A → π $B → π P) → π P;

symbol P : Prop;
symbol Q : Prop;
symbol R : Prop;
symbol S : Prop;
rule (P ∧ Q) ↪ R;
rule R ↪ S;

opaque symbol test : π(P ∧ Q)
≔ begin
//simpl;
//simpl ∧;
end;



