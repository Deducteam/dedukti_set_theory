require open zf.theoriezf.logique;

// Nat

constant symbol nat : Set;
symbol zero : El nat;
symbol s : El nat → El nat;

symbol one ≔ s zero;
symbol two ≔ s one;
symbol three ≔ s two;

symbol eqNP : El nat → El nat → Prop;
rule π(eqNP $x $y) ↪ Π (P : El nat → Prop), π (P $x ⇒ P $y);

constant symbol Peano3 : Π (x y: El nat), π((eqNP (s x) (s y)) ⇒ (eqNP x y));
constant symbol Peano4 : Π (x : El nat), π(¬(eqNP (s x) zero));

constant symbol recN : Π (P : El nat → Prop),
π(P zero) 
→ π(∀ nat (λ x, (P x) ⇒ (P (s x))))
→ π(∀ nat (λ x, (P x)));

opaque symbol lemmeNP : Π (x : El nat), π(eqNP x x) 
≔ begin
assume x P Px;
apply Px;
end;

opaque symbol lemmeSymNP : Π (x y : El nat), π((eqNP x y) ⇒ (eqNP y x)) 
≔ begin
assume x y;
simpl;
assume Pxy P;
apply Pxy (λ z, (P z) ⇒ (P x));
assume Px;
apply Px;
end;

opaque symbol lemmeTransNP : Π (x y z: El nat), π(((eqNP x y) ∧ (eqNP y z)) ⇒ (eqNP x z))
≔ begin
assume x y z Pxyz P Px;
apply (and_ed _ _ Pxyz) P ((and_eg _ _ Pxyz) P Px);
end;

opaque symbol eqNPor : Π (x y : El nat), π((eqNP x y) ∨ (¬(eqNP x y)))
≔ begin
apply recN _;
apply recN _;
//Cas x = 0, y = 0
apply or_ig;
simpl;
assume P Pz;
apply Pz;
//Cas x = 0, s y
assume x Px;
apply or_id;
assume H0;
apply Peano4 x _;
apply lemmeSymNP zero (s x) H0;
assume x Hx;
apply recN _;
//Cas s x, y = 0
apply or_id;
apply Peano4 x;
//Cas s x, s y
assume y Hrec;
apply or_e _ _ _ (Hx y);
assume Hxy;
apply or_ig;
apply Hxy (λ z, eqNP (s x) (s z)) _;
apply lemmeNP (s x);
assume Hxy;
apply or_id;
assume Hsxsy;
apply Hxy _;
apply Peano3 x y Hsxsy;
end;