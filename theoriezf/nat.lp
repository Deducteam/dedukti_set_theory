require open zf.theoriezf.logique;

// Nat

constant symbol nat : Set;
symbol zero : El nat;
symbol s : El nat → El nat;
/*
symbol eqN : El nat → El nat → El nat;
rule eqN (s $x) (s $y) ↪ eqN $x $y;
rule eqN zero (s $y) ↪ zero;
rule eqN (s $x) zero ↪ zero;
rule eqN zero zero ↪ s zero;
*/

symbol eqNP : El nat → El nat → Prop;
rule π(eqNP $x $y) ↪ Π (P : El nat → Prop), π (P $x ⇒ P $y);

symbol p : El nat → El nat;
rule eqNP (s $x) zero ↪ ⊥;
rule eqNP $x (s $y) ↪ eqNP (p $x) $y;
rule p (s $x) ↪ $x;
//rule eqNP (p (s $x)) $y ↪ eqNP $x $y;

symbol one ≔ s zero;
symbol two ≔ s one;
symbol three ≔ s two;

constant symbol recN : Π (P : El nat → Prop),
π(P zero) 
→ π(∀ nat (λ x, (P x) ⇒ (P (s x))))
→ π(∀ nat (λ x, (P x)));