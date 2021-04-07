require open zf.theoriezf.logique;

constant symbol Nat : Set;
symbol zero : El Nat;
symbol s : El Nat → El Nat;
symbol eqN : El Nat → El Nat → El Nat;
rule eqN (s $x) (s $y) ↪ eqN $x $y;
rule eqN zero (s $y) ↪ zero;
rule eqN (s $x) zero ↪ zero;
rule eqN zero zero ↪ s zero;

symbol eqNP : El Nat → El Nat → Prop;
rule π(eqNP $x $y) ↪ Π (P : El Nat → Prop), π (P $x ⇒ P $y);
