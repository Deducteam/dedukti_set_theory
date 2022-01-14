require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.nat;

constant symbol formula : Set;
constant symbol eqF : El nat → El nat → El formula;
constant symbol inF : El nat → El nat → El formula;
constant symbol andF : El formula → El formula → El formula;
constant symbol orF : El formula → El formula → El formula;
constant symbol allF : El nat → El formula → El formula;
constant symbol exF : El nat → El formula → El formula;
constant symbol impF : El formula → El formula → El formula;
constant symbol fF : El formula;
constant symbol tF : El formula;

symbol update : (El nat → El graph) → El nat → El graph → (El nat → El graph);
symbol update1 : (El nat → El graph) → El nat → El graph → El nat → (El nat → El graph);
rule update $σ $x $a $y ↪ update1 $σ $x $a $y $y;
rule update1 $σ zero $a zero $z ↪ $a;
rule update1 $σ zero $a (s $y) $z ↪ $σ $z;
rule update1 $σ (s $x) $a zero $z ↪ $σ $z;
rule update1 $σ (s $x) $a (s $y) $z ↪ update1 $σ $x $a $y $z;

constant symbol recF : Π (P : El formula → El prop), 
π(`∀ x, `∀ y, P (eqF x y))
→ π(`∀ x, `∀  y, P (inF x y))
→ π(`∀ f, `∀ g, (P f ∧ P g) ⇒ (P (andF f g)))
→ π(`∀ f, `∀ g, (P f ∧ P g) ⇒ (P (orF f g)))
→ π(`∀ f, `∀ g, (P f ∧ P g) ⇒ (P (impF f g)))
→ π(`∀ f, (P f) ⇒ (`∀ x, P (allF x f)))
→ π(`∀ f, (P f) ⇒ (`∀ x, P (exF x f)))
→ π(P tF)
→ π(P fF)
→ π(`∀ f, P f);

symbol interpretation : (El nat → El graph) → El formula → El prop;
rule interpretation $σ (eqF $x $y) ↪ ($σ $x) simeq ($σ $y);
rule interpretation $σ (inF $x $y) ↪ ($σ $x) ∈ ($σ $y);
rule interpretation $σ (andF $f $g) ↪ (interpretation $σ $f) ∧ (interpretation $σ $g);
rule interpretation $σ (orF $f $g) ↪ (interpretation $σ $f) ∨ (interpretation $σ $g);
rule interpretation $σ (impF $f $g) ↪ (interpretation $σ $f) ⇒ (interpretation $σ $g);
rule interpretation $σ (allF $x $f) ↪ `∀ a, interpretation (update $σ $x a) $f;
rule interpretation $σ (exF $x $f) ↪ `∃ a, interpretation (update $σ $x a) $f;
rule interpretation $σ fF ↪ ⊥;
rule interpretation $σ tF ↪ ⊤;