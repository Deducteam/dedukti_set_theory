require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.nat;

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

symbol update : (El nat → Graph) → El nat → Graph → (El nat → Graph);
symbol update1 : (El nat → Graph) → El nat → Graph → El nat → (El nat → Graph);
rule update $σ $x $a $y ↪ update1 $σ $x $a $y $y;
rule update1 $σ zero $a zero $z ↪ $a;
rule update1 $σ zero $a (s $y) $z ↪ $σ $z;
rule update1 $σ (s $x) $a zero $z ↪ $σ $z;
rule update1 $σ (s $x) $a (s $y) $z ↪ update1 $σ $x $a $y $z;

constant symbol recF : Π (P : El formula → Prop), 
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

symbol interpretation : (El nat → Graph) → El formula → Prop;
rule interpretation $σ (eqF $x $y) ↪ ($σ $x) simeq ($σ $y);
rule interpretation $σ (inF $x $y) ↪ ($σ $x) ∈ ($σ $y);
rule interpretation $σ (andF $f $g) ↪ (interpretation $σ $f) ∧ (interpretation $σ $g);
rule interpretation $σ (orF $f $g) ↪ (interpretation $σ $f) ∨ (interpretation $σ $g);
rule interpretation $σ (impF $f $g) ↪ (interpretation $σ $f) ⇒ (interpretation $σ $g);
rule interpretation $σ (allF $x $f) ↪ `∀ a, interpretation (update $σ $x a) $f;
rule interpretation $σ (exF $x $f) ↪ `∃ a, interpretation (update $σ $x a) $f;
rule interpretation $σ fF ↪ ⊥;
rule interpretation $σ tF ↪ ⊤;