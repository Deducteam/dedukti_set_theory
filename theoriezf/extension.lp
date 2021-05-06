require open zf.theoriezf.logique;

// Nat

constant symbol nat : Set;
symbol zero : El nat;
symbol s : El nat → El nat;
symbol eqN : El nat → El nat → El nat;
rule eqN (s $x) (s $y) ↪ eqN $x $y;
rule eqN zero (s $y) ↪ zero;
rule eqN (s $x) zero ↪ zero;
rule eqN zero zero ↪ s zero;

symbol eqNP : El nat → El nat → Prop;
rule π(eqNP $x $y) ↪ Π (P : El nat → Prop), π (P $x ⇒ P $y);

symbol one ≔ s zero;
symbol two ≔ s one;
symbol three ≔ s two;

// Formula

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

symbol if : El nat → Graph → Graph → Graph;
rule if zero $g1 $g2 ↪ $g2;
rule if (s zero) $g1 $g2 ↪ $g1;

symbol update : (El nat → Graph) → El nat → Graph → (El nat → Graph);
rule update $σ $x $a $y ↪ if (eqN $x $y) $a ($σ $y);

symbol valuation : Set;
rule El valuation ↪ El nat → El g;

constant symbol recF : Π (P : El formula → Prop), 
π(∀ nat (λ x, ∀ nat (λ y, P (eqF x y))))
→ π(∀ nat (λ x, ∀ nat (λ y, P (inF x y))))
→ π(∀ formula (λ f, ∀ formula (λ g, (P f ∧ P g) ⇒ (P (andF f g)))))
→ π(∀ formula (λ f, ∀ formula (λ g, (P f ∧ P g) ⇒ (P (orF f g)))))
→ π(∀ formula (λ f, ∀ formula (λ g, (P f ∧ P g) ⇒ (P (impF f g)))))
→ π(∀ formula (λ f, (P f) ⇒ (∀ nat (λ x, P (allF x f)))))
→ π(∀ formula (λ f, (P f) ⇒ (∀ nat (λ x, P (exF x f)))))
→ π(P tF)
→ π(P fF)
→ π(∀ formula (λ f, P f));

symbol interpretation : (El nat → Graph) → El formula → Prop;
rule interpretation $σ (eqF $x $y) ↪ ($σ $x) simeq ($σ $y);
rule interpretation $σ (inF $x $y) ↪ ($σ $x) ∈ ($σ $y);
rule interpretation $σ (andF $f $g) ↪ (interpretation $σ $f) ∧ (interpretation $σ $g);
rule interpretation $σ (orF $f $g) ↪ (interpretation $σ $f) ∨ (interpretation $σ $g);
rule interpretation $σ (impF $f $g) ↪ (interpretation $σ $f) ⇒ (interpretation $σ $g);
rule interpretation $σ (allF $x $f) ↪ ∀ g (λ a, interpretation (update $σ $x a) $f);
rule interpretation $σ (exF $x $f) ↪ ∃ g (λ a, interpretation (update $σ $x a) $f);
rule interpretation $σ fF ↪ ⊥;
rule interpretation $σ tF ↪ ⊤;

// Comprehension

symbol comp : Graph → El valuation → El formula → Graph;
rule eta (comp $a $σ $f) $x $x' ↪ (∃ n (λ y, ∃ n (λ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y')))) ∨ (∃ n (λ y, ($x = i y) ∧ ($x' = o) ∧ (eta $a y (root $a)) ∧ (interpretation (update $σ zero (cr $a y)) $f)));
rule root (comp $a $σ $f) ↪ o;