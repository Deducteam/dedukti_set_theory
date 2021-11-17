require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.nat;
require open zf.theoriezf.formulas;

// Comprehension

symbol comp : Graph → (El nat → Graph) → El formula → Graph;
rule eta (comp $a $σ $f) $x $x' ↪ (`∃ y, `∃ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y')) ∨ (`∃ y, ($x = i y) ∧ ($x' = o) ∧ (eta $a y (root $a)) ∧ (interpretation (update $σ zero (cr $a y)) $f));
rule root (comp $a $σ $f) ↪ o;

// Infinity

symbol empty_set : Graph;
symbol Ind : Graph → Prop;

rule empty_set ↪ comp omega (λ _, empty_set) fF;
rule root empty_set ↪ o;
rule Ind $c ↪ (empty_set ∈ $c) ∧ (`∀ a, (a ∈ $c) ⇒ ((join (pair a (pair a a))) ∈ $c));
