require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.nat;
require open Logic.Z.formulas;

// Comprehension

symbol comp : El graph → (El nat → El graph) → El formula → El graph;
rule eta (comp $a $σ $f) $x $x' ↪ (`∃ y, `∃ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y')) ∨ (`∃ y, ($x = i y) ∧ ($x' = o) ∧ (eta $a y (root $a)) ∧ (interpretation (update $σ zero (cr $a y)) $f));
rule root (comp $a $σ $f) ↪ o;

// Infinity

symbol empty_set : El graph;
symbol Ind : El graph → El prop;

rule empty_set ↪ comp omega (λ _, empty_set) fF;
rule root empty_set ↪ o;
rule Ind $c ↪ (empty_set ∈ $c) ∧ (`∀ a, (a ∈ $c) ⇒ ((join (pair a (pair a a))) ∈ $c));
