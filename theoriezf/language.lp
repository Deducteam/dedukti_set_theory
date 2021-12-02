require open zf.theoriezf.logic;

constant symbol graph : Set;
constant symbol node : Set;

symbol eta : El graph → El node → El node → El prop;
symbol root : El graph → El node;

symbol cr : El graph → El node → El graph;
//cr = change root;
rule eta (cr $a $z) $x $y ↪ eta $a $x $y;
rule root (cr $a $x) ↪ $x;
rule (cr (cr $a $x) $y) ↪ cr $a $y;

constant symbol o : El node;
constant symbol O : El node;

symbol i : El node → El node;
symbol i' : El node → El node;
symbol j : El node → El node;
symbol j' : El node → El node;
symbol I : El node → El prop;
symbol J : El node → El prop;

// ρ^ car ρ' affiche un message d'erreur ;
symbol ρ : El graph → El node;
symbol ρ^ : El node → El graph;

symbol Succ : El node → El node;
symbol Pred : El node → El node;
symbol Null : El node → El prop;
symbol Nat : El node → El prop;

symbol < : El node → El node → El prop;
notation < infix 5;

rule i' (i $x) ↪ $x;
rule j' (j $x) ↪ $x;
rule ρ^ (ρ $x) ↪ $x;
rule I (i $x) ↪ ⊤;
rule J (j $x) ↪ ⊤;
rule I (j $x) ↪ ⊥;
rule J (i $x) ↪ ⊥;
rule I (o) ↪ ⊥;
rule J (o) ↪ ⊥;

rule Pred (Succ $x) ↪ $x ;
rule Null O ↪ ⊤;
rule Nat O ↪ ⊤;
rule Null (Succ $x) ↪ ⊥;
rule Nat (Succ $x) ↪ Nat $x;

rule $x < O ↪ ⊥;
rule $x < (Succ $y) ↪ ($x < $y) ∨ ($x = $y);

symbol simeq : El graph → El graph → El prop;
notation simeq infix 4;
rule $a simeq $b ↪ `∃ r : El (node arrow (node arrow prop)), 
    r (root $a) (root $b)
    ∧ (`∀ x, `∀ x', `∀ y, 
        eta $a x' x ∧ r x y
            ⇒ `∃ y', eta $b y' y ∧ r x' y')
    ∧ (`∀ y, `∀ y', `∀ x, 
        eta $b y' y ∧ r x y
            ⇒ `∃ x', eta $a x' x ∧ r x' y');

symbol ∈ : El graph → El graph → El prop;
notation ∈ infix 4;
rule $a ∈ $b ↪ `∃ x, eta $b x (root $b) ∧ ($a simeq cr $b x);

symbol join : El graph → El graph;
rule eta (join $a) $x $x' ↪ (`∃ y, `∃ y', ($x = i y) ∧ ($x' = i y') ∧ eta $a y y')
    ∨ (`∃ y, `∃ z, ($x = i y) ∧ ($x' = o) ∧ eta $a y z ∧ eta $a z (root $a));
rule root (join $a) ↪ o;

symbol pair : El graph → El graph → El graph;
rule eta (pair $a $b) $x $x' ↪ (`∃ y, `∃ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y'))
    ∨ (`∃ y, `∃ y', ($x = j y) ∧ ($x' = j y') ∧ eta $b y y')
    ∨ (($x = i (root $a)) ∧ ($x' = o))
    ∨ (($x = j (root $b)) ∧ ($x' = o));
rule root (pair $a $b) ↪ o;

symbol powerset : El graph → El graph;
rule eta (powerset $a) $x $x' ↪ (`∃ y, `∃ y', ($x = i y) ∧ ($x' = i y') ∧ eta $a y y')
    ∨ (`∃ y, `∃ c, ($x = i y) ∧ ($x' = j (ρ c)) ∧ (eta $a y (root $a)) ∧ ((cr $a y) ∈ c))
    ∨ (`∃ c, ($x = j (ρ c)) ∧ ($x' = o));
rule root (powerset $a) ↪ o;

symbol omega : El graph;
rule eta omega $x $x' ↪ (`∃ y, `∃ y', ($x = i y) ∧ ($x' = i y') ∧ (y < y'))
    ∨ (`∃ y, ($x = i y) ∧ ($x' = o) ∧ Nat y);
rule root omega ↪ o;

symbol Cl : El graph → El graph;
rule eta (Cl $a) $x $x' ↪ (`∃ y, `∃ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y'))
    ∨ (`∃ y, ($x = i y) 
        ∧ ($x' = o)
        ∧ (`∀ c : El (node arrow prop), 
                ((`∀ z, eta $a z (root $a) ⇒ c z)
                ∧ (`∀ z, `∀ z', (eta $a z z') ∧ (c z') ⇒ (c z)))
            ⇒ c y));
rule root (Cl $a) ↪ o;