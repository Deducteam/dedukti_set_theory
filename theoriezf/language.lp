require open zf.theoriezf.logic;

constant symbol Graph : TYPE;

constant symbol Node : TYPE;

symbol g : Set;
rule El g ↪ Graph;

symbol n : Set;
rule El n ↪ Node;

symbol eta : Graph → Node → Node → Prop;
symbol root : Graph → Node;

symbol cr : Graph → Node → Graph;
//cr = change root;
rule eta (cr $a $z) $x $y ↪ eta $a $x $y;
rule root (cr $a $x) ↪ $x;
rule (cr (cr $a $x) $y) ↪ cr $a $y;

constant symbol o : Node;
constant symbol O : Node;

symbol i : Node → Node;
symbol i' : Node → Node;
symbol j : Node → Node;
symbol j' : Node → Node;
symbol I : Node → Prop;
symbol J : Node → Prop;

// ρ^ car ρ' affiche un message d'erreur ;
symbol ρ : Graph → Node;
symbol ρ^ : Node → Graph;

symbol Succ : Node → Node;
symbol Pred : Node → Node;
symbol Null : Node → Prop;
symbol Nat : Node → Prop;

symbol < : Node → Node → Prop;
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

symbol simeq : Graph → Graph → Prop;
notation simeq infix 5;
rule $a simeq $b ↪ `∃ r : El (n arrow (n arrow omicron)), (r (root $a) (root $b)) ∧ (`∀ x, `∀ x', `∀ y, (((eta $a x' x) ∧ (r x y)) ⇒ (`∃ y', ((eta $b y' y) ∧ (r x' y'))))) ∧ (`∀ y, `∀ y', `∀ x, (((eta $b y' y) ∧ (r x y)) ⇒ (`∃ x', ((eta $a x' x) ∧ (r x' y')))));

symbol ∈ : Graph → Graph → Prop;
notation ∈ infix 7;
rule $a ∈ $b ↪ `∃ x, ((eta $b x (root $b)) ∧ ($a simeq cr $b x));

symbol join : Graph → Graph;
rule eta (join $a) $x $x' ↪ (`∃ y, `∃ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y')) ∨ (`∃ y, `∃ z, (($x = i y) ∧ ($x' = o) ∧ eta $a y z ∧ eta $a z (root $a)));
rule root (join $a) ↪ o;

symbol pair : Graph → Graph → Graph;
rule eta (pair $a $b) $x $x' ↪ (`∃ y, `∃ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y')) ∨ (`∃ y, `∃ y', (($x = j y) ∧ ($x' = j y') ∧ eta $b y y')) ∨ (($x = i (root $a)) ∧ ($x' = o)) ∨ (($x = j (root $b)) ∧ ($x' = o));
rule root (pair $a $b) ↪ o;

symbol powerset : Graph → Graph;
rule eta (powerset $a) $x $x' ↪ (`∃ y, `∃ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y')) ∨ (`∃ y, `∃ c, (($x = i y) ∧ ($x' = j (ρ c)) ∧ (eta $a y (root $a)) ∧ ((cr $a y) ∈ c))) ∨ (`∃ c, (($x = j (ρ c)) ∧ ($x' = o)));
rule root (powerset $a) ↪ o;

symbol omega : Graph;
rule eta omega $x $x' ↪ (`∃ y, `∃ y', (($x = i y) ∧ ($x' = i y') ∧ (y < y'))) ∨ (`∃ y, (($x = i y) ∧ ($x' = o) ∧ Nat y));
rule root omega ↪ o;

symbol Cl : Graph → Graph;
rule eta (Cl $a) $x $x' ↪ (`∃ y, `∃ y', (($x = i y) ∧ ($x' = i y') ∧ eta $a y y')) ∨ (`∃ y, (($x = i y) ∧ ($x' = o) ∧ (`∀ c : El (n arrow omicron), ((`∀ z, (eta $a z (root $a)) ⇒ (c z)) ∧ (`∀ z, `∀ z', (((eta $a z z') ∧ (c z')) ⇒ (c z)))) ⇒ c y)));
rule root (Cl $a) ↪ o;