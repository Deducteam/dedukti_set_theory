require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.bisimilarity;
require open Logic.Z.injectivity;
require open Logic.Z.eta1;
require open Logic.Z.eta2;
require open Logic.Z.eta3;
require open Logic.Z.membership;
require open Logic.Z.embedding;
require open Logic.Z.finitary;
require open Logic.Z.formulas;
require open Logic.Z.nat;
require open Logic.Z.language2;
require open Logic.Z.formulas_lemmas;
require open Logic.Z.weak_extensionality;

opaque symbol lemma46 : π(`∀ a, ¬ (a ∈ empty_set))
≔ begin
assume a;
simplify π;
assume H;
refine ex_e node _ H _ _;
assume x Hx;
refine ex_e node _ ((and_el _ _ (lemma23 (λ _, empty_set) fF omega x)) (and_el _ _ Hx)) _ _;
assume y Hy;
refine and_er _ _ Hy
end;

opaque symbol lemma47 : π(empty_set simeq (cr omega (i O)))
≔ begin
refine lemmaExt empty_set (cr omega (i O)) _;
assume x;
refine and_i _ _ _ _
{assume H;
refine ex_e node _ H _ _;
assume y Hy;
refine ex_e node _ ((and_el _ _ (lemma23 (λ _, empty_set) fF omega y)) (and_el _ _ Hy)) _ _;
assume z Hz;
refine bottom_e (x ∈ cr omega (i O)) (and_er _ _ Hz)}
{assume H;
refine ex_e node _ H _ _;
assume y Hy;
refine ex_e node _ ((and_el _ _ (lemma24 y O)) (and_el _ _ Hy)) _ _;
assume z Hz;
refine bottom_e (x ∈ empty_set) (and_er _ _ Hz)}
end;

opaque symbol lemmaJoinPair : π(`∀ a, `∀ c, (c ∈ (join (pair a (pair a a)))) ⇔ ((c ∈ a) ∨ (c simeq a)))
≔ begin
assume a c;
refine and_i _ _ _ _
{assume H1;
refine ex_e graph _ (and_el _ _ (lemma42 (pair a (pair a a)) c) H1) _ _;
assume x Hx;
refine or_e _ _ _ ((and_el _ _ (lemma43 a (pair a a) x)) (and_er _ _ Hx)) _ _
{assume Hxa;
refine or_il _ _ _;
refine lemma31 c x a (and_i _ _ (and_el _ _ Hx) Hxa)}
{assume Hxaa;
refine or_ir _ _ _;
refine or_e _ _ _ (and_el _ _ (lemma43 a a c) (lemma31 c x (pair a a) (and_i _ _ (and_el _ _ Hx) Hxaa))) _ _
{assume Hca;
refine Hca}
{assume Hca;
refine Hca}}}
{assume H2;
refine and_er _ _ (lemma42 (pair a (pair a a)) c) _;
refine or_e _ _ _ H2 _ _
{assume Hca;
refine ex_i graph a _ _;
refine and_i _ _ Hca _;
refine (and_er _ _ (lemma43 a (pair a a) a)) _;
refine or_il _ _ _;
refine lemma3 a}
{assume Hca;
refine ex_i graph (pair a a) _ _;
refine and_i _ _ _ _
{refine (and_er _ _ (lemma43 a a c)) _;
refine or_il _ _ _;
refine Hca}
{refine (and_er _ _ (lemma43 a (pair a a) (pair a a))) _;
refine or_ir _ _ _;
refine lemma3 (pair a a)}}}
end;

opaque symbol lemma48 : π(`∀ a, `∀ y, (a simeq (cr omega (i y))) ⇒ ((join (pair a (pair a a))) simeq (cr omega (i (Succ y)))))
≔ begin
assume a y H;
refine lemmaExt (join (pair a (pair a a))) (cr omega (i (Succ y))) _;
assume c;
refine and_i _ _ _ _
{assume H1;
refine imp_e (`∃ z, ((z < y) ∨ (z = y)) ∧ (c simeq (cr omega (i z)))) _ _ _
{assume H';
refine ex_e node _ H' _ _;
assume z Hz;
refine ex_i node (i z) _ _;
refine and_i _ _ _ _
{refine (and_er _ _ (lemma24 (i z) (Succ y))) _;
refine ex_i node z _ _;
refine and_i _ _ (refl node (i z)) (and_el _ _ Hz)}
{refine and_er _ _ Hz}}
{refine imp_e ((`∃ z, (z < y) ∧ (c simeq (cr omega (i z)))) ∨ (c simeq (cr omega (i y)))) _ _ _
{assume H';
refine or_e _ _ _ H' _ _
{assume H'';
refine ex_e node _ H'' _ _;
assume z Hz;
refine ex_i node z _ _;
refine and_i _ _ _ _
{refine or_il _ _ _;
refine and_el _ _ Hz}
{refine and_er _ _ Hz}}
{assume H'';
refine ex_i node y _ _;
refine and_i _ _ _ _
{refine or_ir _ _ _;
refine refl node y}
{refine H''}}}
{refine imp_e ((c ∈ (cr omega (i y))) ∨ (c simeq (cr omega (i y)))) _ _ _
{assume H';
refine or_e _ _ _ H' _ _
{assume H'';
refine or_il _ _ _;
refine ex_e node _ H'' _ _;
assume x Hx;
refine ex_e node _ (and_el _ _ (lemma24 x y) (and_el _ _ Hx)) _ _;
assume z Hz;
refine ex_i node z _ _;
refine and_i _ _ (and_er _ _ Hz) _;
refine imp_i (i z = x) _ _ _
{assume K;
refine imp_i (x = i z) _ _ _
{assume K';
refine K' (λ w, c simeq (cr omega w)) _;
refine and_er _ _ Hx}
{refine and_el _ _ Hz}}
{refine sym node x (i z) (and_el _ _ Hz)}}
{assume H'';
refine or_ir _ _ _;
refine H''}}
{refine imp_e ((c ∈ a) ∨ (c simeq a)) _ _ _
{assume H';
refine or_e _ _ _ H' _ _
{assume Hca;
refine or_il _ _ _;
refine lemma31 c a (cr omega (i y)) (and_i _ _ Hca H)}
{assume Hca;
refine or_ir _ _ _;
refine lemma5 c a (cr omega (i y)) (and_i _ _ Hca H)}}
{refine and_el _ _ (lemmaJoinPair a c) H1}}}}}
{assume H2;
refine imp_e ((c ∈ a) ∨ (c simeq a)) _ _ _
{assume H';
refine and_er _ _ (lemmaJoinPair a c) H'}
{refine imp_e ((c ∈ (cr omega (i y))) ∨ (c simeq (cr omega (i y)))) _ _ _
{assume H';
refine or_e _ _ _ H' _ _
{assume K;
refine or_il _ _ _;
refine lemma31 c (cr omega (i y)) a (and_i _ _ K (lemma4 a (cr omega (i y)) H))}
{assume K';
refine or_ir _ _ _;
refine lemma5 c (cr omega (i y)) a (and_i _ _ K' (lemma4 a (cr omega (i y)) H))}}
{refine imp_e ((`∃ z, (z < y) ∧ (c simeq (cr omega (i z)))) ∨ (c simeq (cr omega (i y)))) _ _ _
{assume H';
refine or_e _ _ _ H' _ _
{assume K;
refine or_il _ _ _;
refine ex_e node _ K _ _;
assume z Hz;
refine ex_i node (i z) _ _;
refine and_i _ _ _ (and_er _ _ Hz);
refine (and_er _ _ (lemma24 (i z) y)) _;
refine ex_i node z _ _;
refine and_i _ _ (refl node (i z)) (and_el _ _ Hz)}
{assume K';
refine or_ir _ _ _;
refine K'}}
{refine imp_e (`∃ z, ((z < y) ∨ (z = y)) ∧ (c simeq (cr omega (i z)))) _ _ _
{assume H';
refine ex_e node _ H' _ _;
assume z Hz;
refine or_e _ _ _ (and_el _ _ Hz) _ _
{assume K;
refine or_il _ _ _;
refine ex_i node z _ _;
refine and_i _ _ K (and_er _ _ Hz)}
{assume K';
refine or_ir _ _ _;
refine imp_i (y = z) _ _ _
{assume M;
refine imp_i (z = y) _ _ _
{assume M';
refine M' (λ w, c simeq (cr omega (i w))) _;
refine and_er _ _ Hz}
{refine K'}}
{refine sym node z y K'}}}
{refine ex_e node _ H2 _ _;
assume x Hx;
refine ex_e node _ (and_el _ _ (lemma24 x (Succ y)) (and_el _ _ Hx)) _ _;
assume z Hz;
refine ex_i node z _ _;
refine and_i _ _ (and_er _ _ Hz) _;
refine imp_i (i z = x) _ _ _
{assume M;
refine imp_i (x = i z) _ _ _
{assume M';
refine M' (λ w, c simeq (cr omega w)) _;
refine and_er _ _ Hx}
{refine and_el _ _ Hz}}
{refine sym node x (i z) (and_el _ _ Hz)}}}}}}
end;

opaque symbol lemma49 : π(empty_set ∈ omega)
≔ begin
refine ex_i node (i O) _ _;
refine and_i _ _ _ _
{refine (and_er _ _ (lemma25 (i O))) _;
refine ex_i node O _ _;
refine and_i _ _ _ _
{refine refl node (i O)}
{refine top_i}}
{refine lemma47}
end;

opaque symbol lemma50 : π(`∀ a, (a ∈ omega) ⇒ ((join (pair a (pair a a))) ∈ omega))
≔ begin
assume a Ha;
refine ex_e node _ Ha _ _;
assume x Hx;
refine ex_e node _ ((and_el _ _ (lemma25 x)) (and_el _ _ Hx)) _ _;
assume y Hy;
refine ex_i node (i (Succ y)) _ _;
refine and_i _ _ _ _
{refine (and_er _ _ (lemma25 (i (Succ y)))) _;
refine ex_i node (Succ y) _ _;
refine and_i _ _ _ _
{refine refl node (i (Succ y))}
{refine and_er _ _ Hy}}
{refine lemma48 a y _;
refine imp_i (i y = x) _ _ _
{assume H1;
refine imp_i (x = i y) _ _ _
{assume H2;
refine H2 (λ w, a simeq (cr omega w)) (and_er _ _ Hx)}
{refine sym node (i y) x H1}}
{refine sym node x (i y) (and_el _ _ Hy)}}
end;

opaque symbol lemma51 : π(Ind omega)
≔ begin
refine and_i _ _ _ _
{refine lemma49}
{refine lemma50}
end;
