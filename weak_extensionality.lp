require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.bisimilarity;
require open Logic.Z.injectivity;
require open Logic.Z.eta1;
require open Logic.Z.eta2;
require open Logic.Z.membership;
require open Logic.Z.lemma32;
require open Logic.Z.lemma41;
require open Logic.Z.nat;
require open Logic.Z.formulas;
require open Logic.Z.formulas_lemmas;
require open Logic.Z.language2;

opaque symbol lemmaHypExt : Π (c d : El graph), π((`∀ z, (z ∈ c) ⇔ (z ∈ d)) ⇒ ((((c simeq c) ∧ (d simeq d)) ∨ (c simeq d))
∧ (`∀ a, `∀ a', `∀ b, ((a' ∈ a) ∧ (((a simeq c) ∧ (b simeq d)) ∨ (a simeq b))) ⇒ (`∃ b', ((b' ∈ b) ∧ (((a' simeq c) ∧ (b' simeq d)) ∨ (a' simeq b')))))
∧ (`∀ b, `∀ b', `∀ a, ((b' ∈ b) ∧ (((a simeq c) ∧ (b simeq d)) ∨ (a simeq b))) ⇒ (`∃ a', ((a' ∈ a) ∧ (((a' simeq c) ∧ (b' simeq d)) ∨ (a' simeq b')))))))
≔ begin
assume c d Hext;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine or_il _ _ _;
refine (and_i _ _ (lemma3 c) (lemma3 d))}
{assume a a' b H;
refine or_e _ _ _ (and_er _ _ H) _ _
{assume H1;
refine ex_i graph a' _ _;
refine and_i _ _ _ _
{refine lemma31 a' d b (and_i _ _ _ _)
{refine (and_el _ _ (Hext a')) (lemma31 a' a c (and_i _ _ (and_el _ _ H) (and_el _ _ H1)))}
{refine lemma4 b d (and_er _ _ H1)}}
{refine or_ir _ _ _;
refine lemma3 a'}}
{assume H2;
refine ex_i graph a' _ _;
refine and_i _ _ _ _
{refine lemma31 a' a b (and_i _ _ (and_el _ _ H) H2)}
{refine or_ir _ _ _;
refine lemma3 a'}}}}
{assume b b' a H;
refine or_e _ _ _ (and_er _ _ H) _ _
{assume H1;
refine ex_i graph b' _ _;
refine and_i _ _ _ _
{refine lemma31 b' c a (and_i _ _ _ _)
{refine (and_er _ _ (Hext b')) (lemma31 b' b d (and_i _ _ (and_el _ _ H) (and_er _ _ H1)))}
{refine lemma4 a c (and_el _ _ H1)}}
{refine or_ir _ _ _;
refine lemma3 b'}}
{assume H2;
refine ex_i graph b' _ _;
refine and_i _ _ _ _
{refine lemma31 b' b a (and_i _ _ (and_el _ _ H) (lemma4 a b H2))}
{refine or_ir _ _ _;
refine lemma3 b'}}}
end;

opaque symbol lemmaExt : Π (c d : El graph), π((`∀ x, (x ∈ c) ⇔ (x ∈ d)) ⇒ (c simeq d))
≔ begin
assume c d H;
refine lemma41 zero one (orF (andF (eqF zero two) (eqF one three)) (eqF zero one)) c d (update (update (λ _, empty_set) two c) three d) (lemmaHypExt c d H)
end;