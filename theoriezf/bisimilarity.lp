require open zf.theoriezf.logic;
require open zf.theoriezf.language;

opaque symbol lemma3 : π(`∀ a : El graph, a simeq a)
≔ begin
assume a;
refine ExIntro (node arrow (node arrow prop)) (λ a, λ b, a = b) _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine refl node (root a)}
{assume x x' y H;
refine ExIntro node x' _ _;
refine and_i _ _ _ _
{refine imp_e (x = y) (eta a x' y) _ _
{assume Heq;
refine Heq (λ w, eta a x' w) _;
refine and_eg _ _ H}
{refine and_ed _ _ H}}
{refine refl node x'}}}
{assume y y' x H;
refine ExIntro node y' _ _;
refine and_i _ _ _ _
{refine imp_e (y = x) (eta a y' x) _ _
{assume Heq;
refine Heq (λ w, eta a y' w) _;
refine and_eg _ _ H}
{refine lemmaSymEg node x y (and_ed (eta a y' y) (x = y) H)}}
{refine refl node y'}}
end;

opaque symbol lemma4 : π(`∀ a, `∀ b, (a simeq b) ⇒ (b simeq a))
≔ begin
assume a b H;
refine ExElim (node arrow (node arrow prop)) _ H _ _;
assume r Hr;
refine ExIntro (node arrow (node arrow prop)) (λ x, λ y, r y x) _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_eg _ _ (and_eg _ _ Hr)}
{assume y y' x H1;
refine ((and_ed _ _ Hr) y y' x) H1}}
{assume x x' y H2;
refine and_ed _ _ (and_eg _ _ Hr) x x' y H2}
end;

opaque symbol lemma5 : π(`∀ a, `∀ b, `∀ c, ((a simeq b) ∧ (b simeq c)) ⇒ (a simeq c))
≔ begin
assume a b c H;
refine ExElim (node arrow (node arrow prop)) _ (and_eg _ _ H) _ _;
assume rab Hab;
refine ExElim (node arrow (node arrow prop)) _ (and_ed _ _ H) _ _;
assume rbc Hbc;
refine ExIntro (node arrow (node arrow prop)) (λ x, λ z, `∃ y, rab x y ∧ rbc y z) _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine ExIntro node (root b) _ _;
refine and_i _ _ (and_eg _ _ (and_eg _ _ Hab)) (and_eg _ _ (and_eg _ _ Hbc))}
{assume x x' y H1;
refine ExElim node _ (and_ed _ _ H1) _ _;
assume u Hu;
refine ExElim node _ (imp_e _ _ ((and_ed _ _ (and_eg _ _ Hab)) x x' u) (and_i _ _ (and_eg _ _ H1) (and_eg _ _ Hu))) _ _;
assume v Hv;
refine ExElim node _ (imp_e _ _ ((and_ed _ _ (and_eg _ _ Hbc)) u v y) (and_i _ _ (and_eg _ _ Hv) (and_ed _ _ Hu))) _ _;
assume y' H2;
refine ExIntro node y' _ _;
refine and_i _ _ _ _
{refine (and_eg _ _ H2)}
{refine ExIntro node v _ _;
refine (and_i _ _ (and_ed _ _ Hv) (and_ed _ _ H2))}}}
{assume y y' x H3;
refine ExElim node _ (and_ed _ _ H3) _ _;
assume u Hu;
refine ExElim node _ (imp_e _ _ ((and_ed _ _ Hbc) y y' u) (and_i _ _ (and_eg _ _ H3) (and_ed _ _ Hu))) _ _;
assume v Hv;
refine ExElim node _ (imp_e _ _ ((and_ed _ _ Hab) u v x) (and_i _ _ (and_eg _ _ Hv) (and_eg _ _ Hu))) _ _;
assume x' H4;
refine ExIntro node x' _ _;
refine and_i _ _ _ _
{refine (and_eg _ _ H4)}
{refine ExIntro node v _ _;
refine (and_i _ _ (and_ed _ _ H4) (and_ed _ _ Hv))}}
end;

opaque symbol lemma6 : π(`∀ a, a simeq (cr a (root a)))
≔ begin
assume a;
refine ExIntro (node arrow (node arrow prop)) (λ x, λ y, x = y) _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine refl node _}
{assume x x' y H;
refine ExIntro node x' _ _;
refine and_i _ _ _ _
{refine imp_e (eta a x' x) _ _ _
{assume H1;
refine imp_e (x = y) _ _ _
{assume H2;
refine H2 (λ z, eta a x' z) H1}
{refine and_ed _ _ H}}
{refine and_eg _ _ H}}
{refine refl node _}}}
{assume y y' x H;
refine ExIntro node y' _ _;
refine and_i _ _ _ _
{refine imp_e (eta a y' y) _ _ _
{assume H1;
refine imp_e (x = y) _ _ _
{assume H2;
refine imp_e (y = x) _ _ _
{assume H3;
refine H3 (λ z, eta a y' z) H1}
{refine lemmaSymEg node _ _ H2}}
{refine and_ed _ _ H}}
{refine and_eg _ _ H}}
{refine refl node _}}
end;
