require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.bisimilarity;
require open Logic.Z.injectivity;

opaque symbol lemma14 : π(`∀ a, `∀ x, `∀ y', (eta (join a) x (i y')) ⇔ (`∃ y, (x = i y) ∧ (eta a y y')))
≔ begin
assume a x y';
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H1;
refine ex_e node _ H1 _ _;
assume y Hy;
refine ex_e node _ Hy _ _;
assume y'' Hy'';
refine ex_i node y _ _;
refine and_i _ _ _ _
{refine and_el _ _ (and_el _ _ Hy'')}
{refine imp_i (y' = y'') _ _ _
{assume H2;
refine imp_i (y'' = y') _ _ _
{assume H3;
refine H3 (λ z, eta a y z) (and_er _ _ Hy'')}
{refine sym node _ _ H2}}
{refine lemma9 _ _ (and_er _ _ (and_el _ _ Hy''))}}}
{assume H4;
refine bottom_e _ _;
refine ex_e node _ H4 _ _; 
assume y Hy;
refine ex_e node _ Hy _ _; 
assume z Hz;
refine lemma11 y' _;
refine and_er _ _ (and_el _ _ (and_el _ _ Hz))}}
{assume H;
refine ex_e node _ H _ _;
assume y Hy;
refine or_il _ _ _;
refine ex_i node y _ _;
refine ex_i node y' _ _;
refine and_i _ _ (and_i _ _ (and_el _ _ Hy) (refl node (i y'))) (and_er _ _ Hy)}
end;

opaque symbol lemma15 : π(`∀ a, `∀ x, (eta (join a) x o) ⇔ (`∃ y, `∃ z, (x = i y) ∧ (eta a y z) ∧ (eta a z (root a))))
≔ begin
assume a x;
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H1;
refine bottom_e _ _;
refine ex_e node _ H1 _ _; 
assume y Hy;
refine ex_e node _ Hy _ _; 
assume y' Hy';
refine lemma11 y' _;
refine sym node _ _ (and_er _ _ (and_el _ _ Hy'))}
{assume H2;
refine ex_e node _ H2 _ _;
assume y Hy;
refine ex_e node _ Hy _ _;
assume z Hz;
refine ex_i node y _ _;
refine ex_i node z _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_el _ _ (and_el _ _ (and_el _ _ Hz))}
{refine (and_er _ _ (and_el _ _ Hz))}}
{refine and_er _ _ Hz}}}
{assume H;
refine or_ir _ _ _;
refine ex_e node _ H _ _;
assume y Hy;
refine ex_e node _ Hy _ _;
assume z Hz;
refine ex_i node y _ _;
refine ex_i node z _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_i _ _ (and_el _ _ (and_el _ _ Hz)) (refl node o)}
{refine and_er _ _ (and_el _ _ Hz)}}
{refine and_er _ _ Hz}}
end;

opaque symbol lemma16 : π(`∀ a, `∀ b, `∀ x, `∀ y', (eta (pair a b) x (i y')) ⇔ (`∃ y, (x = i y) ∧ (eta a y y')))
≔ begin
assume a b x y';
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H';
refine or_e _ _ _ H' _ _
{assume H'';
refine or_e _ _ _ H'' _ _
{assume H1;
refine ex_e node _ H1 _ _;
assume y Hy;
refine ex_e node _ Hy _ _; 
assume z Hz;
refine ex_i node y _ _;
refine and_i _ _ _ _
{refine and_el _ _ (and_el _ _ Hz)}
{refine imp_i (y' = z) _ _ _
{assume H2;
refine imp_i (z = y') _ _ _
{assume H3;
refine H3 (λ w, eta a y w) (and_er _ _ Hz)}
{refine sym node _ _ H2}}
{refine lemma9 _ _ (and_er _ _ (and_el _ _ Hz))}}}
{assume H5;
refine bottom_e _ _;
refine ex_e node _ H5 _ _;
assume y Hy;
refine ex_e node _ Hy _ _; 
assume z Hz;
refine lemma13 y' z (and_er _ _ (and_el _ _ Hz))}}
{assume H6;
refine bottom_e _ _;
refine lemma11 y' (and_er _ _ H6)}}
{assume H7;
refine bottom_e _ _;
refine lemma11 y' (and_er _ _ H7)}}
{assume H;
refine or_il _ _ _;
refine or_il _ _ _;
refine or_il _ _ _;
refine ex_e node _ H _ _;
assume y Hy;
refine ex_i node y _ _;
refine ex_i node y' _ _;
refine and_i _ _ (and_i _ _ (and_el _ _ Hy) (refl node (i y'))) (and_er _ _ Hy)}
end;

opaque symbol lemma17 : π(`∀ a, `∀ b, `∀ x, `∀ y', (eta (pair a b) x (j y')) ⇔ (`∃ y, (x = j y) ∧ (eta b y y')))
≔ begin
assume a b x y';
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H';
refine or_e _ _ _ H' _ _
{assume H'';
refine or_e _ _ _ H'' _ _
{assume H1;
refine bottom_e _ _;
refine ex_e node _ H1 _ _; 
assume y Hy;
refine ex_e node _ Hy _ _; 
assume z Hz;
refine lemma13 z y' (sym node _ _ (and_er _ _ (and_el _ _ Hz)))}
{assume H2;
refine ex_e node _ H2 _ _;
assume y Hy;
refine ex_e node _ Hy _ _; 
assume z Hz;
refine ex_i node y _ _;
refine and_i _ _ _ _
{refine and_el _ _ (and_el _ _ Hz)}
{refine imp_i (y' = z) _ _ _
{assume H3;
refine imp_i (z = y') _ _ _
{assume H4;
refine H4 (λ w, eta b y w) (and_er _ _ Hz)}
{refine sym node _ _ H3}}
{refine lemma10 _ _ (and_er _ _ (and_el _ _ Hz))}}}}
{assume H5;
refine bottom_e _ _;
refine lemma12 y' (and_er _ _ H5)}}
{assume H6;
refine bottom_e _ _;
refine lemma12 y' (and_er _ _ H6)}}
{assume H;
refine or_il _ _ _;
refine or_il _ _ _;
refine or_ir _ _ _;
refine ex_e node _ H _ _;
assume y Hy;
refine ex_i node y _ _;
refine ex_i node y' _ _;
refine and_i _ _ (and_i _ _ (and_el _ _ Hy) (refl node (j y'))) (and_er _ _ Hy)}
end;

opaque symbol lemma18 : π(`∀ a, `∀ b, `∀ x, (eta (pair a b) x o) ⇔ ((x = i (root a)) ∨ (x = j (root b))))
≔ begin
assume a b x;
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H';
refine or_e _ _ _ H' _ _
{assume H'';
refine or_e _ _ _ H'' _ _
{assume H1;
refine bottom_e _ _;
refine ex_e node _ H1 _ _;
assume y Hy;
refine ex_e node _ Hy _ _;
assume z Hz;
refine lemma11 z (sym node _ _ (and_er _ _ (and_el _ _ Hz)))}
{assume H2;
refine bottom_e _ _;
refine ex_e node _ H2 _ _; 
assume y Hy;
refine ex_e node _ Hy _ _; 
assume z Hz;
refine lemma12 z (sym node _ _ (and_er _ _ (and_el _ _ Hz)))}}
{assume H3;
refine or_il _ _ (and_el _ _ H3)}}
{assume H4;
refine or_ir _ _ (and_el _ _ H4)}}
{assume H;
refine or_e _ _ _ H _ _
{assume Hi;
refine or_il _ _ _;
refine or_ir _ _ _;
refine and_i _ _ Hi (refl node o)}
{assume Hj;
refine or_ir _ _ _;
refine and_i _ _ Hj (refl node o)}}
end; 