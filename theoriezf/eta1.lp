require open zf.theoriezf.logic;
require open zf.theoriezf.language;
require open zf.theoriezf.bisimilarity;
require open zf.theoriezf.injectivity;

opaque symbol lemma14 : π(`∀ a, `∀ x, `∀ y', (eta (join a) x (i y')) ⇔ (`∃ y, (x = i y) ∧ (eta a y y')))
≔ begin
assume a x y';
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H1;
refine ExElim n _ H1 _ _;
assume y Hy;
refine ExElim n _ Hy _ _;
assume y'' Hy'';
refine ExIntro n y _ _;
refine and_i _ _ _ _
{refine and_eg _ _ (and_eg _ _ Hy'')}
{refine imp_i (y' = y'') _ _ _
{assume H2;
refine imp_i (y'' = y') _ _ _
{assume H3;
refine H3 (λ z, eta a y z) (and_ed _ _ Hy'')}
{refine lemmaSymEg n _ _ H2}}
{refine lemma9 _ _ (and_ed _ _ (and_eg _ _ Hy''))}}}
{assume H4;
refine f_e _ _;
refine ExElim n _ H4 _ _; 
assume y Hy;
refine ExElim n _ Hy _ _; 
assume z Hz;
refine lemma11 y' _;
refine and_ed _ _ (and_eg _ _ (and_eg _ _ Hz))}}
{assume H;
refine ExElim n _ H _ _;
assume y Hy;
refine or_ig _ _ _;
refine ExIntro n y _ _;
refine ExIntro n y' _ _;
refine and_i _ _ (and_i _ _ (and_eg _ _ Hy) (refl n (i y'))) (and_ed _ _ Hy)}
end;

opaque symbol lemma15 : π(`∀ a, `∀ x, (eta (join a) x o) ⇔ (`∃ y, `∃ z, (x = i y) ∧ (eta a y z) ∧ (eta a z (root a))))
≔ begin
assume a x;
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H1;
refine f_e _ _;
refine ExElim n _ H1 _ _; 
assume y Hy;
refine ExElim n _ Hy _ _; 
assume y' Hy';
refine lemma11 y' _;
refine lemmaSymEg n _ _ (and_ed _ _ (and_eg _ _ Hy'))}
{assume H2;
refine ExElim n _ H2 _ _;
assume y Hy;
refine ExElim n _ Hy _ _;
assume z Hz;
refine ExIntro n y _ _;
refine ExIntro n z _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_eg _ _ (and_eg _ _ (and_eg _ _ Hz))}
{refine (and_ed _ _ (and_eg _ _ Hz))}}
{refine and_ed _ _ Hz}}}
{assume H;
refine or_id _ _ _;
refine ExElim n _ H _ _;
assume y Hy;
refine ExElim n _ Hy _ _;
assume z Hz;
refine ExIntro n y _ _;
refine ExIntro n z _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_i _ _ (and_eg _ _ (and_eg _ _ Hz)) (refl n o)}
{refine and_ed _ _ (and_eg _ _ Hz)}}
{refine and_ed _ _ Hz}}
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
refine ExElim n _ H1 _ _;
assume y Hy;
refine ExElim n _ Hy _ _; 
assume z Hz;
refine ExIntro n y _ _;
refine and_i _ _ _ _
{refine and_eg _ _ (and_eg _ _ Hz)}
{refine imp_i (y' = z) _ _ _
{assume H2;
refine imp_i (z = y') _ _ _
{assume H3;
refine H3 (λ w, eta a y w) (and_ed _ _ Hz)}
{refine lemmaSymEg n _ _ H2}}
{refine lemma9 _ _ (and_ed _ _ (and_eg _ _ Hz))}}}
{assume H5;
refine f_e _ _;
refine ExElim n _ H5 _ _;
assume y Hy;
refine ExElim n _ Hy _ _; 
assume z Hz;
refine lemma13 y' z (and_ed _ _ (and_eg _ _ Hz))}}
{assume H6;
refine f_e _ _;
refine lemma11 y' (and_ed _ _ H6)}}
{assume H7;
refine f_e _ _;
refine lemma11 y' (and_ed _ _ H7)}}
{assume H;
refine or_ig _ _ _;
refine or_ig _ _ _;
refine or_ig _ _ _;
refine ExElim n _ H _ _;
assume y Hy;
refine ExIntro n y _ _;
refine ExIntro n y' _ _;
refine and_i _ _ (and_i _ _ (and_eg _ _ Hy) (refl n (i y'))) (and_ed _ _ Hy)}
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
refine f_e _ _;
refine ExElim n _ H1 _ _; 
assume y Hy;
refine ExElim n _ Hy _ _; 
assume z Hz;
refine lemma13 z y' (lemmaSymEg n _ _ (and_ed _ _ (and_eg _ _ Hz)))}
{assume H2;
refine ExElim n _ H2 _ _;
assume y Hy;
refine ExElim n _ Hy _ _; 
assume z Hz;
refine ExIntro n y _ _;
refine and_i _ _ _ _
{refine and_eg _ _ (and_eg _ _ Hz)}
{refine imp_i (y' = z) _ _ _
{assume H3;
refine imp_i (z = y') _ _ _
{assume H4;
refine H4 (λ w, eta b y w) (and_ed _ _ Hz)}
{refine lemmaSymEg n _ _ H3}}
{refine lemma10 _ _ (and_ed _ _ (and_eg _ _ Hz))}}}}
{assume H5;
refine f_e _ _;
refine lemma12 y' (and_ed _ _ H5)}}
{assume H6;
refine f_e _ _;
refine lemma12 y' (and_ed _ _ H6)}}
{assume H;
refine or_ig _ _ _;
refine or_ig _ _ _;
refine or_id _ _ _;
refine ExElim n _ H _ _;
assume y Hy;
refine ExIntro n y _ _;
refine ExIntro n y' _ _;
refine and_i _ _ (and_i _ _ (and_eg _ _ Hy) (refl n (j y'))) (and_ed _ _ Hy)}
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
refine f_e _ _;
refine ExElim n _ H1 _ _;
assume y Hy;
refine ExElim n _ Hy _ _;
assume z Hz;
refine lemma11 z (lemmaSymEg n _ _ (and_ed _ _ (and_eg _ _ Hz)))}
{assume H2;
refine f_e _ _;
refine ExElim n _ H2 _ _; 
assume y Hy;
refine ExElim n _ Hy _ _; 
assume z Hz;
refine lemma12 z (lemmaSymEg n _ _ (and_ed _ _ (and_eg _ _ Hz)))}}
{assume H3;
refine or_ig _ _ (and_eg _ _ H3)}}
{assume H4;
refine or_id _ _ (and_eg _ _ H4)}}
{assume H;
refine or_e _ _ _ H _ _
{assume Hi;
refine or_ig _ _ _;
refine or_id _ _ _;
refine and_i _ _ Hi (refl n o)}
{assume Hj;
refine or_id _ _ _;
refine and_i _ _ Hj (refl n o)}}
end; 