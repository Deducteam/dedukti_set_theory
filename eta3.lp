require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.bisimilarity;
require open Logic.Z.injectivity;
require open Logic.Z.eta1;
require open Logic.Z.eta2;
require open Logic.Z.formulas;
require open Logic.Z.nat;
require open Logic.Z.language2;

opaque symbol lemma22 : Π (σ : (El nat → El graph)), Π (f : El formula), π(`∀ a, `∀ x, `∀ y', (eta (comp a σ f) x (i y') ⇔ (`∃ y, (x = i y) ∧ (eta a y y'))))
≔ begin
assume σ f;
assume a x y;
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H1;
refine ExElim node _ H1 _ _; 
assume z Hz;
refine ExElim node _ Hz _ _; 
assume y' Hy';
refine ExIntro node z _ _;
refine and_i _ _ _ _
{refine and_eg _ _ (and_eg _ _ Hy')}
{refine imp_i (y = y') _ _ _
{assume H2;
refine imp_i (y' = y) _ _ _
{assume H3;
refine H3 (λ w, eta a z w) (and_ed _ _ Hy')}
{refine lemmaSymEg node _ _ H2}}
{refine lemma9 _ _ (and_ed _ _ (and_eg _ _ Hy'))}}}
{assume H4;
refine f_e _ _;
refine ExElim node _ H4 _ _; 
assume z Hz;
refine lemma11 y (and_ed _ _ (and_eg _ _ (and_eg _ _ Hz)))}}
{assume H;
refine ExElim node _ H _ _;
assume z Hz;
refine or_ig _ _ _;
refine ExIntro node z _ _;
refine ExIntro node y _ _;
refine and_i _ _ (and_i _ _ (and_eg _ _ Hz) (refl node (i y))) (and_ed _ _ Hz)}
end;

opaque symbol lemma23 : Π (σ : (El nat → El graph)), Π (f : El formula), π(`∀ a, `∀ x, (eta (comp a σ f) x o ⇔ (`∃ y, (x = i y) ∧ (eta a y (root a)) ∧ (interpretation (update σ zero (cr a y)) f))))
≔ begin
assume σ f;
assume a x;
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H1;
refine f_e _ _;
refine ExElim node _ H1 _ _; 
assume y Hy;
refine ExElim node _ Hy _ _; 
assume y' Hy';
refine lemma11 y' (lemmaSymEg node _ _ (and_ed _ _ (and_eg _ _ Hy')))}
{assume H2;
refine ExElim node _ H2 _ _;
assume y Hy;
refine ExIntro node y _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_eg _ _ (and_eg _ _ (and_eg _ _ Hy))}
{refine and_ed _ _ (and_eg _ _ Hy)}}
{refine and_ed _ _ Hy}}}
{assume H;
refine ExElim node _ H _ _;
assume y Hy;
refine or_id _ _ _;
refine ExIntro node y _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_i _ _ (and_eg _ _ (and_eg _ _ Hy)) (refl node o)}
{refine and_ed _ _ (and_eg _ _ Hy)}}
{refine and_ed _ _ Hy}}
end;

opaque symbol lemma24 : π(`∀ x, `∀ y', (eta omega x (i y')) ⇔ (`∃ y, (x = i y) ∧ (y < y')))
≔ begin
assume x y';
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H1;
refine ExElim node _ H1 _ _; 
assume y Hy;
refine ExElim node _ Hy _ _; 
assume z Hz;
refine ExIntro node y _ _;
refine and_i _ _ _ _
{refine and_eg _ _ (and_eg _ _ Hz)}
{refine imp_i (y' = z) _ _ _
{assume H2;
refine imp_i (z = y') _ _ _
{assume H3;
refine H3 (λ w, y < w) (and_ed _ _ Hz)}
{refine lemmaSymEg node _ _ H2}}
{refine lemma9 _ _ (and_ed _ _ (and_eg _ _ Hz))}}}
{assume H4;
refine f_e _ _;
refine ExElim node _ H4 _ _; 
assume y Hy;
refine lemma11 y' (and_ed _ _ (and_eg _ _ Hy))}}
{assume H;
refine ExElim node _ H _ _;
assume y Hy;
refine or_ig _ _ _;
refine ExIntro node y _ _;
refine ExIntro node y' _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_eg _ _ Hy}
{refine refl node (i y')}}
{refine and_ed _ _ Hy}}
end;

opaque symbol lemma25 : π(`∀ x, (eta omega x o) ⇔ (`∃ y, (x = i y) ∧ (Nat y)))
≔ begin
assume x;
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H1;
refine f_e _ _;
refine ExElim node _ H1 _ _; 
assume y Hy;
refine ExElim node _ Hy _ _; 
assume y' Hy';
refine lemma11 y' (lemmaSymEg node _ _ (and_ed _ _ (and_eg _ _ Hy')))}
{assume H2;
refine ExElim node _ H2 _ _;
assume y Hy;
refine ExIntro node y _ _;
refine and_i _ _ _ _
{refine and_eg _ _ (and_eg _ _ Hy)}
{refine and_ed _ _ Hy}}}
{assume H;
refine ExElim node _ H _ _;
assume y Hy;
refine or_id _ _ _;
refine ExIntro node y _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_eg _ _ Hy}
{refine refl node o}}
{refine and_ed _ _ Hy}}
end;

opaque symbol lemma26 : π(`∀ a, `∀ x, `∀ y', (eta (Cl a) x (i y')) ⇔ (`∃ y, (x = i y) ∧ (eta a y y')))
≔ begin
assume a x y';
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H1;
refine ExElim node _ H1 _ _; 
assume y Hy;
refine ExElim node _ Hy _ _; 
assume z Hz;
refine ExIntro node y _ _;
refine and_i _ _ _ _
{refine and_eg _ _ (and_eg _ _ Hz)}
{refine imp_i (y' = z) _ _ _
{assume H2;
refine imp_i (z = y') _ _ _
{assume H3;
refine H3 (λ w, eta a y w) (and_ed _ _ Hz)}
{refine lemmaSymEg node _ _ H2}}
{refine lemma9 _ _ (and_ed _ _ (and_eg _ _ Hz))}}}
{assume H4;
refine f_e _ _;
refine ExElim node _ H4 _ _; 
assume y Hy;
refine lemma11 y' (and_ed _ _ (and_eg _ _ Hy))}}
{assume H;
refine ExElim node _ H _ _;
assume y Hy;
refine or_ig _ _ _;
refine ExIntro node y _ _;
refine ExIntro node y' _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_eg _ _ Hy}
{refine refl node (i y')}}
{refine and_ed _ _ Hy}}
end;

opaque symbol lemma27 : π(`∀ a, `∀ x, (eta (Cl a) x o) ⇔ (`∃ y, ((x = i y) ∧ (`∀ c : El (node arrow prop), ((`∀ z, (eta a z (root a)) ⇒ (c z)) ∧ (`∀ z, `∀ z', (((eta a z z') ∧ (c z')) ⇒ (c z)))) ⇒ c y))))
≔ begin
assume a x;
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H1;
refine f_e _ _;
refine ExElim node _ H1 _ _; 
assume y Hy;
refine ExElim node _ Hy _ _; 
assume y' Hy';
refine lemma11 y' (lemmaSymEg node _ _ (and_ed _ _ (and_eg _ _ Hy')))}
{assume H2;
refine ExElim node _ H2 _ _;
assume y Hy;
refine ExIntro node y _ _;
refine and_i _ _ (and_eg _ _ (and_eg _ _ Hy)) (and_ed _ _ Hy)}}
{assume H;
refine ExElim node _ H _ _;
assume y Hy;
refine or_id _ _ _;
refine ExIntro node y _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_eg _ _ Hy}
{refine refl node o}}
{refine and_ed _ _ Hy}}
end;
