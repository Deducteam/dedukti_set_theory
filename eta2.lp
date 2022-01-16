require open Logic.Z.logic;
require open Logic.Z.language;
require open Logic.Z.bisimilarity;
require open Logic.Z.injectivity;
require open Logic.Z.eta1;

opaque symbol lemma19 : π(`∀ a, `∀ x, `∀ y', (eta (powerset a) x (i y')) ⇔ (`∃ y, (x = i y) ∧ (eta a y y')))
≔ begin
assume a x y';
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H';
refine or_e _ _ _ H' _ _
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
{assume H4;
refine bottom_e _ _;
refine ex_e node _ H4 _ _; 
assume y Hy;
refine ex_e graph _ Hy _ _; 
assume c Hc;
refine lemma13 y' (ρ c) (and_er _ _ (and_el _ _ (and_el _ _ Hc)))}}
{assume H5;
refine bottom_e _ _;
refine ex_e graph _ H5 _ _; 
assume c Hc;
refine lemma11 y' (and_er _ _ Hc)}}
{assume H;
refine ex_e node _ H _ _;
assume y Hy;
refine or_il _ _ _;
refine or_il _ _ _;
refine ex_i node y _ _;
refine ex_i node y' _ _;
refine and_i _ _ (and_i _ _ (and_el _ _ Hy) (refl node (i y'))) (and_er _ _ Hy)}
end;

opaque symbol lemma20 : π(`∀ a, `∀ c, `∀ x, (eta (powerset a) x (j (ρ c))) ⇔ (`∃ y, (x = i y) ∧ (eta a y (root a)) ∧ ((cr a y) ∈ c )))
≔ begin
assume a c x;
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H';
refine or_e _ _ _ H' _ _
{assume H1;
refine bottom_e _ _;
refine ex_e node _ H1 _ _; 
assume y Hy;
refine ex_e node _ Hy _ _; 
assume y' Hy';
refine lemma13 y' (ρ c) (sym node _ _ (and_er _ _ (and_el _ _ Hy')))}
{assume H2;
refine ex_e node _ H2 _ _; 
assume y Hy;
refine ex_e graph _ Hy _ _; 
assume c' Hc';
refine ex_i node y _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_el _ _ (and_el _ _ (and_el _ _ Hc'))}
{refine and_er _ _ (and_el _ _ Hc')}}
{refine ex_e node _ (and_er _ _ Hc') _ _;
assume z Hz;
refine ex_i node z _ _;
refine and_i _ _ _ _
{refine imp_e (ρ c = ρ c') _ _ _
{assume H3;
refine imp_e (ρ c' = ρ c) _ _ _
{assume H4;
refine imp_e (eta (ρ^ (ρ c)) z (root (ρ^ (ρ c)))) (eta c z (root c)) _ _
{assume P;
refine P}
{refine H4 (λ w, eta (ρ^ w) z (root (ρ^ w))) _;
refine and_el _ _ Hz}}
{refine sym node _ _ H3}}
{refine lemma10 _ _ (and_er _ _ (and_el _ _ (and_el _ _ Hc')))}}
{refine ex_e (node arrow (node arrow prop)) _ (and_er _ _ Hz) _ _; 
assume r Hr;
refine ex_i (node arrow (node arrow prop)) r _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_el _ _ (and_el _ _ Hr)}
{assume u u' v Heta;
refine imp_e (ρ c = ρ c') _ _ _
{assume H5;
refine imp_e (ρ c' = ρ c) _ _ _
{assume H6;
refine ex_e node _ ((and_er _ _ (and_el _ _ Hr)) u u' v Heta) _ _;
assume y' Hy';
refine ex_i node y' _ _;
refine imp_e (eta (ρ^ (ρ c)) y' v ∧ r u' y') (eta c y' v ∧ r u' y') _ _
{assume P;
refine P}
{refine H6 (λ w, eta (ρ^ w) y' v ∧ r u' y') Hy'}}
{refine sym node _ _ H5}}
{refine lemma10 _ _ (and_er _ _ (and_el _ _ (and_el _ _ Hc')))}}}
{assume v v' u Heta;
refine (and_er _ _ Hr) v v' u _;
refine imp_e (ρ c' = ρ c) _ _ _
{assume H7;
refine imp_e (ρ c = ρ c') _ _ _
{assume H8;
refine imp_e (eta (ρ^ (ρ c')) v' v ∧ r u v) (eta c' v' v ∧ r u v) _ _
{assume P;
refine P}
{refine H8 (λ w, eta (ρ^ w) v' v ∧ r u v) Heta}}
{refine sym node _ _ H7}}
{refine lemma10 _ _ (sym node _ _ (and_er _ _ (and_el _ _ (and_el _ _ Hc'))))}}}}}}
{assume H9;
refine bottom_e _ _;
refine ex_e graph _ H9 _ _; 
assume c' Hc';
refine lemma12 (ρ c) (and_er _ _ Hc')}}
{assume H;
refine or_il _ _ _;
refine or_ir _ _ _;
refine ex_e node _ H _ _;
assume y Hy;
refine ex_i node y _ _;
refine ex_i graph c _ _;
refine and_i _ _ _ _
{refine and_i _ _ _ _
{refine and_i _ _ (and_el _ _ (and_el _ _ Hy)) (refl node (j (ρ c)))}
{refine and_er _ _ (and_el _ _ Hy)}}
{refine and_er _ _ Hy}}
end;

opaque symbol lemma21 : π(`∀ a, `∀ x, (eta (powerset a) x o) ⇔ (`∃ c, (x = j (ρ c))))
≔ begin
assume a x;
refine and_i _ _ _ _
{assume H;
refine or_e _ _ _ H _ _
{assume H';
refine or_e _ _ _ H' _ _
{assume H1;
refine bottom_e _ _;
refine ex_e node _ H1 _ _;
assume y Hy;
refine ex_e node _ Hy _ _; 
assume y' Hy';
refine lemma11 y' (sym node _ _ (and_er _ _ (and_el _ _ Hy')))}
{assume H2;
refine bottom_e _ _;
refine ex_e node _ H2 _ _;
assume y Hy;
refine ex_e graph _ Hy _ _; 
assume c Hc;
refine lemma12 (ρ c) (sym node _ _ (and_er _ _ (and_el _ _ (and_el _ _ Hc))))}}
{assume H3;
refine ex_e graph _ H3 _ _;
assume c Hc;
refine ex_i graph c _ _;
refine and_el _ _ Hc}}
{assume H;
refine ex_e graph _ H _ _;
assume c Hc;
refine or_ir _ _ _;
refine ex_i graph c _ _;
refine and_i _ _ Hc (refl node o)}
end;

