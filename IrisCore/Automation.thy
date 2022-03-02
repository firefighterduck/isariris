theory Automation
imports ProofRules "HOL-Eisbach.Eisbach_Tools"
begin

method itac = tactic all_tac

method iIntro = 
  (match conclusion in "upred_holds _" \<Rightarrow> \<open>rule upred_wand_holdsI\<close>)?,((rule upred_wandI)+)?
  
method entails_substL uses rule rule_eq = 
  (match rule_eq in "_ = _" \<Rightarrow> \<open>rule upred_entails_trans[OF upred_entails_eq[OF rule_eq]]\<close>)
| (match rule in "_" \<Rightarrow> \<open>rule upred_entails_substE[OF rule, unfolded upred_sep_assoc_eq]\<close>)
| (match rule in "_" \<Rightarrow> \<open>rule upred_entails_trans[OF rule]\<close>)
| (match rule in "_" \<Rightarrow> \<open>rule upred_entails_substE'[OF rule, unfolded upred_conj_assoc]\<close>)

method entails_substR uses rule rule_eq = 
  (match rule_eq in "_ = _" \<Rightarrow> \<open>rule upred_entails_trans[OF _ upred_entails_eq[OF rule_eq]]\<close>)
| (match rule in "_" \<Rightarrow> \<open>rule upred_entails_substI[OF rule, unfolded upred_sep_assoc_eq]\<close>)
| (match rule in "_" \<Rightarrow> \<open>rule upred_entails_trans[OF _ rule]\<close>)

method dupl_pers = (entails_substL rule: upred_entail_eqR[OF persistent_dupl], (pers_solver; fail))?

method subst_pers_keepL uses rule =
  (entails_substL rule: persistent_keep[OF _ rule], (pers_solver; fail))
| entails_substL rule: rule

method find_pat_sep for pat trm :: "'a::ucamera upred_f" = 
  match (trm) in "pat" \<Rightarrow> itac
  \<bar> "_\<^emph>pat" \<Rightarrow> itac
  \<bar> "pat\<^emph>_" \<Rightarrow> itac
  \<bar> "rest\<^emph>_" for rest :: "'a upred_f" \<Rightarrow> \<open>find_pat_sep pat rest\<close>   

method move_sepL for pat :: "'a::ucamera upred_f" =
  match conclusion in \<open>hyps \<turnstile> goal\<close> for hyps goal :: "'a upred_f" \<Rightarrow>
    \<open> find_pat_sep pat hyps; match (hyps) in "pat" \<Rightarrow> itac
      \<bar> "_\<^emph>pat" \<Rightarrow> itac
      \<bar> "pat\<^emph>_" \<Rightarrow> \<open>subst upred_sep_comm\<close>
      \<bar> "_\<^emph>pat\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm2R\<close>
      \<bar> "pat\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule_eq: upred_sep_comm2L; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm3M; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm3L; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm4_2; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm4_1; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm5_2; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm5_1; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm6_2; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm6_1; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm7_2; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm7_1; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm8_2; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm8_1; move_sepL pat\<close>
      \<bar> "_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm8_1; move_sepL pat\<close>
    \<close>

method move_sepR for pat :: "'a::ucamera upred_f" =
  match conclusion in \<open>hyps \<turnstile> goal\<close> for hyps goal :: "'a upred_f" \<Rightarrow>
    \<open> find_pat_sep pat goal; match (goal) in "pat" \<Rightarrow> itac
      \<bar> "_\<^emph>pat" \<Rightarrow> itac
      \<bar> "pat\<^emph>_" \<Rightarrow> \<open>entails_substR rule_eq: upred_sep_comm\<close>
      \<bar> "_\<^emph>pat\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm2R\<close>
      \<bar> "pat\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule_eq: upred_sep_comm2L; move_sepR pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm3M; move_sepR pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm3L; move_sepR pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm4_2; move_sepR pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm4_1; move_sepR pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm5_2; move_sepR pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm5_1; move_sepR pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm6_2; move_sepR pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm6_1; move_sepR pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm7_2; move_sepR pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm7_1; move_sepR pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm8_2; move_sepR pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm8_1; move_sepR pat\<close>
      \<bar> "_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm8_1; move_sepR pat\<close>
    \<close>

method move_sep for left :: bool and pat :: "'a::ucamera upred_f" = 
  match (left) in True \<Rightarrow> \<open>move_sepL pat\<close>
  \<bar> False \<Rightarrow> \<open>move_sepR pat\<close>
    
method move_sep_all for left :: bool and trm :: "'a::ucamera upred_f" =
  match (trm) in "rest\<^emph>head" for rest head :: "'a upred_f" \<Rightarrow> \<open>move_sep_all left rest; move_sep left head\<close>
  \<bar> "P" for P :: "'a upred_f" \<Rightarrow> \<open>move_sep left P\<close>

method move_sep_both for trm :: "'a::ucamera upred_f" =
  move_sepL trm, move_sepR trm

method iApply uses rule =
  match rule in "hyps \<turnstile> goal" for hyps goal \<Rightarrow> \<open>move_sep_all True hyps, subst_pers_keepL rule: rule\<close>
  \<bar> "_ \<Longrightarrow> hyps \<turnstile> goal" for hyps goal \<Rightarrow> \<open>move_sep_all True hyps, subst_pers_keepL rule: rule\<close>
  
method iExistsL =
  (move_sepL "upred_exists ?P", (rule pull_exists_antecedentR)+; rule upred_existsE';
    (simp only: upred_sep_assoc_eq)?)
method iExistsR for inst =
  (move_sepR "upred_exists ?P"; (unfold pull_exists_eq pull_exists_eq')?; 
    rule upred_existsI[of _ _ inst]; (simp only: upred_sep_assoc_eq)?)

method iPureL for dupl =
  (move_sepL "upred_pure ?b", match (dupl) in True \<Rightarrow> dupl_pers \<bar> False \<Rightarrow> itac, rule upred_pure_impl)

method iPureR = 
  (move_sepR "upred_pure ?b", (rule upred_pureI' | rule upred_pureI))
  
method find_applicable_wand for whole trm :: "'a::ucamera upred_f" =
  match (trm) in "P-\<^emph>Q" for P Q :: "'a upred_f" \<Rightarrow>
    \<open>find_pat_sep P whole; move_sepL P; dupl_pers; move_sepL "P-\<^emph>Q"\<close>
  \<bar> "_\<^emph>(P-\<^emph>Q)" for P Q :: "'a upred_f" \<Rightarrow>
    \<open>find_pat_sep P whole; move_sepL P; dupl_pers; move_sepL "P-\<^emph>Q"\<close>
  \<bar> "rest\<^emph>_" for rest :: "'a upred_f" \<Rightarrow> \<open>find_applicable_wand whole rest\<close>

method iApply_wand =
  match conclusion in \<open>hyps \<turnstile> goal\<close> for hyps goal \<Rightarrow>
    \<open>find_applicable_wand hyps hyps; subst_pers_keepL rule: upred_wand_apply\<close>

method iFrame_single = 
  match conclusion in \<open>hyps \<turnstile> goal\<close> for hyps goal :: "'a::ucamera upred_f" \<Rightarrow>
    \<open> match (goal) in "_\<^emph>P" for P \<Rightarrow> \<open>move_sepL P; dupl_pers; rule upred_frame\<close> 
      \<bar> P for P :: "'a upred_f" \<Rightarrow> 
      \<open>move_sepL P; rule upred_entails_refl | rule upred_weakeningL | rule upred_weakeningR\<close> \<close>

method remove_emp = 
  match conclusion in \<open>hyps \<turnstile> goal\<close> for hyps goal :: "'a::ucamera upred_f" \<Rightarrow>
    \<open>(find_pat_sep upred_emp hyps; move_sepL upred_emp; simp only: upred_true_sep; remove_emp)?;
     (find_pat_sep upred_emp goal; move_sepR upred_emp; simp only: upred_true_sep; remove_emp)?\<close>
  
lemma test_lemma: "S \<^emph> (\<box>P) \<^emph> Q \<^emph> ((\<box>P)-\<^emph>\<box>R) \<^emph> (\<triangleright>R) -\<^emph> (\<box>R) \<^emph> (\<triangleright>R) \<^emph> Q"
apply iIntro
apply iApply_wand
by iFrame_single+
end