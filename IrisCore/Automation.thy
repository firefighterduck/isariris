theory Automation
imports ProofRules "HOL-Eisbach.Eisbach_Tools"
begin

method itac = tactic all_tac

method iIntro = 
  (match conclusion in "upred_holds _" \<Rightarrow> \<open>rule upred_wand_holdsI\<close>)?,((rule upred_wandI)+)?
  
method entails_substL uses rule = 
  (match rule in "_ = _" \<Rightarrow> \<open>rule upred_entails_trans[OF upred_entails_eq[OF rule]]\<close>
   \<bar> "_ \<turnstile> _" \<Rightarrow> \<open>rule upred_entails_trans[OF rule]\<close>)
| rule upred_entails_substE[OF rule, unfolded upred_sep_assoc_eq]
| rule upred_entails_substE'[OF rule, unfolded upred_conj_assoc]

method move_sepL for pat :: "'a::ucamera upred_f" =
  match conclusion in \<open>hyps \<turnstile> goal\<close> for hyps goal \<Rightarrow>
    \<open> match (hyps) in "pat" \<Rightarrow> itac
      \<bar> "_\<^emph>pat" \<Rightarrow> itac
      \<bar> "pat\<^emph>_" \<Rightarrow> \<open>subst upred_sep_comm\<close>
      \<bar> "_\<^emph>pat\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm2R\<close>
      \<bar> "pat\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm2L; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm3M; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm3L; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm4_2; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm4_1; move_sepL pat\<close>
    \<close>

method apply_wand = (move_sepL "?P-\<^emph>?Q");
  match conclusion in \<open>hyps \<turnstile> goal\<close> for hyps goal \<Rightarrow>
    \<open> match (hyps) in "P\<^emph>(Q-\<^emph>R)" for P Q R \<Rightarrow> \<open>(move_sepL Q; 
      entails_substL rule: upred_sep_comm2R; entails_substL rule: upred_wand_apply)\<close> \<close>

method iFrame_simp = match conclusion in \<open>hyps \<turnstile> goal\<close> for hyps goal \<Rightarrow>
    \<open> match (goal) in "_\<^emph>P" for P \<Rightarrow> \<open>move_sepL P; rule upred_frame\<close> 
      \<bar> _ \<Rightarrow> \<open>rule upred_entails_refl | rule upred_weakeningL | rule upred_weakeningR\<close>\<close>
    
lemma test_lemma: "S \<^emph> P \<^emph> Q \<^emph> (P-\<^emph>R) \<^emph> (\<triangleright>R) -\<^emph> R \<^emph> (\<triangleright>R) \<^emph> Q"
apply iIntro
apply apply_wand
by iFrame_simp+
end