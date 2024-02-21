theory Atomic
imports Automation Invariant
begin

definition mono_pred :: "(('a::ofe \<Rightarrow> 'res::ucamera upred_f) \<Rightarrow> ('a \<Rightarrow> 'res upred_f)) \<Rightarrow> 'res upred_f"
  where "mono_pred F \<equiv> \<forall>\<^sub>u \<Phi> \<Psi>. (\<upharpoonleft>(non_expansive \<Phi>)) \<longrightarrow>\<^sub>u (\<upharpoonleft>(non_expansive \<Psi>)) \<longrightarrow>\<^sub>u 
  ((\<box>(\<forall>\<^sub>u x. \<Phi> x -\<^emph> \<Psi> x)) -\<^emph> (\<forall>\<^sub>u x. F \<Phi> x -\<^emph> F \<Psi> x))"

lemma mono_predE: "\<lbrakk>mono_pred F; non_expansive \<Phi>; non_expansive \<Psi>\<rbrakk> \<Longrightarrow> 
  (\<box>(\<forall>\<^sub>u x. \<Phi> x -\<^emph> \<Psi> x)) \<^emph> F \<Phi> x \<turnstile> F \<Psi> x"
proof -
assume assms: "mono_pred F" "non_expansive \<Phi>" "non_expansive \<Psi>"
then have "\<forall>\<^sub>u \<Phi> \<Psi>. (\<upharpoonleft>(non_expansive \<Phi>)) \<longrightarrow>\<^sub>u (\<upharpoonleft>(non_expansive \<Psi>)) \<longrightarrow>\<^sub>u 
  ((\<box>(\<forall>\<^sub>u x. \<Phi> x -\<^emph> \<Psi> x)) -\<^emph> (\<forall>\<^sub>u x. F \<Phi> x -\<^emph> F \<Psi> x))" by (simp add: mono_pred_def)
then have "\<forall>\<Phi> \<Psi>. upred_holds ((\<upharpoonleft>(non_expansive \<Phi>)) \<longrightarrow>\<^sub>u (\<upharpoonleft>(non_expansive \<Psi>)) \<longrightarrow>\<^sub>u 
  ((\<box>(\<forall>\<^sub>u x. \<Phi> x -\<^emph> \<Psi> x)) -\<^emph> (\<forall>\<^sub>u x. F \<Phi> x -\<^emph> F \<Psi> x)))"
  by (smt (verit, best) upred_forall_inst upred_holds_subst)
then have "\<forall>\<Phi> \<Psi>. non_expansive \<Phi> \<longrightarrow> non_expansive \<Psi> \<longrightarrow> 
  upred_holds (((\<box>(\<forall>\<^sub>u x. \<Phi> x -\<^emph> \<Psi> x)) -\<^emph> (\<forall>\<^sub>u x. F \<Phi> x -\<^emph> F \<Psi> x)))"
  by (smt (verit, best) entails_impl_true upred_holds_entails)
with assms(2-) have "upred_holds (((\<box>(\<forall>\<^sub>u x. \<Phi> x -\<^emph> \<Psi> x)) -\<^emph> (\<forall>\<^sub>u x. F \<Phi> x -\<^emph> F \<Psi> x)))" by blast
then show ?thesis by (meson upred_entails_trans upred_forall_inst upred_wandE upred_wand_holdsE)
qed
  
definition mono_ne :: "(('a::ofe \<Rightarrow> 'res::ucamera upred_f) \<Rightarrow> ('a \<Rightarrow> 'res upred_f)) \<Rightarrow> bool"
  where "mono_ne F \<equiv> \<forall>\<Phi>. non_expansive \<Phi> \<longrightarrow> non_expansive (F \<Phi>)"

lemma mono_neE: "\<lbrakk>mono_ne F; non_expansive \<Phi>\<rbrakk> \<Longrightarrow> non_expansive (F \<Phi>)" by (simp add: mono_ne_def)
  
definition greatest_fixpoint :: 
  "(('a::ofe \<Rightarrow> 'res::ucamera upred_f) \<Rightarrow> ('a \<Rightarrow> 'res upred_f)) \<Rightarrow> 'a \<Rightarrow> 'res upred_f"
  where
  "greatest_fixpoint F x = 
  (\<exists>\<^sub>u (\<Phi>::'a-n>'res upred_f). (\<box>(\<forall>\<^sub>u x. Rep_ne \<Phi> x -\<^emph> F (Rep_ne \<Phi>) x)) \<^emph> Rep_ne \<Phi> x)"

lemma gfp_ne_outer: "\<lbrakk>\<forall>\<Phi> x n. n_equiv n (F1 \<Phi> x) (F2 \<Phi> x); n_equiv n x1 x2\<rbrakk> \<Longrightarrow>
  n_equiv n (greatest_fixpoint F1 x1) (greatest_fixpoint F2 x2)"
  unfolding greatest_fixpoint_def
  apply (rule upred_ne_rule; (simp add: ofe_refl iris_simp)?)+
  using Rep_ne non_expansive_def by blast

lemma gfp_ne [upred_ne_rule]: "non_expansive (greatest_fixpoint F)"
  unfolding greatest_fixpoint_def
  apply (rule non_expansiveI)
  apply (rule upred_ne_rule; (simp add: ofe_refl iris_simp)?)+
  using Rep_ne non_expansive_def by blast

lemma gfp_unfold_l: "mono_pred F \<Longrightarrow> greatest_fixpoint F x \<turnstile> F (greatest_fixpoint F) x"
apply (subst greatest_fixpoint_def)
apply iExistsL
subgoal for \<Phi>
apply (entails_substR rule: mono_predE[of F "Rep_ne \<Phi>" "greatest_fixpoint F"])
apply (simp_all add: Rep_ne upred_ne_rule)
apply (check_moveL "\<box>?P")
apply dupl_pers
apply (check_moveL "Rep_ne \<Phi> x")
apply (rule upred_sep_mono[of _ _ "(\<box>(\<forall>\<^sub>ux. Rep_ne \<Phi> x -\<^emph> F (Rep_ne \<Phi>) x)) \<^emph> Rep_ne \<Phi> x", unfolded upred_sep_assoc_eq])
apply (rule upred_persisIR)
apply iForallR
apply iIntro
unfolding greatest_fixpoint_def apply (iExistsR \<Phi>)
apply (iApply rule: upred_persisE)
apply (iForallL x)
apply iApply_wand
by iFrame_single
done

lemma persis_split: "\<lbrakk>P\<turnstile>\<box>Q; P\<turnstile>R\<rbrakk> \<Longrightarrow> P\<turnstile>(\<box>Q)\<^emph>R"
by (metis persistent_keep persistent_persis upred_entails_trans upred_frame upred_sep_comm)

context 
  fixes F :: "('a::ofe \<Rightarrow> 'res::ucamera upred_f) \<Rightarrow> ('a \<Rightarrow> 'res upred_f)"
  assumes F_mono_pred: "mono_pred F" and F_mono_ne: "mono_ne F"
begin

lift_definition F_gfp :: "'a -n> 'res upred_f" is "F (greatest_fixpoint F)" 
  by (rule mono_neE[OF F_mono_ne gfp_ne])
  
lemma gfp_unfold_r: "F (greatest_fixpoint F) x \<turnstile> greatest_fixpoint F x"
apply (subst (1) greatest_fixpoint_def)
apply (iExistsR F_gfp)
apply (simp add: F_gfp.rep_eq)
apply (rule persis_split; iris_simp)
apply (entails_substR rule: upred_entail_eqL[OF pers_forall])
apply iForallR
apply (rule upred_entails_trans[OF upred_emp_entailed])
apply (rule persistent_persisI)
apply pers_solver
apply (iIntro, iris_simp)
apply (entails_substR rule: mono_predE[OF F_mono_pred, of "greatest_fixpoint F"])
apply (simp_all add: mono_neE[OF F_mono_ne gfp_ne] upred_ne_rule)
apply (check_moveR "\<box>?P")
apply (rule upred_sep_mono[OF upred_entails_refl persistent_persisI, OF persistent_pure[of True], unfolded iris_simp])
apply iForallR
apply (iIntro, iris_simp)
by (rule gfp_unfold_l[OF F_mono_pred])

lemma gfp_coiter: "non_expansive Q \<Longrightarrow>
  (\<box>(\<forall>\<^sub>u y. Q y -\<^emph> F Q y)) -\<^emph> (\<forall>\<^sub>u x. Q x -\<^emph> greatest_fixpoint F x)"
  apply iIntros
  apply (subst greatest_fixpoint_def)
  apply (iExistsR "Abs_ne  Q")
  by (auto simp: Abs_ne_inverse)
  
lemma gfp_paco: "\<lbrakk>non_expansive Q; mono_pred (\<lambda>P a. Q a \<or>\<^sub>u F P a)\<rbrakk> \<Longrightarrow>
  (\<box>(\<forall>\<^sub>u y. Q y -\<^emph> F (greatest_fixpoint (\<lambda>P a. Q a \<or>\<^sub>u F P a)) y)) -\<^emph> (\<forall>\<^sub>u x. Q x -\<^emph> greatest_fixpoint F x)"
  apply iIntros
  subgoal for x
  apply (check_moveL "\<box> ?P")
  apply (iApply rule: upred_persisE)
  apply (iForallL x)
  apply iApply_wand
  apply (entails_substR rule: gfp_unfold_r)
  apply (entails_substR rule: mono_predE[OF F_mono_pred, of "greatest_fixpoint (\<lambda>P a. Q a \<or>\<^sub>u F P a)"])
  apply (simp_all add: mono_neE[OF F_mono_ne gfp_ne] upred_ne_rule)
  apply iFrame_single
  apply iIntros
  subgoal for x
  apply (entails_substR rule: upred_entails_trans[OF _ upred_forall_inst, OF gfp_coiter[to_entailment],
    to_entailment, of "greatest_fixpoint (\<lambda>P a. Q a \<or>\<^sub>u F P a)"])
  apply (simp_all add: mono_neE[OF F_mono_ne gfp_ne] upred_ne_rule)
  apply iFrame_single
  apply iIntros
  apply (iApply rule: gfp_unfold_l)
  subgoal for y
  apply (rule upred_disjE')
  apply (iApply rule: upred_persisE)
  apply (iForallL y)
  apply iApply_wand
  by iFrame_single+
  done done done
end

lemma gfp_unfold: "\<lbrakk>mono_pred F; mono_ne F\<rbrakk> \<Longrightarrow> greatest_fixpoint F x \<stileturn>\<turnstile> F (greatest_fixpoint F) x"
  by (auto simp: upred_entail_eq_def intro: gfp_unfold_l gfp_unfold_r)

lemma gfp_strong_mono: "\<lbrakk>mono_pred F; mono_ne F; mono_pred G; mono_ne G\<rbrakk> \<Longrightarrow>
  (\<box>(\<forall>\<^sub>u Q x. F Q x -\<^emph> G Q x)) -\<^emph> (\<forall>\<^sub>u x. greatest_fixpoint F x -\<^emph> greatest_fixpoint G x)"
  apply iIntro
  apply (entails_substR rule: gfp_coiter)
  apply (simp_all add: mono_neE[OF _ gfp_ne] upred_ne_rule)
  apply iIntros
  subgoal for y
  apply (iApply rule: gfp_unfold_l)
  apply (iApply rule: upred_persisE)
  apply (iForallL "greatest_fixpoint F")
  apply (iForallL y)
  apply iApply_wand
  by iFrame_single done
  
lemma gfp_coind: "\<lbrakk>non_expansive Q; mono_pred (\<lambda>P a. Q a \<or>\<^sub>u F P a); mono_ne F;
  mono_pred F; mono_ne (\<lambda>P a. Q a \<or>\<^sub>u F P a)\<rbrakk> \<Longrightarrow>
  (\<box>(\<forall>\<^sub>u y. Q y -\<^emph> F (\<lambda>a. Q a \<or>\<^sub>u greatest_fixpoint F a) y)) -\<^emph> (\<forall>\<^sub>u x. Q x -\<^emph> greatest_fixpoint F x)"
  apply iIntro
  apply (entails_substR rule: gfp_paco)
  apply (simp_all add: mono_neE[OF _ gfp_ne] upred_ne_rule)
  apply iIntros
  subgoal for y
  apply (iApply rule: upred_persisE)
  apply (iDrop "\<box>?P")
  apply (iForallL y)
  apply iApply_wand
  apply (entails_substR rule: mono_predE[of F "(\<lambda>a. Q a \<or>\<^sub>u greatest_fixpoint F a)"])
  apply (simp_all add: mono_neE[OF _ gfp_ne] upred_ne_rule)
  apply iFrame_single
  prefer 2
  subgoal by (auto simp: non_expansive_def gfp_ne[unfolded non_expansive_def] intro!: upred_ne_rule)
  apply iIntros
  apply (rule upred_disjE)
  apply (entails_substR rule: gfp_unfold_r)
  apply (simp_all add: mono_neE[OF _ gfp_ne] upred_ne_rule)
  apply (rule upred_disjIL, iris_simp)
  apply (entails_substR rule: upred_entails_trans[OF _ upred_forall_inst, OF gfp_strong_mono[to_entailment],
    to_entailment])
  apply (simp_all add: mono_neE[OF _ gfp_ne] upred_ne_rule)
  apply iFrame_single
  apply iIntros
  by (simp add: upred_disjIR) done
  
context 
fixes get_inv :: "gname \<Rightarrow> 'res::ucamera \<Rightarrow> inv option"
  and put_inv
assumes inv_inG: "inG get_inv put_inv"
begin
abbreviation fancy_upd' ("\<Turnstile>{_,_}=>_") where "fancy_upd' \<equiv> fancy_upd put_inv"
abbreviation wand_fupd' ("_={_,_}=\<^emph>_") where "wand_fupd' \<equiv> wand_fupd put_inv"
abbreviation wand_linear_fupd' ("_={_}=\<^emph>_") where "wand_linear_fupd' \<equiv> wand_linear_fupd put_inv"
abbreviation inv where "inv \<equiv> Invariant.inv put_inv"

definition atomic_acc :: "mask \<Rightarrow> mask \<Rightarrow> ('x \<Rightarrow> 'res upred_f) \<Rightarrow> 'res upred_f \<Rightarrow> 
  ('x \<Rightarrow> 'y \<Rightarrow> 'res upred_f) \<Rightarrow> ('x \<Rightarrow> 'y \<Rightarrow> 'res upred_f) \<Rightarrow> 'res upred_f" where
  "atomic_acc \<E>\<^sub>o \<E>\<^sub>i a P b \<Phi> = 
    \<Turnstile>{\<E>\<^sub>o, \<E>\<^sub>i}=> (\<exists>\<^sub>u x. a x \<^emph> (((a x) ={\<E>\<^sub>i,\<E>\<^sub>o}=\<^emph> P) \<and>\<^sub>u (\<forall>\<^sub>u y. ((b x y) ={\<E>\<^sub>i, \<E>\<^sub>o}=\<^emph> (\<Phi> x y)))))"

abbreviation atomic_update_pre :: "mask \<Rightarrow> mask \<Rightarrow> ('x \<Rightarrow> 'res upred_f) \<Rightarrow> ('x \<Rightarrow> 'y \<Rightarrow> 'res upred_f)
  \<Rightarrow> ('x \<Rightarrow> 'y \<Rightarrow> 'res upred_f) \<Rightarrow> (unit \<Rightarrow> 'res upred_f) \<Rightarrow> unit \<Rightarrow> 'res upred_f" where
"atomic_update_pre \<E>\<^sub>o \<E>\<^sub>i a b \<Phi> \<Psi> _ \<equiv> atomic_acc \<E>\<^sub>o \<E>\<^sub>i a (\<Psi> ()) b \<Phi>"

definition "atomic_update \<E>\<^sub>o \<E>\<^sub>i a b \<Phi> \<equiv> greatest_fixpoint (atomic_update_pre \<E>\<^sub>o \<E>\<^sub>i a b \<Phi>) ()"

lemma atomic_acc_ne: "non_expansive (atomic_acc \<E>\<^sub>o \<E>\<^sub>i)"
apply (rule non_expansiveI)
apply (auto simp: atomic_acc_def n_equiv_fun_def)
by (rule upred_ne_rule;(auto simp: ofe_refl intro: inv_inG)?)+

lemma atomic_update_ne: "non_expansive (atomic_update \<E>\<^sub>o \<E>\<^sub>i)"
apply (auto simp: non_expansive_def atomic_update_def n_equiv_fun_def greatest_fixpoint_def)
apply ((rule upred_ne_rule); (simp add: ofe_refl n_equiv_fun_def)?)+
using non_expansiveE[OF atomic_acc_ne, unfolded n_equiv_fun_def] by blast

lemma atomic_acc_wand: "((P1 -\<^emph> P2) \<and>\<^sub>u (\<forall>\<^sub>u x y. \<Phi>1 x y -\<^emph> \<Phi>2 x y)) -\<^emph>
  (atomic_acc \<E>\<^sub>o \<E>\<^sub>i a P1 b \<Phi>1 -\<^emph> atomic_acc \<E>\<^sub>o \<E>\<^sub>i a P2 b \<Phi>2)"
  apply iIntro
  unfolding atomic_acc_def
  apply (rule fupd_frame_mono[OF inv_inG])
  apply iExistsL
  subgoal for x
  apply (iExistsR x)
  apply (check_moveR "a x")
  apply iFrame_single
  apply (rule upred_entails_conjI)
  subgoal
    apply iIntro
    apply (iApply rule: upred_weakeningL')
    apply iApply_wand
    using fupd_frame_mono[OF inv_inG] upred_wandE upred_weakeningL' by blast
  apply (iApply rule: upred_weakeningR')
  apply (rule upred_forallI)
  subgoal for y
  apply (iForallL y)
  apply iIntro
  apply iApply_wand
  apply (iApply rule: upred_weakeningR')
  apply (iApply rule: fupd_frame_mono[OF inv_inG])
  apply (iForallL x) apply (iForallL y)
  by iApply_wand
done done

lemma atomic_update_unfold: "atomic_update \<E>\<^sub>o \<E>\<^sub>i a b \<Phi> 
  \<stileturn>\<turnstile> atomic_acc \<E>\<^sub>o \<E>\<^sub>i a (atomic_update \<E>\<^sub>o \<E>\<^sub>i a b \<Phi>) b \<Phi>"
  unfolding atomic_update_def
  apply (rule gfp_unfold)
  apply (simp_all add: mono_pred_def mono_ne_def)
  apply iIntro
  subgoal
    apply iForallR+
    apply (rule upred_implI_pure)+
    apply (iIntro, iris_simp)
    subgoal for P1 P2
    apply (entails_substR rule: atomic_acc_wand[of "P1 ()" "P2 ()" \<Phi>])
    apply iFrame_single
    by (simp add: upred_persisE) done
  by (auto simp: d_equiv non_expansive_def ofe_refl)

lemma atomic_acc_mono_pred: "mono_pred (atomic_update_pre \<E>\<^sub>o \<E>\<^sub>i a b \<Phi>)"
unfolding mono_pred_def
apply iIntros
apply (entails_substR rule: atomic_acc_wand)
apply iFrame_single
apply (iApply rule: upred_persisE)
by iFrame_single

lemma atomic_acc_mono_ne: "mono_ne (atomic_update_pre \<E>\<^sub>o \<E>\<^sub>i a b \<Phi>)"
by (simp add: non_expansiveI ofe_refl mono_ne_def atomic_acc_ne)

lemma atomic_acc_mask_weaken: "\<E>\<^sub>o1 \<subseteq> \<E>\<^sub>o2 \<Longrightarrow> atomic_acc \<E>\<^sub>o1 \<E>\<^sub>i a P b \<Phi> -\<^emph> atomic_acc \<E>\<^sub>o2 \<E>\<^sub>i a P b \<Phi>"
apply iIntro
apply (subst (2) atomic_acc_def)
apply (rule add_holds[OF fupd_mask_subseteq[OF inv_inG, of \<E>\<^sub>o1]], assumption)
apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])
apply (subst atomic_acc_def)
apply (check_moveL "\<Turnstile>{\<E>\<^sub>o1,\<E>\<^sub>i}=> ?P")
apply (rule fupd_frame_mono[OF inv_inG])
apply iExistsL
subgoal for x
apply (iExistsR x)
apply (check_moveR "a x")
apply iFrame_single
apply (rule upred_entails_conjI)
apply (iApply rule: upred_weakeningL')
apply iIntro
apply iApply_wand
apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])
apply (entails_substL rule: fupd_frame_l[OF inv_inG], iris_simp)
apply (iApply rule: upred_weakeningR')
apply iIntros
subgoal for y
apply (iForallL y)
apply iApply_wand
apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])
by (entails_substL rule: fupd_frame_l[OF inv_inG], iris_simp) done done
  
lemma atomic_update_mask_weaken: "\<E>\<^sub>o1 \<subseteq> \<E>\<^sub>o2 \<Longrightarrow> atomic_update \<E>\<^sub>o1 \<E>\<^sub>i a b \<Phi> -\<^emph> atomic_update \<E>\<^sub>o2 \<E>\<^sub>i a b \<Phi>"
  apply (subst (2) atomic_update_def)
  apply iIntro
  apply (entails_substR rule: upred_entails_trans[OF _ upred_forall_inst,
    OF gfp_coiter[where?Q="\<lambda>_. atomic_update \<E>\<^sub>o1 \<E>\<^sub>i a b \<Phi>",to_entailment], to_entailment])
  subgoal
    apply iFrame_single
    apply iIntros
    apply (iApply rule: upred_entail_eqL[OF atomic_update_unfold])
    by (iApply rule: atomic_acc_mask_weaken)
  subgoal by (rule atomic_acc_mono_pred)
  subgoal by (rule atomic_acc_mono_ne)
  by (simp add: non_expansive_def ofe_refl)
  
lemma elim_modal_acc: "(\<And>Q. elim_modal P P' (\<Turnstile>{Eo,Ei}=> Q) (\<Turnstile>{Eo,Ei}=> Q)) \<Longrightarrow>
  elim_modal P P' (atomic_acc Eo Ei a Pas b \<Phi>) (atomic_acc Eo Ei a Pas b \<Phi>)"
  by (auto simp: atomic_acc_def)

lemma elim_acc_atomic_acc: "elim_acc (fancy_upd' E1 E2) (fancy_upd' E2 E1) a' b' c' 
  (atomic_acc E1 Ei a Pas b Q) 
  (\<lambda>x'. atomic_acc E2 Ei a (b' x' \<^emph> (case c' x' of Some c \<Rightarrow> c -\<^emph> Pas | None \<Rightarrow> Pas)) b 
    (\<lambda>x y. b' x' \<^emph> (case c' x' of Some c \<Rightarrow> c -\<^emph> Q x y | None \<Rightarrow> Q x y)))"
  unfolding elim_acc_def accessor_def atomic_acc_def
  apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])
  apply iExistsL subgoal for x'
  apply (check_moveL "upred_forall (?P::'a \<Rightarrow> 'res upred_f)")
  apply (iForallL x')
  apply iApply_wand
  apply (rule fupd_frame_mono[OF inv_inG])
  apply iExistsL subgoal for x
  apply (iExistsR x)
  apply (check_moveR "a x")
  apply iFrame_single
  apply (rule upred_entails_conjI)
  subgoal
    apply iIntro
    apply (iApply rule: upred_weakeningL')
    apply iApply_wand
    apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])
    apply iApply_wand
    apply (rule fupd_frame_mono[OF inv_inG])
    apply (cases "c' x'"; iris_simp) by iApply_wand
  apply iIntros subgoal for y
  apply (iApply rule: upred_weakeningR')
  apply (iForallL y)
  apply iApply_wand
  apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])
  apply iApply_wand
  apply (rule fupd_frame_mono[OF inv_inG])
  apply (cases "c' x'"; iris_simp) by iApply_wand
done done done

lemma open_inv_atomic_acc: "\<lbrakk>names N \<subseteq> E1; (\<triangleright>P) \<turnstile> atomic_acc (E1 - names N) Ei a (Pas \<^emph> \<triangleright>P) b (\<lambda>x y. Q x y \<^emph> \<triangleright>P)\<rbrakk>
  \<Longrightarrow> inv N P \<turnstile> atomic_acc E1 Ei a Pas b Q"
  apply (rule elim_inv_applied[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] elim_acc_atomic_acc], simplified, unfolded iris_simp])
  by (simp add: upred_sep_comm)+

lemma open_inv_atomic_acc': "\<lbrakk>names N \<subseteq> E1; (R \<^emph> \<triangleright>P) \<turnstile> atomic_acc (E1 - names N) Ei a (Pas \<^emph> \<triangleright>P) b (\<lambda>x y. Q x y \<^emph> \<triangleright>P)\<rbrakk>
  \<Longrightarrow> R \<^emph> inv N P \<turnstile> atomic_acc E1 Ei a Pas b Q"
  apply (rule elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] elim_acc_atomic_acc], simplified, unfolded iris_simp])
  by (simp add: upred_sep_comm)+

lemma aacc_intro: "Ei \<subseteq> Eo \<Longrightarrow>
  \<forall>\<^sub>u x. a x -\<^emph> (((a x) ={Eo}=\<^emph> P) \<and>\<^sub>u (\<forall>\<^sub>u y. ((b x y) ={Eo}=\<^emph> (Q x y)))) -\<^emph> atomic_acc Eo Ei a P b Q"
  unfolding atomic_acc_def
  apply iIntros subgoal for x
  apply (entails_substR rule: fupd_mask_intro[OF inv_inG], simp_all)
  apply iIntros
  apply (iExistsR x)
  apply (check_moveR "a x") apply iFrame_single
  apply (rule upred_entails_conjI)
  subgoal apply iIntro apply (iApply rule: upred_weakeningL') apply iApply_wand
    using frameE frameI fupd_frame_refl' inv_inG upred_weakeningR by blast
  apply iIntros subgoal for y apply (iApply rule: upred_weakeningR') apply (iForallL y) apply iApply_wand
    using frameE frameI fupd_frame_refl' inv_inG upred_weakeningR by blast
  done done

lemma aupd_intro: "\<lbrakk>persistent P; P\<and>\<^sub>uQ\<turnstile>atomic_acc Eo Ei a Q b \<Phi>\<rbrakk> \<Longrightarrow> P\<and>\<^sub>uQ\<turnstile>atomic_update Eo Ei a b \<Phi>"
  apply (subst atomic_update_def)
  apply (rule persis_conj_sepL, simp)
  apply (entails_substR rule: upred_entails_trans[OF _ upred_forall_inst, 
      OF gfp_coiter[where ?Q="\<lambda>_. Q", to_entailment], to_entailment])
  subgoal
    apply iIntro
    apply (rule upred_sep_mono, simp_all)
    apply (rule persistent_persisI, simp)
    apply iIntros
    apply (rule upred_entails_trans[of _ "P \<and>\<^sub>u Q" "atomic_acc Eo Ei a Q b \<Phi>"], simp_all)
    by (simp add: upred_entails_conj_sep)
  using atomic_acc_mono_pred atomic_acc_mono_ne apply blast+
  by (auto simp: ofe_refl non_expansive_def)

lemma aupd_intro': "\<lbrakk>persistent P; P\<^emph>Q\<turnstile>atomic_acc Eo Ei a Q b \<Phi>\<rbrakk> \<Longrightarrow> P\<^emph>Q\<turnstile>atomic_update Eo Ei a b \<Phi>"
using aupd_intro persis_conj_sepL upred_entails_conj_sep upred_entails_trans by blast
  
lemma aacc_aacc: "E1' \<subseteq> E1 \<Longrightarrow>
  atomic_acc E1' E2 a P b Q -\<^emph> (\<forall>\<^sub>u x::'x. a x -\<^emph> (atomic_acc E2 E3 a' (a x \<^emph> (P ={E1}=\<^emph> P')) b'
  (\<lambda>x' y'. (a x \<^emph> (P={E1}=\<^emph> (Q' x' y'))) \<or>\<^sub>u (\<exists>\<^sub>u y::'y. b x y \<^emph> ((Q x y) ={E1}=\<^emph> (Q' x' y')))))) -\<^emph>
  atomic_acc E1 E3 a' P' b' Q'"
  apply iIntros
  apply (iApply rule: atomic_acc_mask_weaken)
  apply (subst (2) atomic_acc_def) apply (subst (2) atomic_acc_def)
  apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])
  apply iExistsL subgoal for x
  apply (check_moveL "upred_forall (?P::'x \<Rightarrow> 'res upred_f)") apply (iForallL x)
  apply (subst atomic_acc_def)
  apply iApply_wand
  apply (rule fupd_frame_mono[OF inv_inG])
  apply iExistsL subgoal for x'
  apply (iExistsR x')
  apply (check_moveR "a' x'") apply iFrame_single
  apply (rule upred_entails_conjI)
  subgoal
    apply iIntro
    apply (iApply rule: upred_weakeningL')
    apply iApply_wand
    apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]], iris_simp)
    apply (iApply rule: upred_weakeningL')
    apply iApply_wand
    apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])
    by iApply_wand
  apply iIntros subgoal for y
  apply (iApply rule: upred_weakeningR')
  apply (iForallL y)
  apply iApply_wand
  apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])
  apply (rule upred_disjE'; iris_simp)
  subgoal
    apply (iApply rule: upred_weakeningL')
    apply iApply_wand
    apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])
    by iApply_wand
  apply (iApply rule: upred_weakeningR')
  apply iExistsL subgoal for y'
  apply (check_moveL "upred_forall (?P::'y \<Rightarrow> 'res upred_f)") apply (iForallL y')
  apply iApply_wand
  apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])
  by iApply_wand done done done done
  
lemma aacc_aupd: "E1' \<subseteq> E1 \<Longrightarrow>
  atomic_update E1' E2 a b Q -\<^emph> 
  (\<forall>\<^sub>u x::'x. a x -\<^emph> (atomic_acc E2 E3 a' (a x \<^emph> (atomic_update E1' E2 a b Q ={E1}=\<^emph> P')) b'
    (\<lambda>x' y'. (a x \<^emph> (atomic_update E1' E2 a b Q ={E1}=\<^emph> (Q' x' y'))) 
      \<or>\<^sub>u (\<exists>\<^sub>u y::'y. b x y \<^emph> ((Q x y) ={E1}=\<^emph> (Q' x' y')))))) -\<^emph>
  atomic_acc E1 E3 a' P' b' Q'"
  apply iIntros
  apply (entails_substR rule: aacc_aacc[to_entailment, of E1' E1 E2 a "atomic_update E1' E2 a b Q" b Q E3 a' P' b' Q'])
  apply iFrame_single
  by (iApply rule: upred_entail_eqL[OF atomic_update_unfold])
end
end