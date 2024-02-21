theory Own
imports ProofRules
begin

definition pred_infinite :: "('b \<Rightarrow> bool) \<Rightarrow> bool" where 
  "pred_infinite P \<equiv> \<forall>xs::'b list. \<exists>x. P x \<and> x \<notin> set xs"

context inG begin
definition own :: "gname \<Rightarrow> 'b \<Rightarrow> 'a upred_f" where
  "own \<gamma> x = upred_own (return_cmra \<gamma> x)"

lemma own_ne [upred_ne_rule]: "n_equiv n x y \<Longrightarrow> n_equiv n (own \<gamma> x) (own \<gamma> y)" 
  unfolding own_def
  apply (rule upred_own_ne)
  using return_ne by simp

lemma own_valid: "own \<gamma> a \<turnstile> \<V>(a)"
  unfolding own_def
  apply (rule upred_entails_trans[OF upred_own_valid])
  by (auto simp: upred_entails.rep_eq upred_valid.rep_eq return_n_valid)

lemma own_valid': "own \<gamma> a \<turnstile> \<V>(return_cmra \<gamma> a)"
  by (simp add: own_def upred_own_valid)

lemma valid_get: "\<V>(return_cmra \<gamma> a) \<stileturn>\<turnstile> \<V>(a)"
  by (auto simp: upred_valid.rep_eq upred_entail_eq_def upred_entails.rep_eq return_n_valid)

lemma own_op: "own \<gamma> (a\<cdot>b) \<stileturn>\<turnstile> own \<gamma> a \<^emph> own \<gamma> b"
  unfolding own_def return_op
  by (rule upred_own_op)

lemma own_valid2: "own \<gamma> a1 -\<^emph> own \<gamma> a2 -\<^emph> \<V>(a1\<cdot>a2)"
  unfolding own_def
  apply (rule upred_wand_holds2I)
  apply (rule upred_entails_trans[OF upred_wand_holds2E[OF upred_own_valid2]])
  by (auto simp: upred_entails.rep_eq upred_valid.rep_eq return_n_valid return_op[symmetric])
  
lemma own_alloc: "valid a \<Longrightarrow> \<Rrightarrow>\<^sub>b (own \<gamma> a)"
  sorry (* Axiomatized as proof in Coq is not easily reproducible. *)

lemma own_alloc_strong: "pred_infinite P \<Longrightarrow> valid a \<Longrightarrow> \<Rrightarrow>\<^sub>b (\<exists>\<^sub>u\<gamma>. ((\<upharpoonleft>(P \<gamma>)) \<^emph> own \<gamma> a))"
sorry

lemma own_update: "return_cmra \<gamma> a\<leadsto>return_cmra \<gamma> b \<Longrightarrow> own \<gamma> a ==\<^emph> own \<gamma> b"
  unfolding camera_upd_def own_def opM_def
  apply (rule upred_wand_holdsI)
  apply transfer'
  apply (auto split: option.splits)
  by (metis n_incl_refl n_valid_incl_subst)

lemma add_own: "\<lbrakk>valid a; Q\<^emph>(own \<gamma> a)\<turnstile>\<Rrightarrow>\<^sub>bR\<rbrakk> \<Longrightarrow> Q\<turnstile>\<Rrightarrow>\<^sub>bR"
proof -
  assume assms: "valid a" "Q\<^emph>(own \<gamma> a)\<turnstile>\<Rrightarrow>\<^sub>bR"
  from own_alloc[OF this(1)] have "\<Rrightarrow>\<^sub>b own \<gamma> a" .
  from assms(2) have "Q\<^emph>\<Rrightarrow>\<^sub>b own \<gamma> a\<turnstile>\<Rrightarrow>\<^sub>b R"
    by (meson upd_frameR upd_mono upd_idem upred_entails_trans)
  from add_holds[OF \<open>\<Rrightarrow>\<^sub>b own \<gamma> a\<close> this] show ?thesis .
qed  

lemma inG_dcamera_val: "dcamera_val (return_cmra \<gamma> a) \<Longrightarrow> dcamera_val a"
  unfolding dcamera_val_def discrete_val_def
  using return_ne
  apply (auto simp: ofe_refl ofe_eq_eq valid_def)
  apply (metis return_get option.inject)
  apply (metis return_get ofe_eq_equiv option.sel)
  using return_n_valid apply blast
  apply (metis return_get option.sel)
  apply (metis return_get ofe_limit option.sel)
  using return_n_valid by blast
end

lemma put_update: "\<lbrakk>inG get_cmra put_cmra; (a::'b::ucamera) \<leadsto> b\<rbrakk> \<Longrightarrow> 
  (inG.return_cmra put_cmra \<gamma> a::'a::ucamera) \<leadsto> inG.return_cmra put_cmra \<gamma> b"
proof (subst total_update, auto)
define return_cmra where "return_cmra \<equiv> inG.return_cmra put_cmra"
fix n x
assume assms:"inG get_cmra put_cmra"  "a \<leadsto> b" "n_valid (return_cmra \<gamma> a \<cdot> x) n"
then have 0:"n_valid x n" by (auto simp: camera_comm intro: camera_valid_op)
from assms(3) have "get_cmra \<gamma> x = Some y \<Longrightarrow> n_valid (a \<cdot> y) n" for y
  by (metis (no_types, lifting) \<epsilon>_n_valid assms(1) inG.put_n_valid2 inG.return_cmra_def 
    inG.return_n_valid inG.return_op return_cmra_def  inG.get_n_valid inG.get_op inG.return_get[OF assms(1)])
with assms(2) have 1:"get_cmra \<gamma> x = Some y \<Longrightarrow> n_valid (b \<cdot> y) n" for y by (simp add: total_update)
from inG.get_valid_op2[OF assms(1)] 0 1 have 2: 
  "get_cmra \<gamma> x = Some y \<Longrightarrow> n_valid (return_cmra \<gamma> b \<cdot> x) n" for y 
  by (auto simp: valid_raw_option_def op_option_def return_cmra_def)
show "n_valid (inG.return_cmra put_cmra \<gamma> b \<cdot> x) n" proof (cases "get_cmra \<gamma> x")
  case None
  from inG.get_none_op[OF assms(1) this] have "get_cmra \<gamma> (return_cmra \<gamma> b \<cdot> x) = Some b" 
    by (metis camera_comm inG.return_get[OF assms(1)] return_cmra_def)
  with inG.get_n_valid[OF assms(1)] have *:"n_valid (return_cmra \<gamma> b \<cdot> x) n \<Longrightarrow> n_valid b n" 
    by (metis assms(1) camera_valid_op inG.return_n_valid return_cmra_def)
  from assms(3) have "n_valid a n" using camera_valid_op inG.return_n_valid[OF assms(1)] 
    return_cmra_def by blast
  then have "n_valid (a \<cdot> \<epsilon>) n" by (simp add: \<epsilon>_right_id)
  with assms(2) have **:"n_valid b n" by (auto simp: total_update intro:camera_valid_op)
  with inG.get_valid_op2[OF assms(1) None 0] show ?thesis by (auto simp: op_option_def valid_raw_option_def) 
next
  case (Some a)
  from 2[OF this, unfolded return_cmra_def] show ?thesis .
qed
qed

lemma put_update': "\<lbrakk>\<forall>(x::'a::camera). valid x; inG get_cmra put_cmra\<rbrakk> \<Longrightarrow> 
  inG.return_cmra put_cmra \<gamma> (x::'a) \<leadsto> inG.return_cmra put_cmra \<gamma> b"
proof (auto simp: camera_upd_def opM_def split: option.splits)
fix n
assume assms: "All (camera_class.valid :: 'a \<Rightarrow> bool)" "inG get_cmra put_cmra"
from inG.return_n_valid[OF assms(2)] have "n_valid (inG.return_cmra put_cmra \<gamma> b) n \<longleftrightarrow> n_valid b n" by simp
with assms(1)[unfolded valid_def] show "n_valid (inG.return_cmra put_cmra \<gamma> b) n" by simp
next
fix n y
assume assms: "All (camera_class.valid :: 'a \<Rightarrow> bool)" "inG get_cmra put_cmra" 
  "n_valid (inG.return_cmra put_cmra \<gamma> x \<cdot> y) n"
from camera_valid_op this(3) camera_comm have 1: "n_valid y n" by metis
from assms(1)[unfolded valid_def] have 2: "n_valid b n" by simp
from assms(1)[unfolded valid_def] have 3: "n_valid (b \<cdot> a) n" for a by simp
show "n_valid (inG.return_cmra put_cmra \<gamma> b \<cdot> y) n" proof (cases "get_cmra \<gamma> y")
case None
from inG.get_valid_op2[OF assms(2) this 1] 2 show ?thesis 
  by (auto simp: op_option_def valid_raw_option_def)
next
case (Some a)
from inG.get_valid_op2[OF assms(2) this 1] 3 show ?thesis 
  by (auto simp: op_option_def valid_raw_option_def)
qed
qed

notation inG.own ("own _ _ _")

context fixes get_cmra :: "gname \<Rightarrow> 'a::ucamera \<Rightarrow> 'b::total_camera option"
  and upd_cmra :: "gname \<Rightarrow> 'b option upd \<Rightarrow> 'a upd"
  assumes inG: "inG get_cmra upd_cmra"
begin
lemma own_core_persis: "own upd_cmra \<gamma> a \<turnstile> \<box>(own upd_cmra \<gamma> (core a))"
  unfolding inG.own_def[OF inG]
  apply (rule upred_entails_trans[OF upred_own_core_persis])
  unfolding core_def
  apply (auto simp: comp_def inG.return_pcore[OF inG])
  using total_pcore
  by (metis option.case_eq_if option.distinct(1) upred_entails_refl)

lemma pcore_id_put: "pcore_id_pred x \<Longrightarrow> pcore_id_pred (inG.return_cmra upd_cmra \<gamma> x)"
  unfolding pcore_id_pred_def inG.return_pcore[OF inG]
  by auto
end
end