theory View
imports DerivedConstructions Frac
begin
subsection \<open>View camera\<close>
text \<open>A camera combinator similar to \<^typ>\<open>'m auth\<close>\<close>

datatype 'a view = 
  View (view_auth_proj: "((dfrac\<times>'a ag)) option") (view_frag_proj: 'a)

definition view_auth :: "dfrac \<Rightarrow> 'a \<Rightarrow> 'a::ucamera view" ("\<Zspot>A{_} _") where
  "view_auth dq a = View (Some (dq, to_ag a)) \<epsilon>"
definition view_frag :: "'a::ucamera \<Rightarrow> 'a view" ("\<circle>A _") where 
  "view_frag b = View None b"
  
abbreviation view_auth_disc :: "'a \<Rightarrow> 'a::ucamera view" ("\<Zspot>A\<box> _") where 
  "view_auth_disc a \<equiv> \<Zspot>A{DfracDiscarded} a"
abbreviation view_auth_full :: "'a \<Rightarrow> 'a::ucamera view" ("\<Zspot>A _") where
  "view_auth_full a \<equiv> \<Zspot>A{DfracOwn 1} a"

abbreviation view_auth_frac :: "frac \<Rightarrow> 'a \<Rightarrow> 'a::ucamera view" ("\<Zspot>A{#_} _") where
  "view_auth_frac f a \<equiv> \<Zspot>A{DfracOwn f} a"
  
instantiation view :: (ofe) ofe begin
definition n_equiv_view :: "nat \<Rightarrow> 'a view \<Rightarrow> 'a view \<Rightarrow> bool" where
  "n_equiv_view n v1 v2 \<equiv> n_equiv n (view_auth_proj v1) (view_auth_proj v2) 
    \<and> n_equiv n (view_frag_proj v1) (view_frag_proj v2)"
definition ofe_eq_view :: "'a view \<Rightarrow> 'a view \<Rightarrow> bool" where
  "ofe_eq_view v1 v2 \<equiv> ofe_eq (view_auth_proj v1) (view_auth_proj v2) 
    \<and> ofe_eq (view_frag_proj v1) (view_frag_proj v2)"
instance proof (standard)
fix n and x y z :: "'a view"
show "n_equiv n x y \<Longrightarrow> n_equiv n y z \<Longrightarrow> n_equiv n x z"
  unfolding view_auth_proj_def view_frag_proj_def n_equiv_view_def ofe_eq_view_def
  apply (cases x; cases y; cases z)
  apply simp
  using ofe_trans by metis
qed (auto simp: view_auth_proj_def n_equiv_view_def ofe_eq_view_def
  ofe_refl ofe_mono ofe_sym ofe_limit intro: ofe_trans split: view.splits)
end

instance view :: (discrete) discrete 
  by standard (auto simp: view_auth_proj_def n_equiv_view_def ofe_eq_view_def 
    d_equiv d_eq split: view.splits)

definition view_rel :: "nat \<Rightarrow> 'a::ucamera \<Rightarrow> 'a \<Rightarrow> bool" where 
  "view_rel n a b \<equiv> n_incl n b a \<and> n_valid a n"
  
lemma view_rel_mono: 
  assumes "view_rel n1 a1 b1" "n_equiv n2 a1 a2" "n_incl n2 b2 b1" "n2 \<le> n1"
  shows "view_rel n2 a2 b2"
proof -
  from assms(1) have rel1: "n_incl n1 b1 a1 \<and> n_valid a1 n1" by (simp add: view_rel_def)
  with assms(4) have "n_incl n2 b1 a1" using camera_n_incl_le by auto
  with assms(3) have "n_incl n2 b2 a1"
    by (smt (verit, ccfv_SIG) camera_assoc dual_order.refl n_incl_def op_equiv_subst)
  with assms(2) have "n_incl n2 b2 a2" by (meson n_incl_def ofe_trans_eqL)
  moreover from assms(2,4) rel1 have "n_valid a2 n2"
    by (simp add: ne_sprop_weaken valid_raw_non_expansive)   
  ultimately show ?thesis by (simp add: view_rel_def)
qed

lemma view_rel_n_valid: "view_rel n a b \<Longrightarrow> n_valid b n" apply (simp add: view_rel_def)
  using camera_props(6) n_incl_def n_valid_ne by blast

lemma view_rel_unit: "\<exists>a. view_rel n a \<epsilon>"
proof -
have "view_rel n \<epsilon> \<epsilon>" by (auto simp: view_rel_def \<epsilon>_n_valid)
then show ?thesis by blast
qed

lemma auth_view_rel_unit: "view_rel n a \<epsilon> \<longleftrightarrow> n_valid a n"
  by (simp add: view_rel_def)

lemma auth_view_rel_exists: "(\<exists>a. view_rel n a b) \<longleftrightarrow> n_valid b n"
  apply (auto simp add: view_rel_def)
  using view_rel_def view_rel_n_valid apply blast
  using n_incl_refl by blast

lemma view_rel_ne: "\<lbrakk>n_equiv n m1 m2; n_equiv n f1 f2\<rbrakk> \<Longrightarrow> view_rel n m1 f1 \<longleftrightarrow> view_rel n m2 f2"
  apply (rule iffI)
  using view_rel_mono[of n m1 f1 n m2 f2] apply (simp add: ofe_sym total_n_inclI)
  using view_rel_mono[of n m2 f2 n m1 f1] by (simp add: ofe_sym total_n_inclI)
  
lemma auth_view_rel_discrete: "view_rel 0 a (b::'a::ducamera) \<Longrightarrow> view_rel n a b"
apply (auto simp: view_rel_def n_incl_def d_equiv) using d_valid[unfolded valid_def] by blast

instantiation view :: (ucamera) camera begin
lift_definition valid_raw_view :: "'a view \<Rightarrow> sprop" is "\<lambda>x n. case view_auth_proj x of 
    Some (dq,ag) \<Rightarrow> n_valid dq n \<and> (\<exists>a. n_equiv n ag (to_ag a) \<and> view_rel n a (view_frag_proj x))
  | None \<Rightarrow> \<exists>a. view_rel n a (view_frag_proj x)" 
  apply (simp add: view_auth_proj_def view_frag_proj_def split: option.splits view.splits)
  apply (meson view_rel_mono ofe_refl total_n_inclI)
  by (smt (verit) case_prod_conv dcamera_valid_iff view_rel_mono ofe_mono ofe_refl total_n_inclI)
definition pcore_view :: "'a view \<Rightarrow> 'a view option" where 
  "pcore x = Some (View (core (view_auth_proj x)) (core (view_frag_proj x)))"
definition op_view :: "'a view \<Rightarrow> 'a view \<Rightarrow> 'a view" where
  "op_view x y = View (view_auth_proj x \<cdot> view_auth_proj y) (view_frag_proj x \<cdot> view_frag_proj y)"
instance proof
show "non_expansive (valid_raw::'a view \<Rightarrow> sprop)"
apply (rule non_expansiveI) 
apply (auto simp: n_equiv_sprop_def valid_raw_view.rep_eq view_auth_proj_def 
  view_frag_proj_def n_equiv_view_def n_equiv_option_def split: option.splits view.splits)
by (meson view_rel_ne ofe_mono ofe_refl ofe_sym ofe_trans)+
next 
show "non_expansive (pcore::'a view \<Rightarrow> 'a view option)"
proof (rule non_expansiveI)
  fix n and x y :: "'a view"
  assume assm: "n_equiv n x y"
  obtain a1 f1 a2 f2 where xy: "x = View a1 f1" "y= View a2 f2" by (metis view.collapse)
  with assm have "n_equiv n a1 a2" "n_equiv n f1 f2" by (auto simp: n_equiv_view_def)
  then have "n_equiv n (pcore a1) (pcore a2)" "n_equiv n (pcore f1) (pcore f2)"
    using pcore_ne by blast+
  then show "n_equiv n (pcore x) (pcore y)"
    unfolding pcore_view_def xy
    apply (auto simp: n_equiv_option_def n_equiv_view_def core_def split: option.splits)
    using ofe_refl apply blast+
    apply (metis option.simps(3) total_pcore)+
    done
  qed
next
show "non_expansive2 (op::'a view \<Rightarrow> 'a view \<Rightarrow> 'a view)"
  by (rule non_expansive2I) (auto simp: op_view_def n_equiv_view_def)
next
fix a b c :: "'a view"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (cases a; cases b; cases c) (auto simp: camera_assoc op_view_def)
next
fix a b :: "'a view"
show "a \<cdot> b = b \<cdot> a" by (cases a; cases b) (auto simp: camera_comm op_view_def)
next
fix a a' :: "'a view"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" apply (cases a; cases a') unfolding pcore_view_def
  by (auto simp: camera_pcore_id op_view_def core_def total_pcore split: option.splits)
next
fix a a' :: "'a view"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a"
  apply (cases a; cases a') unfolding pcore_view_def 
  by (auto simp: camera_pcore_idem core_def total_pcore split: option.splits)
next
fix a a' b :: "'a view"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  apply (cases a; cases a'; cases b) unfolding pcore_view_def
  apply (auto simp: op_view_def camera_pcore_mono total_pcore pcore_fun_def core_def split: option.splits)
  by (metis (no_types, opaque_lifting) camera_props(5) option.sel total_pcore view.sel(1) view.sel(2))
next
fix a b :: "'a view" and n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
apply (unfold valid_raw_view.rep_eq) apply (cases a; cases b)
subgoal for a1 a2 b1 b2 apply (cases a1; cases b1)
subgoal apply (auto simp: view_auth_proj_def op_view_def op_option_def split: view.splits)
  using view_rel_mono n_incl_op_extend ofe_refl by blast
subgoal apply (auto simp: view_auth_proj_def op_view_def op_option_def split: view.splits)
  using view_rel_mono n_incl_op_extend ofe_refl by blast
subgoal apply (auto simp: view_auth_proj_def op_view_def op_option_def split: view.splits)
  using view_rel_mono n_incl_op_extend ofe_refl by blast
apply (simp add: view_auth_proj_def op_view_def op_option_def op_prod_def split: view.splits prod.splits)
subgoal for a1' b1' c1 a11 m a12 b11 b12
  apply auto
  prefer 2 using view_rel_mono[of n m "a2\<cdot>b2" n m a2, unfolded n_incl_def]
  apply (meson ag_valid_n_incl camera_props(8) linorder_le_cases n_equiv_sprop_def n_incl_op_extend ofe_refl ofe_trans to_ag_n_valid)
  using camera_valid_op by fast done done
next
fix a b c :: "'a view" and n
assume assms: "Rep_sprop (valid_raw a) n" "n_equiv n a (b \<cdot> c)"
obtain a1 a2 b1 b2 c1 c2 where abc: "a=View a1 a2" "b=View b1 b2" "c=View c1 c2"
  by (metis view.collapse)
with assms(2) have n_eq: "n_equiv n a1 (b1\<cdot>c1)" "n_equiv n a2 (b2\<cdot>c2)"
  by (auto simp: op_view_def n_equiv_view_def) 
then have n_eq_prod: "n_equiv n (a1,a2) ((b1,b2)\<cdot>(c1,c2))"
  by (auto simp: op_prod_def)
from assms(1) abc have valid_prod: "n_valid (a1,a2) n"
  apply (cases a1)
  apply (auto simp: valid_raw_view.rep_eq prod_n_valid_def valid_raw_option_def view_rel_n_valid)
  using n_valid_ne ofe_sym to_ag_n_valid by blast
from camera_extend[OF valid_prod n_eq_prod] obtain d1 d2 e1 e2 where de:
  "(a1, a2) = (d1,d2) \<cdot> (e1,e2)" "n_equiv n (d1,d2) (b1, b2)" "n_equiv n (e1,e2) (c1, c2)"
  by auto
let ?d = "View d1 d2" and ?e = "View e1 e2"
from de abc have  "a=?d\<cdot> ?e" "n_equiv n ?d b" "n_equiv n ?e c" 
  by (auto simp: n_equiv_view_def op_view_def op_prod_def)
then show "\<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c" by blast
qed
end

instance view :: (ducamera) dcamera proof
  fix x :: "'a view"
  assume assm: "n_valid x 0"
  obtain auth frag where x: "x = View auth frag" by (rule view.exhaust)
  from assm x have "auth=None \<Longrightarrow> \<exists>a. view_rel 0 a frag" 
    by (simp add: valid_raw_view.rep_eq)
  then have auth_none: "auth=None \<Longrightarrow> \<exists>a. view_rel n a frag" for n
    using auth_view_rel_discrete by auto
  from assm x have "auth=Some (dq,ag) \<Longrightarrow> 
    n_valid dq 0 \<and> (\<exists>a. n_equiv 0 ag (to_ag a) \<and> view_rel 0 a frag)" for dq ag 
    by (simp add: valid_raw_view.rep_eq)
  then have auth_some: "auth=Some (dq,ag) \<Longrightarrow> valid dq \<and> (\<exists>a. ag=(to_ag a) \<and> view_rel n a frag)" 
    for dq ag n using auth_view_rel_discrete by (auto simp: d_equiv d_valid)
  with auth_none have "n_valid x n" for n 
    by (simp add: valid_raw_view.rep_eq x d_equiv valid_def split: option.splits)      
  then show "valid x" unfolding valid_def by blast
qed
  
instantiation view :: (ucamera) ucamera begin
definition \<epsilon>_view :: "'a view" where "\<epsilon>_view = View \<epsilon> \<epsilon>"
instance proof 
  show "valid (\<epsilon>::'a view)"
    by (simp add: valid_def \<epsilon>_view_def valid_raw_view.rep_eq view_rel_unit \<epsilon>_option_def)
next
  fix a :: "'a view"
  show "\<epsilon> \<cdot> a = a" by (simp add: op_view_def \<epsilon>_view_def \<epsilon>_left_id)
next
  show "pcore \<epsilon> = Some (\<epsilon>::'a view)"
  unfolding pcore_view_def \<epsilon>_view_def
  by (simp add: \<epsilon>_pcore core_def split: option.splits)
qed
end

lemma auth_dfrac_op: "\<Zspot>A{dq1 \<cdot> dq2} a = \<Zspot>A{dq1} a \<cdot> \<Zspot>A{dq2} a"
by (auto simp: view_auth_def op_view_def \<epsilon>_left_id op_option_def op_prod_def op_ag_def Rep_ag_inverse)

lemma auth_frag_op: "\<circle>A (a\<cdot>b) = \<circle>A a \<cdot> \<circle>A b"
by (auto simp: op_view_def view_frag_def op_option_def)

lemma auth_frag_mono: "incl a b \<Longrightarrow> incl (\<circle>A a) (\<circle>A b)"
apply (auto simp: incl_def op_view_def view_frag_def op_option_def)
by (metis view.sel(1) view.sel(2))

lemma auth_frag_core: "core (\<circle>A a) = \<circle>A (core a)"
by (auto simp: view_frag_def core_def pcore_view_def pcore_option_def)

lemma auth_both_core_discarded: "core (\<Zspot>A\<box> a \<cdot> \<circle>A b) = (\<Zspot>A\<box> a) \<cdot> \<circle>A (core b)"
by (auto simp: view_auth_def view_frag_def op_view_def core_def pcore_view_def \<epsilon>_left_id 
  op_option_def pcore_option_def pcore_prod_def discarded_core_id pcore_id)

lemma auth_both_core_frac: "core (\<Zspot>A{DfracOwn q} a \<cdot> \<circle>A b) = \<circle>A (core b)"
by (auto simp: core_def pcore_view_def view_auth_def view_frag_def op_view_def pcore_option_def
  op_option_def \<epsilon>_left_id pcore_prod_def pcore_dfrac_def)

lemma auth_core_id: "pcore_id_pred (\<Zspot>A\<box> a)"
by (auto simp: pcore_id_pred_def pcore_view_def view_auth_def \<epsilon>_core)
  (auto simp: core_def pcore_prod_def pcore_option_def pcore_dfrac_def pcore_ag_def)

lemma auth_both_dfrac_n_valid: "n_valid (\<Zspot>A{dq} a \<cdot> \<circle>A b) n \<longleftrightarrow> valid dq \<and> n_incl n b a \<and> n_valid a n"
apply (auto simp: view_auth_def view_frag_def valid_raw_view.rep_eq op_view_def op_option_def 
  \<epsilon>_left_id valid_def n_incl_def n_equiv_ag.rep_eq to_ag.rep_eq view_rel_def intro: ofe_trans ofe_refl)
using dcamera_valid_iff apply auto[1]
using n_valid_ne ofe_sym apply blast
done

lemma auth_both_n_valid: "n_valid (\<Zspot>A a \<cdot> \<circle>A b) n \<longleftrightarrow> n_incl n b a \<and> n_valid a n"
  using auth_both_dfrac_n_valid valid_dfrac_own by blast

lemma option_op_valid_dfrac1:
  "\<lbrakk>option_op (Some (DfracOwn 1, to_ag aa)) (view_auth_proj x) = Some (b, c); n_valid b n\<rbrakk> \<Longrightarrow> b=DfracOwn 1"
apply (cases "view_auth_proj x")
apply (auto simp: op_prod_def op_dfrac_def valid_raw_dfrac_def valid_raw_frac_def)
subgoal for a b' apply (cases a) apply (auto simp: op_frac.rep_eq valid_raw_frac.rep_eq)
using linorder_not_le one_frac.rep_eq apply auto[1]
using one_op order_less_imp_triv by blast done

lemma option_op_prod_left: "option_op (Some (a,b)) (view_auth_proj x) = Some (c, d) \<Longrightarrow> 
  option_op (Some (a,b')) (view_auth_proj x) = Some (e, f) \<Longrightarrow> e=c"
  apply (cases "view_auth_proj x")
  by (auto simp: op_prod_def)
  
lemma view_update: "(\<forall>n bf. view_rel n a (b \<cdot> bf) \<longrightarrow> view_rel n a' (b' \<cdot> bf)) \<Longrightarrow>
  (\<Zspot>A a \<cdot> \<circle>A b) \<leadsto> (\<Zspot>A a' \<cdot> \<circle>A b')"
  unfolding total_update
  apply auto
  apply (auto simp: valid_raw_view.rep_eq view_auth_def view_frag_def op_view_def op_option_def
    \<epsilon>_left_id view_rel_def n_incl_def split: option.splits)
  apply (meson option.simps(3) option_opE)
  apply (meson option.simps(3) option_opE)
  apply (meson option.simps(3) option_opE)
  apply (meson option.simps(3) option_opE)
  apply (frule option_op_valid_dfrac1, simp) using option_op_prod_left apply blast
  subgoal for n z aa ba aaa c ab baa
  apply (cases "view_auth_proj z") apply (auto simp: n_equiv_ag.rep_eq to_ag.rep_eq)
  apply (metis n_valid_ne ofe_sym ofe_trans)
  apply (auto simp: op_prod_def op_ag.rep_eq to_ag_def)
  using dcamera_valid_iff dfrac_not_valid_own apply blast+
done done

lemma view_\<epsilon>_alt: "\<epsilon> = \<circle>A \<epsilon>" by (simp add: \<epsilon>_view_def view_frag_def \<epsilon>_option_def)

lemma auth_update: "(a,b) \<leadsto>\<^sub>L (a',b') \<Longrightarrow> (\<Zspot>A a \<cdot> \<circle>A b) \<leadsto> (\<Zspot>A a' \<cdot> \<circle>A b')"
proof -
assume assm: "(a, b) \<leadsto>\<^sub>L (a', b')"
from assm have "\<forall>n bf. view_rel n a (b \<cdot> bf) \<longrightarrow> view_rel n a' (b' \<cdot> bf)"
  by (auto simp: lup_def \<epsilon>_left_id view_rel_def n_incl_def camera_assoc)
from view_update[OF this] show ?thesis .
qed

lemma auth_update_alloc: "(a,\<epsilon>) \<leadsto>\<^sub>L (a',b') \<Longrightarrow> \<Zspot>A a \<leadsto> (\<Zspot>A a' \<cdot> \<circle>A b')"
  by (drule auth_update) (auto simp: \<epsilon>_right_id view_\<epsilon>_alt[symmetric])

lemma auth_update_dealloc: "(a, b) \<leadsto>\<^sub>L (a', \<epsilon>) \<Longrightarrow> (\<Zspot>A a \<cdot> \<circle>A b) \<leadsto>\<Zspot>A a'"
  by (drule auth_update) (auto simp: \<epsilon>_right_id view_\<epsilon>_alt[symmetric])

lemma unfold_add_view: "x+y=1 \<Longrightarrow> \<Zspot>A a = \<Zspot>A{DfracOwn(x+y)} a"
  by auto
  
subsubsection \<open>MapView camera\<close>

definition map_view_rel :: "nat \<Rightarrow> ('a,'b::ofe) fmap \<Rightarrow> ('a\<rightharpoonup>(dfrac\<times>'b ag)) \<Rightarrow> bool" where 
  "map_view_rel n m f \<equiv>
    \<forall>k d vag. f k = Some (d,vag) \<longrightarrow> (\<exists>v. n_equiv n vag (to_ag v) \<and> valid d \<and> fmlookup m k = Some v)"

lemma map_view_relE: "\<lbrakk>map_view_rel n m f; f k = Some (d,vag)\<rbrakk> \<Longrightarrow>
  \<exists>v. n_equiv n vag (to_ag v) \<and> valid d \<and> fmlookup m k = Some v"
  by (simp add: map_view_rel_def)
  
lemma map_view_rel_mono: 
  assumes "map_view_rel n1 m1 f1" "n_equiv n2 m1 m2" "n_incl n2 f2 f1" "n2 \<le> n1"
  shows "map_view_rel n2 m2 f2"
proof -
  from assms(1) have rel1: "\<forall>k d vag. f1 k = Some (d,vag) \<longrightarrow> (\<exists>v. n_equiv n1 vag (to_ag v) \<and> valid d 
    \<and> fmlookup m1 k = Some v)" by (simp add: map_view_rel_def)
  {
    fix k d vag
    {
      assume f2k: "f2 k = Some (d, vag)"
      then obtain d' vag' where dvag': "f1 k = Some (d', vag')" "n_incl n2 (Some (d,vag)) (Some (d',vag'))"
        using fun_n_incl[OF assms(3)] 
        by (metis (no_types, lifting) domIff n_equiv_option_def n_equiv_prod.elims(2) n_incl_def subsetD)
      with rel1 obtain v' where v': "n_equiv n1 vag' (to_ag v')" "valid d'" "fmlookup m1 k = Some v'"
        by blast
      from dvag'(2) have eq_or_incl: "(n_equiv n2 d d' \<and> n_equiv n2 vag vag') \<or>
        (n_incl n2 d d' \<and> n_incl n2 vag vag')" by (auto simp: option_n_incl)
      with v'(1) assms(4) have v'2: "n_equiv n2 vag (to_ag v') \<or> n_incl n2 (to_ag v') vag" 
      by (meson ag_valid_n_incl camera_props(8) n_equiv_sprop_def ofe_mono ofe_trans to_ag_n_valid)
      from assms(2) v'(3) obtain v where v: "fmlookup m2 k = Some v" "n_equiv n2 v' v" 
        unfolding n_equiv_fmap.rep_eq 
        by (metis fmdom'I fmdom'_notI n_equiv_fun_def n_equiv_option_def option.sel)
      from this(2) v'2 have "n_equiv n2 vag (to_ag v) \<or> n_incl n2 (to_ag v) vag"
        using ofe_trans to_ag_n_equiv to_ag_n_incl by blast
      with ag_incl_equiv have "n_incl n2 (to_ag v) vag" using ofe_sym by blast
      from v'(1) to_ag_n_valid have "n_valid vag' n1" using n_valid_ne ofe_sym by blast
      with ag_valid_n_incl[OF this] eq_or_incl assms(4) have "n_equiv n2 vag vag'"
        using Rep_sprop ag_valid_n_incl by blast
      with \<open>n_valid vag' n1\<close> assms(4) have "n_valid vag n2"
        using Rep_sprop n_valid_ne ofe_sym by fastforce
      from eq_or_incl d_equiv n_incl_def v'(2) have "valid d" by (metis camera_valid_op valid_dfrac)
      with ag_valid_n_incl[OF \<open>n_valid vag n2\<close> \<open>n_incl n2 (to_ag v) vag\<close>] v(1)
      have "\<exists>v. n_equiv n2 vag (to_ag v) \<and> valid d \<and> fmlookup m2 k = Some v" using ofe_sym by blast
    } 
    then have "f2 k = Some (d,vag) \<longrightarrow> (\<exists>v. n_equiv n2 vag (to_ag v) \<and> valid d \<and> fmlookup m2 k = Some v)"
      by simp
  } 
  then show ?thesis unfolding map_view_rel_def by simp
qed

lemma map_view_rel_n_valid: "map_view_rel n a b \<Longrightarrow> n_valid b n" 
  apply (auto simp: valid_raw_fun.rep_eq valid_raw_option_def split: option.splits)
  subgoal for k d vag apply (drule map_view_relE) 
  apply (auto simp: prod_n_valid_def valid_def valid_raw_ag.rep_eq n_equiv_ag.rep_eq)
  by (metis Set.set_insert ofe_trans_eqR singleton_insert_inj_eq to_ag.rep_eq) done

lemma map_view_rel_unit: "\<exists>a. map_view_rel n a \<epsilon>"
proof -
  have "map_view_rel n fmempty \<epsilon>" by (auto simp: map_view_rel_def \<epsilon>_fun_def \<epsilon>_option_def)
  then show ?thesis by auto
qed
  
lemma map_view_rel_ne: "\<lbrakk>n_equiv n m1 m2; n_equiv n f1 f2\<rbrakk> \<Longrightarrow> map_view_rel n m1 f1 \<longleftrightarrow> map_view_rel n m2 f2"
  apply (rule iffI)
  using map_view_rel_mono[of n m1 f1 n m2 f2] apply (simp add: ofe_sym total_n_inclI)
  using map_view_rel_mono[of n m2 f2 n m1 f1] by (simp add: ofe_sym total_n_inclI)

lemma map_view_rel_discrete: "map_view_rel 0 (a::('a,'b::discrete) fmap) b \<Longrightarrow> map_view_rel n a b"
  unfolding map_view_rel_def
  by (auto simp: d_equiv)
  
datatype ('k,'v) map_view = 
  MapView (map_view_auth_proj: "((dfrac\<times>('k,'v) fmap ag)) option") (map_view_frag_proj: "('k\<rightharpoonup>(dfrac\<times>'v ag))")
  
definition mview_auth :: "dfrac \<Rightarrow> ('k,'v) fmap \<Rightarrow> ('k,'v::ofe) map_view" ("\<Zspot>V{_} _") where
  "mview_auth dq a = MapView (Some (dq, to_ag a)) \<epsilon>"
definition mview_frag :: "('k\<rightharpoonup>(dfrac\<times>'v ag)) \<Rightarrow> ('k,'v::ofe) map_view" ("\<circle>V _") where 
  "mview_frag b = MapView None b"

abbreviation mview_auth_disc :: "('k,'v) fmap \<Rightarrow> ('k,'v::ofe) map_view" ("\<Zspot>V\<box> _") where 
  "mview_auth_disc a \<equiv> \<Zspot>V{DfracDiscarded} a"
abbreviation mview_auth_full :: "('k,'v) fmap \<Rightarrow> ('k,'v::ofe) map_view" ("\<Zspot>V _") where
  "mview_auth_full a \<equiv> \<Zspot>V{DfracOwn 1} a"

definition map_view_auth :: "dfrac \<Rightarrow> ('k,'v) fmap \<Rightarrow> ('k,'v::ofe) map_view" where
  "map_view_auth dq m = \<Zspot>V{dq} m"
definition map_view_frag :: "'k \<Rightarrow> dfrac \<Rightarrow> 'v \<Rightarrow> ('k,'v::ofe) map_view" where
  "map_view_frag k dq v = \<circle>V [k\<mapsto>(dq,to_ag v)]"
  
instantiation map_view :: (type,ofe) ofe begin
definition n_equiv_map_view :: "nat \<Rightarrow> ('a, 'b) map_view \<Rightarrow> ('a, 'b) map_view \<Rightarrow> bool" where
  "n_equiv_map_view n v1 v2 \<equiv> n_equiv n (map_view_auth_proj v1) (map_view_auth_proj v2) 
    \<and> n_equiv n (map_view_frag_proj v1) (map_view_frag_proj v2)"
definition ofe_eq_map_view :: "('a, 'b) map_view \<Rightarrow> ('a, 'b) map_view \<Rightarrow> bool" where
  "ofe_eq_map_view v1 v2 \<equiv> ofe_eq (map_view_auth_proj v1) (map_view_auth_proj v2) 
    \<and> ofe_eq (map_view_frag_proj v1) (map_view_frag_proj v2)"
instance proof (standard)
fix n and x y z :: "('a,'b) map_view"
show "n_equiv n x y \<Longrightarrow> n_equiv n y z \<Longrightarrow> n_equiv n x z"
  unfolding map_view_auth_proj_def map_view_frag_proj_def n_equiv_map_view_def ofe_eq_map_view_def
  apply (cases x; cases y; cases z)
  apply simp
  using ofe_trans by metis
qed (auto simp: map_view_auth_proj_def n_equiv_map_view_def ofe_eq_map_view_def
  ofe_refl ofe_mono ofe_sym ofe_limit intro: ofe_trans split: map_view.splits)
end

instance map_view :: (type,discrete) discrete 
  by standard (auto simp: map_view_auth_proj_def n_equiv_map_view_def ofe_eq_map_view_def 
    d_equiv d_eq split: map_view.splits)

lemma option_bind_map: "Option.bind x (\<lambda>a. map_option (\<lambda>b. f a b) y) =
  (case x of Some a \<Rightarrow> (case y of Some b \<Rightarrow> Some (f a b) | None \<Rightarrow> None) | None \<Rightarrow> None)"
  by (metis (mono_tags) bind.bind_lunit bind.bind_lzero map_option_case option.case_eq_if option.exhaust_sel)

lemma mv_pcore_alt: "Option.bind (pcore (map_view_auth_proj mv)) 
  (\<lambda>auth. map_option (\<lambda>frag. MapView auth frag) (pcore (map_view_frag_proj mv))) 
  = (case mv of (MapView auth frag) \<Rightarrow> 
  (case pcore auth of Some a \<Rightarrow> (case pcore frag of Some b \<Rightarrow> Some (MapView a b) | None \<Rightarrow> None) | None \<Rightarrow> None))"
  using option_bind_map map_view_auth_proj_def map_view_frag_proj_def 
  by (auto split: map_view.splits)  

instantiation map_view :: (type, ofe) camera begin
lift_definition valid_raw_map_view :: "('a, 'b) map_view \<Rightarrow> sprop" is
  "\<lambda>mv n. case map_view_auth_proj mv of 
    Some (dq, ag) \<Rightarrow> n_valid dq n \<and> (\<exists>a. n_equiv n ag (to_ag a) \<and> map_view_rel n a (map_view_frag_proj mv))
  | None \<Rightarrow> \<exists>a. map_view_rel n a (map_view_frag_proj mv)"
  apply (simp add: map_view_auth_proj_def map_view_frag_proj_def split: option.splits map_view.splits)
  apply (meson map_view_rel_mono ofe_refl total_n_inclI)
  by (smt (verit) case_prod_conv dcamera_valid_iff map_view_rel_mono ofe_mono ofe_refl total_n_inclI)
definition pcore_map_view :: "('a, 'b) map_view \<Rightarrow> ('a, 'b) map_view option" where
  "pcore_map_view mv = Option.bind (pcore (map_view_auth_proj mv))
    (\<lambda>auth. map_option (\<lambda>frag. MapView auth frag) (pcore (map_view_frag_proj mv)))"
definition op_map_view :: "('a, 'b) map_view \<Rightarrow> ('a, 'b) map_view \<Rightarrow> ('a, 'b) map_view" where
  "op_map_view mv1 mv2 = MapView (map_view_auth_proj mv1 \<cdot> map_view_auth_proj mv2) 
    (map_view_frag_proj mv1 \<cdot> map_view_frag_proj mv2)"
instance proof
show "non_expansive (valid_raw::('a, 'b) map_view \<Rightarrow> sprop)"
apply (rule non_expansiveI) 
apply (auto simp: n_equiv_sprop_def valid_raw_map_view.rep_eq map_view_auth_proj_def 
  map_view_frag_proj_def n_equiv_map_view_def n_equiv_option_def split: option.splits map_view.splits)
by (meson map_view_rel_ne ofe_mono ofe_refl ofe_sym ofe_trans)+
next 
show "non_expansive (pcore::('a, 'b) map_view \<Rightarrow> ('a, 'b) map_view option)"
proof (rule non_expansiveI)
  fix n and x y :: "('a,'b) map_view"
  assume assm: "n_equiv n x y"
  obtain a1 f1 a2 f2 where xy: "x = MapView a1 f1" "y= MapView a2 f2" by (metis map_view.collapse)
  with assm have "n_equiv n a1 a2" "n_equiv n f1 f2" by (auto simp: n_equiv_map_view_def)
  then have "n_equiv n (pcore a1) (pcore a2)" "n_equiv n (pcore f1) (pcore f2)"
    using pcore_ne by blast+
  then show "n_equiv n (pcore x) (pcore y)"
    unfolding pcore_map_view_def mv_pcore_alt xy
    by (auto simp: n_equiv_option_def n_equiv_map_view_def split: option.splits)
  qed
next
show "non_expansive2 (op::('a, 'b) map_view \<Rightarrow> ('a, 'b) map_view \<Rightarrow> ('a, 'b) map_view)"
  by (rule non_expansive2I) (auto simp: op_map_view_def n_equiv_map_view_def)
next
fix a b c :: "('a,'b) map_view"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (cases a; cases b; cases c) (auto simp: camera_assoc op_map_view_def)
next
fix a b :: "('a,'b) map_view"
show "a \<cdot> b = b \<cdot> a" by (cases a; cases b) (auto simp: camera_comm op_map_view_def)
next
fix a a' :: "('a,'b) map_view"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" apply (cases a; cases a') unfolding pcore_map_view_def
  unfolding mv_pcore_alt by (auto simp: camera_pcore_id op_map_view_def split: option.splits)
next
fix a a' :: "('a,'b) map_view"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a"
  apply (cases a; cases a') unfolding pcore_map_view_def unfolding mv_pcore_alt 
  by (auto simp: camera_pcore_idem split: option.splits)
next
fix a a' b :: "('a,'b) map_view"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  apply (cases a; cases a'; cases b) unfolding pcore_map_view_def unfolding mv_pcore_alt
  apply (auto simp: op_map_view_def camera_pcore_mono total_pcore pcore_fun_def split: option.splits)
  by (metis camera_pcore_mono map_view.sel(1) map_view.sel(2) option.sel pcore_fun_def)
next
fix a b :: "('a,'b) map_view" and n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
apply (unfold valid_raw_map_view.rep_eq) apply (cases a; cases b)
subgoal for a1 a2 b1 b2 apply (cases a1; cases b1)
subgoal apply (auto simp: map_view_auth_proj_def op_map_view_def op_option_def split: map_view.splits)
  using map_view_rel_mono n_incl_op_extend ofe_refl by blast
subgoal apply (auto simp: map_view_auth_proj_def op_map_view_def op_option_def split: map_view.splits)
  using map_view_rel_mono n_incl_op_extend ofe_refl by blast
subgoal apply (auto simp: map_view_auth_proj_def op_map_view_def op_option_def split: map_view.splits)
  using map_view_rel_mono n_incl_op_extend ofe_refl by blast
apply (simp add: map_view_auth_proj_def op_map_view_def op_option_def op_prod_def split: map_view.splits prod.splits)
subgoal for a1' b1' c1 a11 m a12 b11 b12
  apply auto
  prefer 2 using map_view_rel_mono[of n m "a2\<cdot>b2" n m a2, unfolded n_incl_def]
  apply (meson ag_valid_n_incl camera_props(8) linorder_le_cases n_equiv_sprop_def n_incl_op_extend ofe_refl ofe_trans to_ag_n_valid)
  using camera_valid_op by fast done done
next
fix a b c :: "('a,'b) map_view" and n
assume assms: "Rep_sprop (valid_raw a) n" "n_equiv n a (b \<cdot> c)"
obtain a1 a2 b1 b2 c1 c2 where abc: "a=MapView a1 a2" "b=MapView b1 b2" "c=MapView c1 c2"
  by (metis map_view.collapse)
with assms(2) have n_eq: "n_equiv n a1 (b1\<cdot>c1)" "n_equiv n a2 (b2\<cdot>c2)"
  by (auto simp: op_map_view_def n_equiv_map_view_def) 
then have n_eq_prod: "n_equiv n (a1,a2) ((b1,b2)\<cdot>(c1,c2))"
  by (auto simp: op_prod_def)
from assms(1) abc have valid_prod: "n_valid (a1,a2) n"
  apply (cases a1)
  apply (auto simp: valid_raw_map_view.rep_eq prod_n_valid_def valid_raw_option_def map_view_rel_n_valid)
  using n_valid_ne ofe_sym to_ag_n_valid by blast
from camera_extend[OF valid_prod n_eq_prod] obtain d1 d2 e1 e2 where de:
  "(a1, a2) = (d1,d2) \<cdot> (e1,e2)" "n_equiv n (d1,d2) (b1, b2)" "n_equiv n (e1,e2) (c1, c2)"
  by auto
let ?d = "MapView d1 d2" and ?e = "MapView e1 e2"
from de abc have  "a=?d\<cdot> ?e" "n_equiv n ?d b" "n_equiv n ?e c" 
  by (auto simp: n_equiv_map_view_def op_map_view_def op_prod_def)
then show "\<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c" by blast
qed
end

instance map_view :: (type,discrete) dcamera proof
  fix x :: "('a,'b) map_view"
  assume assm: "n_valid x 0"
  obtain auth frag where x: "x = MapView auth frag" by (rule map_view.exhaust)
  from assm x have "auth=None \<Longrightarrow> \<exists>a. map_view_rel 0 a frag" 
    by (simp add: valid_raw_map_view.rep_eq)
  then have auth_none: "auth=None \<Longrightarrow> \<exists>a. map_view_rel n a frag" for n
    using map_view_rel_discrete by auto
  from assm x have "auth=Some (dq,ag) \<Longrightarrow> 
    n_valid dq 0 \<and> (\<exists>a. n_equiv 0 ag (to_ag a) \<and> map_view_rel 0 a frag)" for dq ag 
    by (simp add: valid_raw_map_view.rep_eq)
  then have auth_some: "auth=Some (dq,ag) \<Longrightarrow> valid dq \<and> (\<exists>a. ag=(to_ag a) \<and> map_view_rel n a frag)" 
    for dq ag n using map_view_rel_discrete by (auto simp: d_equiv d_valid)
  with auth_none have "n_valid x n" for n 
    by (simp add: valid_raw_map_view.rep_eq x d_equiv valid_def split: option.splits)      
  then show "valid x" unfolding valid_def by blast
qed
  
instantiation map_view :: (type,ofe) ucamera begin
definition \<epsilon>_map_view :: "('a, 'b) map_view" where "\<epsilon>_map_view = MapView \<epsilon> \<epsilon>"
instance proof 
  show "valid (\<epsilon>::('a,'b) map_view)"
    by (simp add: valid_def \<epsilon>_map_view_def valid_raw_map_view.rep_eq map_view_rel_unit \<epsilon>_option_def)
next
  fix a :: "('a,'b) map_view"
  show "\<epsilon> \<cdot> a = a" by (simp add: op_map_view_def \<epsilon>_map_view_def \<epsilon>_left_id)
next
  show "pcore \<epsilon> = Some (\<epsilon>::('a,'b) map_view)"
  unfolding pcore_map_view_def \<epsilon>_map_view_def mv_pcore_alt
  by (simp add: \<epsilon>_pcore split: option.splits)
qed
end

lemma pcore_id_frag: "pcore dq = Some dq \<Longrightarrow> pcore_id_pred (map_view_frag k dq v)"
  unfolding pcore_id_pred_def map_view_frag_def mview_frag_def pcore_map_view_def mv_pcore_alt
  apply (auto simp add: fun_eq_iff \<epsilon>_pcore \<epsilon>_option_def[symmetric] comp_def pcore_fun_def 
    split: option.splits)
  apply (metis \<epsilon>_option_def not_Some_eq total_pcore)
  by (auto simp: pcore_option_def pcore_prod_def pcore_ag_def)

lemma map_view_auth_valid: "valid (map_view_auth (DfracOwn 1) fmempty)"
  apply (auto simp: map_view_auth_def valid_def valid_raw_map_view.rep_eq map_view_auth_proj_def 
    mview_auth_def)
  using dcamera_valid_iff valid_dfrac_own apply blast
  apply (auto simp: map_view_rel_def \<epsilon>_fun_def \<epsilon>_option_def)
  using ofe_refl by blast
  
lemma view_both_valid: "n_valid (\<Zspot>V{dq} a \<cdot> \<circle>V b) n \<longleftrightarrow> map_view_rel n a b \<and> valid dq"
  unfolding mview_auth_def mview_frag_def valid_raw_map_view.rep_eq
  apply (auto simp: op_map_view_def op_option_def map_empty_left_id to_ag_n_equiv op_fun_def 
      \<epsilon>_option_def \<epsilon>_fun_def split: option.splits)
  subgoal for a' using map_view_rel_mono[of n a' b n a b] by (simp add: ofe_sym)
  using dcamera_valid_iff apply blast+
  using ofe_refl by auto

lemma view_both_valid2: "n_valid (\<Zspot>V a \<cdot> \<circle>V b) n \<longleftrightarrow> map_view_rel n a b"
  using view_both_valid valid_dfrac_own by auto

lemma map_view_both_valid: "n_valid (map_view_auth (DfracOwn 1) m \<cdot> map_view_frag k dq v) n \<longleftrightarrow>
  valid dq \<and> n_equiv n (fmlookup m k) (Some v)"
  unfolding map_view_auth_def map_view_frag_def
  unfolding view_both_valid2 map_view_rel_def 
  by (auto simp: to_ag_n_equiv n_equiv_option_def ofe_sym)

lemma map_view_frac_unique: "n_valid (map_view_frag k (DfracOwn 1) v \<cdot> MapView ma mf) n \<Longrightarrow> mf k = None"
proof -
assume assm: "n_valid (map_view_frag k (DfracOwn 1) v \<cdot> MapView ma mf) n"
from this[unfolded valid_raw_map_view.rep_eq map_view_frag_def mview_frag_def op_map_view_def
  op_option_def, simplified] have "\<exists>a. map_view_rel n a ([k \<mapsto> (DfracOwn 1, to_ag v)] \<cdot> mf)" 
  apply (cases ma) by auto
then obtain a where "map_view_rel n a ([k \<mapsto> (DfracOwn 1, to_ag v)] \<cdot> mf)" by blast
from this[unfolded map_view_rel_def] have 1: "([k \<mapsto> (DfracOwn 1, to_ag v)] \<cdot> mf) ka =
  Some (d, vag) \<longrightarrow> (\<exists>v. n_equiv n vag (to_ag v) \<and> camera_class.valid d \<and> fmlookup a ka = Some v)"
  for ka d vag by simp
{
  fix d' v'
  assume some: "mf k = Some (d', v')"
  with 1[of k] have "\<exists>d vag. ([k \<mapsto> (DfracOwn 1, to_ag v)] \<cdot> mf) k = Some (d, vag) 
    \<and> (\<exists>v. n_equiv n vag (to_ag v) \<and> camera_class.valid d \<and> fmlookup a k = Some v)"
    by (auto simp: op_fun_def op_option_def op_prod_def)
  then obtain d vag where "([k \<mapsto> (DfracOwn 1, to_ag v)] \<cdot> mf) k = Some (d, vag) 
    \<and> (\<exists>v. n_equiv n vag (to_ag v) \<and> camera_class.valid d \<and> fmlookup a k = Some v)" by blast
  with some have "d= DfracOwn 1 \<cdot> d' \<and> camera_class.valid d" 
    by (auto simp: op_fun_def op_option_def op_prod_def)
  then have False apply (cases d; cases d') apply (auto simp: op_dfrac_def valid_def 
    valid_raw_dfrac_def valid_raw_frac_def frac_op_plus)
    using \<open>d = DfracOwn 1 \<cdot> d' \<and> camera_class.valid d\<close> dfrac_not_valid_own by blast+
}
then show ?thesis apply (cases "mf k") by auto
qed

lemma map_view_auth_unique: "n_valid (map_view_auth (DfracOwn 1) x \<cdot> MapView ma mf) n \<Longrightarrow> ma = None"
apply (cases ma)
apply (auto simp: valid_raw_map_view.rep_eq map_view_auth_def mview_auth_def op_map_view_def
  op_option_def op_prod_def split: option.splits)
using dfrac_not_valid_own[unfolded valid_def] dcamera_valid_iff by blast

lemma map_view_split: "n_equiv n (MapView ma mf) (MapView ma \<epsilon> \<cdot> MapView \<epsilon> mf)"
by (auto simp: n_equiv_map_view_def op_map_view_def \<epsilon>_left_id \<epsilon>_right_id ofe_refl)

lemma n_incl_map_view_auth: "\<lbrakk>n_incl n (map_view_auth (DfracOwn 1) h) (MapView x_auth x_frag); 
  n_valid (MapView x_auth x_frag) n\<rbrakk> \<Longrightarrow> \<exists>fm_ag. x_auth = Some (DfracOwn 1,fm_ag) \<and> n_equiv n fm_ag (to_ag h)"
proof -
  assume assms: "n_incl n (map_view_auth (DfracOwn 1) h) (MapView x_auth x_frag)" 
  "n_valid (MapView x_auth x_frag) n"
  then obtain y where y: "n_equiv n (MapView x_auth x_frag) (map_view_auth (DfracOwn 1) h \<cdot> y)" 
    unfolding n_incl_def by blast
  then obtain y_auth y_frag where "y = MapView y_auth y_frag" using map_view.exhaust by blast
  with y have *: "n_equiv n x_auth (Some (DfracOwn 1, to_ag h) \<cdot> y_auth)" 
    by (auto simp: n_equiv_map_view_def op_map_view_def map_view_auth_def mview_auth_def)
  then have "y_auth = None \<Longrightarrow> n_equiv n x_auth (Some (DfracOwn 1, to_ag h))" by (simp add: op_option_def)
  then have 1:"y_auth = None \<Longrightarrow> \<exists>fm_ag. x_auth = Some (DfracOwn 1,fm_ag) \<and> n_equiv n fm_ag (to_ag h)"
    by (auto simp: n_equiv_option_def)
  from * have "y_auth=Some (dy,fm_ag_y) \<Longrightarrow> \<exists>fm_ag. x_auth = Some (DfracOwn 1\<cdot>dy,fm_ag) \<and> n_equiv n fm_ag
    (to_ag h\<cdot>fm_ag_y)" for dy fm_ag_y by (auto simp: n_equiv_option_def op_option_def op_prod_def)
  with assms(2) have "y_auth=Some (dy,fm_ag_y) \<Longrightarrow> False" for dy fm_ag_y apply (cases dy)
    apply (auto simp: valid_raw_map_view.rep_eq valid_raw_dfrac_def op_dfrac_def)
    using frac_not_valid valid_frac apply auto by (meson less_imp_not_less one_op)
  with 1 show "\<exists>fm_ag. x_auth = Some (DfracOwn 1,fm_ag) \<and> n_equiv n fm_ag (to_ag h)" 
    by (cases y_auth) auto
qed 

lemma n_incl_map_view_frag: "\<lbrakk>n_incl n (map_view_frag l (DfracOwn 1) x) (MapView (Some (a, b)) y); 
  n_valid (MapView (Some (a, b)) y) n\<rbrakk> \<Longrightarrow> n_equiv n (y l) (Some (DfracOwn 1,to_ag x))"
proof -
  assume assms: "n_incl n (map_view_frag l (DfracOwn 1) x) (MapView (Some (a, b)) y)"
    "n_valid (MapView (Some (a, b)) y) n"
  then obtain c_a c_f where c: "n_equiv n (MapView (Some (a, b)) y) (map_view_frag l (DfracOwn 1) x
   \<cdot> MapView c_a c_f)"
    unfolding n_incl_def using map_view.exhaust by metis
  then have "n_equiv n y ([l\<mapsto>(DfracOwn 1, (to_ag x))] \<cdot> c_f)" 
    by (auto simp: n_equiv_map_view_def op_map_view_def map_view_frag_def mview_frag_def)
  then have "n_equiv n (y l) (Some (DfracOwn 1, to_ag x) \<cdot> c_f l)" apply (cases "c_f l")
    apply (auto simp: n_equiv_fun_def op_fun_def)
    apply (smt (verit, del_insts) option_op.simps(2))
    by (metis (full_types))
  with n_valid_ne[OF c assms(2)] show "n_equiv n (y l) (Some (DfracOwn 1, to_ag x))" 
    apply (cases "c_f l") apply (auto simp: op_option_def valid_raw_map_view.rep_eq op_prod_def
      map_view_rel_def op_map_view_def map_view_frag_def mview_frag_def op_fun_def
      split: option.splits)
    apply (metis \<open>n_valid (map_view_frag l (DfracOwn 1) x \<cdot> MapView c_a c_f) n\<close> map_view_frac_unique
      option.simps(3))
    by (metis \<open>n_valid (map_view_frag l (DfracOwn 1) x \<cdot> MapView c_a c_f) n\<close> map_view_frac_unique 
      option.distinct(1))
qed 

lemma map_view_rel_singleton_full_op: "map_view_rel n h ([l \<mapsto> (DfracOwn 1, v)] \<cdot> f) \<Longrightarrow> f l = None"
proof -
  assume assm: "map_view_rel n h ([l \<mapsto> (DfracOwn 1, v)] \<cdot> f)"
  have "\<exists>x y. ([l \<mapsto> (DfracOwn 1, v)] \<cdot> f) l = Some (x,y)" apply (cases "f l")
    by (auto simp: op_fun_def op_option_def)
  then obtain d x where dx: "([l \<mapsto> (DfracOwn 1, v)] \<cdot> f) l = Some (d,x)" by blast
  with assm have "valid d" by (auto simp: map_view_rel_def)
  with dx have "f l \<noteq> None \<Longrightarrow> False" by (auto simp: op_fun_def op_option_def op_prod_def dfrac_not_valid_own)
  then show "f l = None" by blast
qed
end