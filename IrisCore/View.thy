theory View
imports DerivedConstructions Frac
begin

subsubsection \<open>View camera\<close>
text \<open>A camera combinator similar to \<^typ>\<open>'m auth\<close>\<close>


definition map_view_rel :: "nat \<Rightarrow> ('a\<rightharpoonup>('b::ofe)) \<Rightarrow> ('a\<rightharpoonup>(dfrac\<times>'b ag)) \<Rightarrow> bool" where "map_view_rel n m f \<equiv>
  \<forall>k d vag. f k = Some (d,vag) \<longrightarrow> (\<exists>v. n_equiv n vag (to_ag v) \<and> valid d \<and> m k = Some v)"

lemma map_view_rel_mono: 
  assumes "map_view_rel n1 m1 f1" "n_equiv n2 m1 m2" "n_incl n2 f2 f1" "n2 \<le> n1"
  shows "map_view_rel n2 m2 f2"
proof -
  from assms(1) have rel1: "\<forall>k d vag. f1 k = Some (d,vag) \<longrightarrow> (\<exists>v. n_equiv n1 vag (to_ag v) \<and> valid d 
    \<and> m1 k = Some v)" by (simp add: map_view_rel_def)
  {
    fix k d vag
    {
      assume f2k: "f2 k = Some (d, vag)"
      then obtain d' vag' where dvag': "f1 k = Some (d', vag')" "n_incl n2 (Some (d,vag)) (Some (d',vag'))"
        using fun_n_incl[OF assms(3)] 
        by (metis (no_types, lifting) domIff n_equiv_option_def n_equiv_prod.elims(2) n_incl_def subsetD)
      with rel1 obtain v' where v': "n_equiv n1 vag' (to_ag v')" "valid d'" "m1 k = Some v'"
        by blast
      from dvag'(2) have eq_or_incl: "(n_equiv n2 d d' \<and> n_equiv n2 vag vag') \<or>
        (n_incl n2 d d' \<and> n_incl n2 vag vag')" by (auto simp: option_n_incl)
      with v'(1) assms(4) have v'2: "n_equiv n2 vag (to_ag v') \<or> n_incl n2 (to_ag v') vag" 
        by (smt (verit, ccfv_SIG) camera_props(7) n_incl_def ofe_down_contr ofe_sym ofe_trans 
          to_ag.rep_eq to_ag_op valid_raw_ag.rep_eq)
      from assms(2) v'(3) obtain v where v: "m2 k = Some v" "n_equiv n2 v' v"
        by (metis n_equiv_fun_def n_equiv_option_def option.inject option.simps(3)) 
      from this(2) v'2 have "n_equiv n2 vag (to_ag v) \<or> n_incl n2 (to_ag v) vag"
         by (metis ag_incl_equiv ofe_sym to_ag_n_incl)
      with ag_incl_equiv have "n_incl n2 (to_ag v) vag" using ofe_sym by blast
      from v'(1) to_ag_n_valid have "n_valid vag' n1" using n_valid_ne ofe_sym by blast
      with ag_valid_n_incl[OF this] eq_or_incl assms(4) have "n_equiv n2 vag vag'"
        using Rep_sprop ag_valid_n_incl by blast
      with \<open>n_valid vag' n1\<close> assms(4) have "n_valid vag n2"
        using Rep_sprop n_valid_ne ofe_sym by fastforce
      from eq_or_incl d_equiv n_incl_def v'(2) have "valid d" by (metis camera_valid_op valid_dfrac)
      with ag_valid_n_incl[OF \<open>n_valid vag n2\<close> \<open>n_incl n2 (to_ag v) vag\<close>] v(1)
      have "\<exists>v. n_equiv n2 vag (to_ag v) \<and> valid d \<and> m2 k = Some v" using ofe_sym by blast
    } 
    then have "f2 k = Some (d,vag) \<longrightarrow> (\<exists>v. n_equiv n2 vag (to_ag v) \<and> valid d \<and> m2 k = Some v)"
      by simp
  } 
  then show ?thesis unfolding map_view_rel_def by simp
qed

lemma map_view_rel_n_valid: "map_view_rel n a b \<Longrightarrow> n_valid b n" sorry
lemma map_view_rel_unit: "\<exists>a. map_view_rel n a \<epsilon>" sorry
lemma map_view_rel_ne: "\<lbrakk>n_equiv n m1 m2; n_equiv n f1 f2\<rbrakk> \<Longrightarrow> map_view_rel n m1 f1 \<longleftrightarrow> map_view_rel n m2 f2"
  apply (rule iffI)
  using map_view_rel_mono[of n m1 f1 n m2 f2] apply (simp add: ofe_sym total_n_inclI)
  using map_view_rel_mono[of n m2 f2 n m1 f1] by (simp add: ofe_sym total_n_inclI)

datatype ('k,'v) map_view = 
  MapView (map_view_auth_proj: "((dfrac\<times>('k\<rightharpoonup>('v)) ag)) option") (map_view_frag_proj: "('k\<rightharpoonup>(dfrac\<times>'v ag))")

definition map_view_auth :: "dfrac \<Rightarrow> ('k\<rightharpoonup>'v) \<Rightarrow> ('k,'v::ofe) map_view" ("\<Zspot>V{_} _") where
  "map_view_auth dq a = MapView (Some (dq, to_ag a)) \<epsilon>"
definition map_view_frag :: "('k\<rightharpoonup>(dfrac\<times>'v ag)) \<Rightarrow> ('k,'v::ofe) map_view" ("\<circle>V _") where 
  "map_view_frag b = MapView None b"

abbreviation map_view_auth_disc :: "('k\<rightharpoonup>'v) \<Rightarrow> ('k,'v::ofe) map_view" ("\<Zspot>V\<box> _") where 
  "map_view_auth_disc a \<equiv> \<Zspot>V{DfracDiscarded} a"
abbreviation map_view_auth_full :: "('k\<rightharpoonup>'v) \<Rightarrow> ('k,'v::ofe) map_view" ("\<Zspot>V _") where
  "map_view_auth_full a \<equiv> \<Zspot>V{DfracOwn 1} a"

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
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n" sorry
next
fix a b c :: "('a,'b) map_view" and n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b \<cdot> c) \<Longrightarrow> 
  \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c" sorry
qed
end