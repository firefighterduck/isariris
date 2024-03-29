theory DerivedConstructions
imports CoreStructures
begin
subsection \<open> Basic camera constructions \<close>

subsubsection \<open> Tuple/Product type \<close>
instantiation prod :: (camera,camera) camera begin
  definition valid_raw_prod :: "'a \<times> 'b \<Rightarrow> sprop" where
    "valid_raw_prod \<equiv> \<lambda>(x::'a,y::'b). valid_raw x \<and>\<^sub>s valid_raw y"
  definition pcore_prod :: "'a\<times>'b \<Rightarrow> ('a\<times>'b) option" where
    "pcore_prod \<equiv> \<lambda>(x,y). case pcore x of Some x' \<Rightarrow> (case pcore y of Some y' \<Rightarrow> Some (x',y') 
      | None \<Rightarrow> None) | None \<Rightarrow> None"
  definition op_prod :: "'a\<times>'b \<Rightarrow> 'a\<times>'b \<Rightarrow> 'a\<times>'b" where 
    "op_prod \<equiv> \<lambda>(x,y) (a,b). (x \<cdot> a,y \<cdot> b)"
instance proof
show "non_expansive (valid_raw::'a \<times> 'b \<Rightarrow> sprop)"
  by (rule non_expansiveI;auto simp: valid_raw_prod_def sprop_conj.rep_eq n_equiv_sprop_def ) 
  (metis ofe_mono ofe_sym n_valid_ne)+
next 
show "non_expansive (pcore::'a\<times>'b \<Rightarrow> ('a\<times>'b) option)"
  by (rule non_expansiveI; auto simp: pcore_prod_def n_equiv_option_def split: option.splits)
  (metis n_equiv_option_def pcore_ne option.distinct(1) option.sel)+
next
show "non_expansive2 (op::'a\<times>'b \<Rightarrow> 'a\<times>'b \<Rightarrow> 'a\<times>'b)"
  by (rule non_expansive2I) (auto simp: op_prod_def)
next
fix a b c :: "'a\<times>'b"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)"
  by (auto simp: op_prod_def camera_assoc split: prod.splits)
next
fix a b :: "'a\<times>'b"
show "a \<cdot> b = b \<cdot> a"
  by (auto simp: op_prod_def camera_comm split: prod.splits)
next
fix a a' :: "'a\<times>'b"
show "pcore a = Some a' \<Longrightarrow>  a' \<cdot> a = a"
  by (auto simp: pcore_prod_def op_prod_def camera_pcore_id split: prod.splits option.splits)
next
fix a a' :: "'a\<times>'b"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a"
  by (auto simp: pcore_prod_def camera_pcore_idem split: option.splits prod.splits)
next
fix a a' b :: "'a\<times>'b"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  by (auto simp: pcore_prod_def op_prod_def split: prod.splits option.splits)
  (metis camera_pcore_mono option.simps(1,3))+
next
fix a b :: "'a\<times>'b"
fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  by (transfer; auto simp: valid_raw_prod_def sprop_conj.rep_eq op_prod_def camera_valid_op 
    split: prod.splits)
next
fix a b c :: "'a\<times>'b"
fix n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b \<cdot> c) \<Longrightarrow> 
  \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c"
  by (transfer; auto simp: valid_raw_prod_def sprop_conj.rep_eq op_prod_def split: prod.splits)
    (metis camera_extend)
qed
end
lemma n_incl_prod[simp]: "n_incl n (a,b) (x,y) = (n_incl n a x \<and> n_incl n b y)"
  by (auto simp: n_incl_def op_prod_def)

lemma prod_valid_def: "valid (x,y) \<longleftrightarrow> valid x \<and> valid y"
  by (auto simp: valid_raw_prod_def valid_def sprop_conj.rep_eq)

lemma prod_validI: "\<lbrakk>valid x; valid y\<rbrakk> \<Longrightarrow> valid (x,y)"
  by (auto simp: valid_raw_prod_def valid_def sprop_conj.rep_eq)

lemma prod_n_valid_def: "n_valid (x,y) n \<longleftrightarrow> n_valid x n \<and> n_valid y n"
  by (auto simp: valid_raw_prod_def valid_def sprop_conj.rep_eq)

lemma prod_n_valid_fun_def: "n_valid (x,y) = (\<lambda>n. n_valid x n \<and> n_valid y n)"
  using prod_n_valid_def by auto

lemma prod_n_valid_snd: "n_valid (x,y) n \<Longrightarrow> n_valid y n"
  using prod_n_valid_fun_def by metis
  
instance prod :: (core_id,core_id) core_id by standard (auto simp: pcore_prod_def pcore_id)

instance prod :: (dcamera,dcamera) dcamera 
  apply (standard; auto simp: valid_raw_prod_def valid_def sprop_conj.rep_eq)
  using d_valid[simplified valid_def] by blast+

lemma prod_dcamera_val [intro!]: "\<lbrakk>dcamera_val x; dcamera_val y\<rbrakk> \<Longrightarrow> dcamera_val (x,y)"
  apply (auto simp: dcamera_val_def discrete_val_def valid_def)
  using prod_n_valid_def by blast+

instantiation prod :: (ucamera,ucamera) ucamera begin
definition \<epsilon>_prod :: "'a \<times> 'b" where [simp]: "\<epsilon>_prod = (\<epsilon>,\<epsilon>)"
instance by standard 
  (auto simp: valid_raw_prod_def sprop_conj.rep_eq pcore_prod_def op_prod_def valid_def 
    \<epsilon>_left_id \<epsilon>_pcore \<epsilon>_valid[unfolded valid_def]) 
end

lemma prod_pcore_id_pred: 
  "pcore_id_pred (a::'a::ucamera,b::'b::ucamera) \<longleftrightarrow> pcore_id_pred a \<and> pcore_id_pred b"
  by (auto simp: pcore_id_pred_def pcore_prod_def split: option.splits)

instance prod :: (ducamera,ducamera) ducamera ..

subsubsection \<open> Extended sum type \<close>
fun sum_pcore :: "'a::camera+\<^sub>e'b::camera \<Rightarrow> ('a+\<^sub>e'b) option" where
  "sum_pcore (Inl x) = (case pcore x of Some x' \<Rightarrow> Some (Inl x') | None \<Rightarrow> None)"
| "sum_pcore (Inr x) = (case pcore x of Some x' \<Rightarrow> Some (Inr x') | None \<Rightarrow> None)"
| "sum_pcore sum_ext.Inv = Some sum_ext.Inv"  

lemma sum_pcore_ne: "non_expansive sum_pcore"
proof (rule non_expansiveI)
fix n x y
assume "n_equiv n x (y::('a,'b) sum_ext)"
then show "n_equiv n (sum_pcore x) (sum_pcore y)" 
  by (cases x y rule: sum_ex2; auto simp: ofe_refl ofe_sym n_equiv_option_def split: option.splits)
  (metis option.distinct(1) option.sel pcore_ne n_equiv_option_def)+
qed

instantiation sum_ext :: (camera,camera) camera begin
  definition valid_raw_sum_ext :: "('a,'b) sum_ext \<Rightarrow> sprop" where
    "valid_raw_sum_ext s \<equiv> case s of (Inl a) \<Rightarrow> valid_raw a | Inr b \<Rightarrow> valid_raw b | sum_ext.Inv \<Rightarrow> sFalse"
  definition "pcore_sum_ext \<equiv> sum_pcore"
  definition op_sum_ext :: "('a,'b) sum_ext \<Rightarrow> ('a,'b) sum_ext \<Rightarrow> ('a,'b) sum_ext" where
    "op_sum_ext x y = (case (x,y) of (Inl x', Inl y') \<Rightarrow> Inl (x' \<cdot> y') 
    | (Inr x', Inr y') \<Rightarrow> Inr (x' \<cdot> y') | _ \<Rightarrow> sum_ext.Inv)"
instance proof
show "non_expansive (valid_raw::('a,'b) sum_ext \<Rightarrow> sprop)"
  by (rule non_expansiveI;auto simp: valid_raw_sum_ext_def split: sum_ext.splits)
  (auto simp: n_equiv_sprop_def)
next
show "non_expansive (pcore::('a,'b) sum_ext \<Rightarrow> ('a,'b) sum_ext option)"
  by (simp add: sum_pcore_ne pcore_sum_ext_def)
next
show "non_expansive2 (op::('a,'b) sum_ext \<Rightarrow> ('a,'b) sum_ext \<Rightarrow> ('a,'b) sum_ext)"
proof (rule non_expansive2I)
fix x y a b :: "('a,'b) sum_ext"
fix n
assume " n_equiv n x y" "n_equiv n a b"
then show "n_equiv n (x \<cdot> a) (y \<cdot> b)"
  by (cases x y a b rule: sum_ex4) (auto simp: ofe_refl ofe_sym op_sum_ext_def)
qed
next
fix a b c :: "('a,'b) sum_ext"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" 
  by (cases a b c rule: sum_ex3) (auto simp: op_sum_ext_def camera_assoc)
next
fix a b :: "('a,'b) sum_ext"
show "a \<cdot> b = b \<cdot> a" by (cases a b rule: sum_ex2) (auto simp: op_sum_ext_def camera_comm)
next
fix a a' :: "('a,'b) sum_ext"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" by (cases a a' rule: sum_ex2) 
  (auto simp: pcore_sum_ext_def op_sum_ext_def camera_pcore_id split: option.splits)
next
fix a a' :: "('a,'b) sum_ext"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a" by (cases a a' rule: sum_ex2)
  (auto simp: pcore_sum_ext_def camera_pcore_idem split: option.splits)
next
fix a a' b :: "('a,'b) sum_ext"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  apply (cases a a' b rule: sum_ex3) 
  apply (simp_all add: pcore_sum_ext_def op_sum_ext_def split: option.splits sum_ext.splits)
  apply (metis camera_pcore_mono option.inject sum_ext.inject(1) sum_ext.simps(4) sum_ext.simps(6))
  apply blast+
  apply (metis camera_pcore_mono option.inject sum_ext.distinct(5) sum_ext.inject(2) sum_ext.simps(4))
  by blast+
next
fix a b :: "('a,'b) sum_ext"
fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n" by (cases a; cases b) 
  (auto simp: valid_raw_sum_ext_def op_sum_ext_def camera_valid_op split: sum_ext.splits)
next
fix a b c :: "('a,'b) sum_ext"
fix n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b \<cdot> c) \<Longrightarrow> 
  \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c" apply (cases a b c rule: sum_ex3) 
  apply (simp_all add: valid_raw_sum_ext_def op_sum_ext_def split: sum_ext.splits)
  using camera_extend by fast+
qed
end

instance sum_ext :: (dcamera,dcamera) dcamera
  apply (standard; auto simp: valid_raw_sum_ext_def valid_def split: sum_ext.splits)
  using d_valid[simplified valid_def] by blast+

instance sum_ext :: (core_id,core_id) core_id 
proof
fix a :: "('a,'b) sum_ext"
show "pcore a = Some a" by (cases a) (auto simp: pcore_sum_ext_def pcore_id)
qed

lemma sum_update_l: "a\<leadsto>b \<Longrightarrow> (Inl a) \<leadsto> Inl b"
by (auto simp: camera_upd_def op_sum_ext_def valid_def valid_raw_sum_ext_def opM_def
  split: sum_ext.splits option.splits)

lemma sum_update_r: "a\<leadsto>b \<Longrightarrow> (Inr a) \<leadsto> Inr b"
by (auto simp: camera_upd_def op_sum_ext_def valid_def valid_raw_sum_ext_def opM_def
  split: sum_ext.splits option.splits)

lemma sum_swap_l: "\<lbrakk>\<forall>c n. \<not> n_valid (op a c) n; valid b\<rbrakk> \<Longrightarrow> (Inl a) \<leadsto> Inr b"
by (auto simp: camera_upd_def op_sum_ext_def valid_def valid_raw_sum_ext_def opM_def
  split: sum_ext.splits option.splits) 

lemma sum_swap_r: "\<lbrakk>\<forall>c n. \<not> n_valid (op a c) n; valid b\<rbrakk> \<Longrightarrow> (Inr a) \<leadsto> Inl b"
by (auto simp: camera_upd_def op_sum_ext_def valid_def valid_raw_sum_ext_def opM_def
  split: sum_ext.splits option.splits)

subsubsection \<open> Agreement camera combinator\<close>
lemma map_ag_ne: "non_expansive f \<Longrightarrow> non_expansive (map_ag f)"
apply (auto simp: non_expansive_def map_ag_def n_equiv_ag.rep_eq)
apply (metis imageE image_abs_ag(1) rev_image_eqI)
by (metis imageE image_abs_ag(1) rev_image_eqI)

instantiation ag :: (ofe) camera begin
lift_definition valid_raw_ag :: "'a ag \<Rightarrow> sprop" is
  "\<lambda>a n. \<exists>b. a={b} \<or> (\<forall>x y. (x\<in>a\<and>y\<in>a) \<longrightarrow> n_equiv n x y)" by (metis ofe_mono)
definition "pcore_ag (a::'a ag) \<equiv> Some a"
lift_definition op_ag :: "'a ag \<Rightarrow> 'a ag \<Rightarrow> 'a ag" is "(\<union>)" by simp
instance proof
show "non_expansive (valid_raw::'a ag \<Rightarrow> sprop)"
  apply (rule non_expansiveI; auto simp: valid_raw_ag.rep_eq n_equiv_ag.rep_eq n_equiv_sprop_def)
  by (metis ofe_mono ofe_sym ofe_trans)+
next
show "non_expansive (pcore::'a ag \<Rightarrow> 'a ag option)"
  by (rule non_expansiveI) (auto simp: pcore_ag_def n_equiv_option_def)
next
show "non_expansive2 (op::'a ag \<Rightarrow> 'a ag \<Rightarrow> 'a ag)"
  by (rule non_expansive2I) (auto simp: op_ag.rep_eq n_equiv_ag_def)
next
fix a b c :: "'a ag"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by transfer auto
next
fix a b :: "'a ag"
show "a \<cdot> b = b \<cdot> a" by transfer auto
next
fix a a' :: "'a ag"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" by (auto simp: pcore_ag_def; transfer; simp)
next
fix a a' :: "'a ag"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a" by (simp add: pcore_ag_def)
next
fix a a' b :: "'a ag"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  by (auto simp: pcore_ag_def)
next
fix a b :: "'a ag"
fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  by transfer (auto simp: Un_singleton_iff)
next
fix a b c :: "'a ag"
fix n
assume assms: "n_equiv n a (b \<cdot> c)" "Rep_sprop (valid_raw a) n"
have valid_equiv: "Rep_sprop (valid_raw (x\<cdot>y)) n \<Longrightarrow> n_equiv n x (y::'a ag)" for x y
  apply transfer
  apply simp_all
  by (metis equals0I ofe_refl singleton_Un_iff)
from assms have "Rep_sprop (valid_raw (b\<cdot>c)) n"
  by transfer (metis empty_iff insert_iff ofe_sym ofe_trans)
from assms have "n_equiv n a b" by (transfer;auto;meson UnI1 ofe_trans)
moreover from assms have "n_equiv n a c" by (transfer;auto;meson UnI2 ofe_trans)
moreover have "a=a\<cdot>a" by (auto simp: op_ag_def Rep_ag_inverse)
ultimately show "\<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c"
  by blast
qed
end

instance ag :: (discrete) dcamera
  by standard (auto simp: valid_raw_ag.rep_eq valid_def d_equiv split: option.splits)
  
instance ag :: (ofe) core_id by standard (auto simp: pcore_ag_def)

lemma map_ag_op: "n_equiv n (map_ag f (x \<cdot> y)) (map_ag f x \<cdot> map_ag f y)"
  by (auto simp: map_ag.rep_eq op_ag.rep_eq n_equiv_ag.rep_eq)
    (meson Un_iff ofe_refl rev_image_eqI)+

lemma to_ag_valid: "valid (to_ag a)"
  by (auto simp: to_ag.rep_eq valid_def valid_raw_ag.rep_eq)
lemma to_ag_n_valid: "n_valid (to_ag a) n" using to_ag_valid valid_def by auto
    
lemma to_ag_op: "(to_ag a) = b\<cdot>c \<Longrightarrow> (b=to_ag a) \<and> (c=to_ag a)"
proof -
  assume assm: "to_ag a = b\<cdot>c"
  then have "{a} = Rep_ag b \<union> Rep_ag c" by (metis assm op_ag.rep_eq to_ag.rep_eq)
  then have "Rep_ag b = {a}" "Rep_ag c = {a}" using Rep_ag by fast+
  then show "(b=to_ag a) \<and> (c=to_ag a)" by (metis Rep_ag_inverse to_ag.abs_eq)
qed

lemma to_ag_op_refl: "(to_ag a) \<cdot> (to_ag a) = to_ag a" by transfer simp

lemma ag_idem: "((a::'a::ofe ag) \<cdot> a) = a"
  by (simp add: Rep_ag_inverse op_ag_def)

lemma ag_incl: "incl (a::'a::ofe ag) b \<longleftrightarrow> b = (a\<cdot>b)"
  apply (simp add: incl_def op_ag_def)
  by (metis Rep_ag_inverse op_ag.rep_eq sup.left_idem)

lemma to_ag_uninj: "n_valid a n \<Longrightarrow> \<exists>b. n_equiv n (to_ag b) a"
  apply (auto simp: valid_def valid_raw_ag.rep_eq n_equiv_ag.rep_eq to_ag.rep_eq)
  using ofe_refl apply blast
  by (metis (no_types, opaque_lifting) Rep_ag_inverse equals0I op_ag.rep_eq singletonI 
    sup_bot.left_neutral to_ag.rep_eq to_ag_op)
 
lemma d_valid_ag: "valid (a::('a::discrete) ag) \<Longrightarrow> \<exists>b. a = to_ag b"
  apply (simp add: valid_def valid_raw_ag.rep_eq to_ag_def d_equiv )
  by (metis (mono_tags, lifting) Rep_ag_inverse image_ag image_empty is_singletonE is_singletonI' 
    mem_Collect_eq)

lemma ag_agree: "n_valid ((a::('a::ofe) ag) \<cdot> b) n \<Longrightarrow> n_equiv n a b"
  apply (simp add: valid_raw_ag.rep_eq op_ag.rep_eq n_equiv_ag.rep_eq)
  apply (rule conjI)
  apply (smt (verit, del_insts) Rep_ag Rep_ag_inverse all_not_in_conv mem_Collect_eq ofe_eq_limit op_ag.rep_eq to_ag.abs_eq to_ag_op)
  by (smt (verit, del_insts) Rep_ag Rep_ag_inject ex_in_conv mem_Collect_eq ofe_eq_limit op_ag.rep_eq to_ag.rep_eq to_ag_op)

lemma ag_valid_n_incl: "\<lbrakk>n_valid b n; n_incl n a b\<rbrakk> \<Longrightarrow> n_equiv n a (b::'a::ofe ag)"
proof -
  assume assms: "n_valid b n" "n_incl n a b"
  then obtain c where "n_equiv n b (a\<cdot>c)" using n_incl_def by blast
  with ag_agree[OF n_valid_ne[OF this assms(1)]]  
  show ?thesis using ag_idem by (metis ofe_sym ofe_trans op_ne)
qed
  
lemma d_ag_agree: "valid ((a::('a::discrete) ag) \<cdot> b) \<Longrightarrow> a=b"
  by (auto simp: n_equiv_ag.rep_eq valid_def d_equiv) (metis ag_agree d_equiv)

lemma ag_incl_equiv: "n_equiv n a b \<Longrightarrow> n_incl n a (b::'a::ofe ag)"
  by (metis ag_idem n_incl_def ofe_sym)

lemma to_ag_n_incl: "\<lbrakk>n_equiv n a b; n_incl n (to_ag a) c\<rbrakk> \<Longrightarrow> n_incl n (to_ag b) c"
  apply (simp add: n_incl_def to_ag.rep_eq n_equiv_ag.rep_eq op_ag.rep_eq)
  using ofe_trans by blast

subsubsection \<open> Exclusive camera functor\<close>
instantiation ex :: (ofe) camera begin
definition valid_raw_ex :: "'a ex \<Rightarrow> sprop" where 
  "valid_raw_ex x = (case x of Ex _ \<Rightarrow> sTrue | ex.Inv \<Rightarrow> sFalse)" 
definition pcore_ex :: "'a ex \<Rightarrow> 'a ex option" where
  "pcore_ex x = (case x of Ex _ \<Rightarrow> None | ex.Inv \<Rightarrow> Some ex.Inv)"
definition op_ex :: "'a ex \<Rightarrow> 'a ex \<Rightarrow> 'a ex" where [simp]: "op_ex _ _ = ex.Inv"
instance proof
show "non_expansive (valid_raw::'a ex \<Rightarrow> sprop)"
  by (rule non_expansiveI) (auto simp: valid_raw_ex_def n_equiv_sprop_def split: ex.splits)
next
show "non_expansive (pcore::'a ex \<Rightarrow> 'a ex option)"
  by (rule non_expansiveI) (auto simp: pcore_ex_def n_equiv_option_def split: ex.splits)
next
show "non_expansive2 (op::'a ex \<Rightarrow> 'a ex \<Rightarrow> 'a ex)" by (rule non_expansive2I) simp
qed (auto simp: valid_raw_ex_def pcore_ex_def split: ex.splits)
end

lemma ex_inv_invalid [simp]: "\<not> (valid ex.Inv)"
  by (auto simp: valid_def valid_raw_ex_def)

instance ex :: (discrete) dcamera by (standard; auto simp: valid_raw_ex_def valid_def split: ex.splits)

subsubsection \<open> Authoritative camera functor \<close>
lemma valid_raw_auth_aux: "(\<lambda>n. \<exists>c. x = ex.Ex c \<and> n_incl n (y::'a::ucamera) c \<and> n_valid c n) \<in> 
  {s. \<forall>n m. m \<le> n \<longrightarrow> s n \<longrightarrow> s m}" apply (simp add: n_incl_def) using ofe_mono by fastforce

lemma valid_raw_auth_aux2: "(\<lambda>n. a = None \<and> n_valid b n \<or> (\<exists>c. a = Some (ex.Ex c) \<and> n_incl n b c \<and> n_valid c n))
  \<in> {s. \<forall>n m. m \<le> n \<longrightarrow> s n \<longrightarrow> s m}"
  by (cases a;auto simp: n_valid_ne) (metis camera_n_incl_le)
  
instantiation auth :: (ucamera) camera begin
definition valid_raw_auth :: "'a auth \<Rightarrow> sprop" where
  "valid_raw_auth a = (case a of Auth (x,b) \<Rightarrow> Abs_sprop (\<lambda>n. (x=None\<and>Rep_sprop (valid_raw b) n) \<or> 
    (\<exists>c. x=Some(Ex c) \<and> n_incl n b c \<and> Rep_sprop (valid_raw c) n)))"
definition pcore_auth :: "'a auth \<Rightarrow> 'a auth option" where
  "pcore_auth a = (case a of Auth (_,b) \<Rightarrow> Some (Auth (None,core b)))"
definition op_auth :: "'a auth \<Rightarrow> 'a auth \<Rightarrow> 'a auth" where
  "op_auth a b = (case a of Auth (x1,b1) \<Rightarrow> case b of Auth (x2,b2) \<Rightarrow> Auth (op (x1,b1) (x2,b2)))"
instance proof  
show "non_expansive (valid_raw::'a auth \<Rightarrow> sprop)"
apply (rule non_expansiveI)
apply (auto simp: valid_raw_auth_def n_equiv_sprop_def n_equiv_option_def split: auth.splits)
subgoal for n b b' m a a' proof -
assume assms: "m\<le>n" "Rep_sprop (Abs_sprop (\<lambda>n. \<exists>c. a = ex.Ex c \<and> n_incl n b c \<and> n_valid c n)) m"
  "n_equiv n b b'" "n_equiv n a a'"
from Abs_sprop_inverse[OF valid_raw_auth_aux, of a b] assms(2) have "\<exists>c. a = ex.Ex c \<and> n_incl m b c \<and> n_valid c m" by simp
with assms (1,3,4) have "\<exists>c. a' = ex.Ex c \<and> n_incl m b' c \<and> n_valid c m" 
apply (simp add: n_incl_def)
by (smt (verit, ccfv_threshold) dual_order.eq_iff n_equiv_ex.elims(1) n_equiv_ex.simps(1) ne_sprop_weaken ofe_mono ofe_sym ofe_trans op_equiv_subst valid_raw_non_expansive)
then show "Rep_sprop (Abs_sprop (\<lambda>n. \<exists>c. a' = ex.Ex c \<and> n_incl n b' c \<and> n_valid c n)) m"
using Abs_sprop_inverse[OF valid_raw_auth_aux, of a' b'] by simp qed
apply (meson n_valid_ne ofe_mono)
apply (simp add: \<open>\<And>n m b' b a' a. \<lbrakk>m \<le> n; Rep_sprop (Abs_sprop (\<lambda>n. \<exists>c. a = ex.Ex c \<and> n_incl n b c \<and> n_valid c n)) m; n_equiv n b b'; n_equiv n a a'\<rbrakk> \<Longrightarrow> Rep_sprop (Abs_sprop (\<lambda>n. \<exists>c. a' = ex.Ex c \<and> n_incl n b' c \<and> n_valid c n)) m\<close> ofe_sym)
by (meson n_equiv_sprop_def non_expansiveE valid_raw_non_expansive)
next
show "non_expansive (pcore::'a auth \<Rightarrow> 'a auth option)" by (rule non_expansiveI)
  (auto simp: pcore_auth_def n_equiv_option_def core_ne[unfolded non_expansive_def] split: auth.splits)
next
show "non_expansive2 (op::'a auth \<Rightarrow> 'a auth \<Rightarrow> 'a auth)"
  by (rule non_expansive2I) (auto simp: op_auth_def op_prod_def split: auth.splits)
next
fix a b c :: "'a auth"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (auto simp: op_auth_def camera_assoc split: auth.splits)
next
fix a b :: "'a auth"
show "a \<cdot> b = b \<cdot> a" by (auto simp: op_auth_def camera_comm split: auth.splits)
next
fix a a' :: "'a auth"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" 
  apply (simp add: pcore_auth_def op_auth_def op_prod_def split: auth.splits prod.splits)
  by (metis Pair_inject \<epsilon>_left_id \<epsilon>_option_def auth.inject camera_core_id)
next
fix a a' :: "'a auth"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a"
  by (auto simp: pcore_auth_def camera_pcore_idem core_def total_pcore split: auth.splits)
next
fix a a' b :: "'a auth"
assume assms: "pcore a = Some a'" "\<exists>c. b = a \<cdot> c"
obtain c d where a:"a = Auth (c,d)" using auth.exhaust by auto
then have a': "a' = Auth (None, core d)" using assms(1) pcore_auth_def by force
from assms(2) a obtain x y where c: "b = Auth ((c,d)\<cdot>(x,y))" apply (simp add: op_auth_def split: auth.splits)
  by (metis auth.exhaust surj_pair)
then have b': "pcore b = Some (Auth (None, core (d\<cdot>y)))"
  by (auto simp: pcore_auth_def core_def op_prod_def split: prod.splits)
obtain z where z:"core(d\<cdot>y) = core d \<cdot> z" using camera_pcore_mono[of d _ "d\<cdot>y"] total_pcore
  by (meson camera_core_mono incl_def)
with a' b' have "Auth (None, core (d\<cdot>y)) = a' \<cdot> Auth (None, z)" 
    by (auto simp: op_auth_def op_prod_def op_option_def)
with b' show "\<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)" by auto
next
fix a b :: "'a auth"
fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  apply (auto simp: valid_raw_auth_def op_auth_def op_prod_def op_option_def Abs_sprop_inverse[OF valid_raw_auth_aux2] split: auth.splits)
  using option_op.elims apply force
  apply (smt (verit, best) camera_assoc ex.distinct(1) n_incl_def op_ex_def option.sel option_op.elims)
  using camera_valid_op apply blast
  by (meson camera_valid_op n_incl_def n_valid_ne)
next
fix a b c :: "'a auth"
fix n
assume assms: "Rep_sprop (valid_raw a) n" "n_equiv n a (b \<cdot> c)"
obtain a1 a2 where a: "a=Auth (a1,a2)" using auth.exhaust by auto
obtain b1 b2 where b: "b=Auth (b1,b2)" using auth.exhaust by auto
obtain c1 c2 where c: "c=Auth (c1,c2)" using auth.exhaust by auto
from assms(2) a b c have n: "n_equiv n a1 (b1\<cdot>c1)" "n_equiv n a2 (b2\<cdot>c2)" 
  by (auto simp: op_auth_def op_prod_def)
from assms(1) a have a_val: "(a1=None\<and>Rep_sprop (valid_raw a2) n) \<or> 
  (\<exists>c. a1=Some(Ex c) \<and> n_incl n a2 c \<and> Rep_sprop (valid_raw c) n)"
  by (auto simp: valid_raw_auth_def Abs_sprop_inverse[OF valid_raw_auth_aux2] split: auth.splits) 
{
  then have "a1=None \<Longrightarrow> \<exists>d2 e2. (a2=d2\<cdot>e2 \<and> n_equiv n d2 b2 \<and> n_equiv n e2 c2)"
    using camera_extend n(2) by blast
  then obtain d2 e2 where "a1=None \<Longrightarrow> (a2=d2\<cdot>e2 \<and> n_equiv n d2 b2 \<and> n_equiv n e2 c2)" by blast
  then have "a1=None \<Longrightarrow> a=Auth(a1,d2)\<cdot>Auth(a1,e2) \<and> n_equiv n (Auth(a1,d2)) b \<and> n_equiv n (Auth(a1,e2)) c"
    using a b c n apply (simp add: op_auth_def op_prod_def op_option_def)
    by (metis n_equiv_option_def not_Some_eq option_op.elims)
  then have "a1=None \<Longrightarrow> \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c" by blast
}
moreover {
  fix x
  from a_val have x: "a1=Some(Ex x) \<Longrightarrow> n_incl n a2 x \<and> Rep_sprop (valid_raw x) n" by simp
  then have "a1=Some(Ex x) \<Longrightarrow> Rep_sprop (valid_raw a1) n" 
    by (auto simp: valid_raw_option_def valid_raw_ex_def split: option.splits ex.splits)
  then have "a1=Some(Ex x) \<Longrightarrow> \<exists>d1 e1. (a1=d1\<cdot>e1 \<and> n_equiv n d1 b1 \<and> n_equiv n e1 c1)"
    using n(1) camera_extend by blast
  then obtain d1 e1 where a1: "a1=Some(Ex x) \<Longrightarrow> (a1=d1\<cdot>e1 \<and> n_equiv n d1 b1 \<and> n_equiv n e1 c1)" 
    by blast
  from x have "a1=Some(Ex x) \<Longrightarrow> Rep_sprop (valid_raw a2) n" using n_valid_incl_subst[of n a2 x \<epsilon> n]
    by (metis \<epsilon>_left_id camera_comm order_refl)
  then have "a1=Some(Ex x) \<Longrightarrow> \<exists>d2 e2. (a2=d2\<cdot>e2 \<and> n_equiv n d2 b2 \<and> n_equiv n e2 c2)"
    using camera_extend n(2) by blast  
  then obtain d2 e2 where "a1=Some(Ex x) \<Longrightarrow> (a2=d2\<cdot>e2 \<and> n_equiv n d2 b2 \<and> n_equiv n e2 c2)" by blast
  with a1 a b c have "a1=Some(Ex x) \<Longrightarrow> a=Auth(d1,d2)\<cdot>Auth(e1,e2)\<and> n_equiv n (Auth(d1,d2)) b \<and> n_equiv n (Auth(e1,e2)) c"
    by (auto simp: op_auth_def op_prod_def)
  then have "a1=Some(Ex x) \<Longrightarrow> \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c" by blast
}
ultimately show "\<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c"
  using a apply (cases a1) apply blast using a_val by blast
qed
end

instance auth :: (ducamera) dcamera 
  apply standard 
  apply (simp add: valid_raw_auth_def Abs_sprop_inverse[OF valid_raw_auth_aux2] valid_def n_incl_def 
    split: auth.splits)
  by (auto simp: d_equiv dcamera_valid_iff[symmetric])

instantiation auth :: (ucamera) ucamera begin
definition "\<epsilon>_auth \<equiv> Auth (None, \<epsilon>)"
instance proof (standard)
have "valid (\<epsilon>::'a auth) = valid (Auth (None, \<epsilon>::'a))" by (simp add: \<epsilon>_auth_def)
also have "... = (\<forall>n. Rep_sprop (valid_raw (Auth (None, \<epsilon>::'a))) n)" by (simp add: valid_def)
also have "... = (\<forall>n. Rep_sprop (Abs_sprop (\<lambda>n. Rep_sprop (valid_raw  (\<epsilon>::'a)) n)) n)"
  by (auto simp:  valid_raw_auth_def)
also have "... = (\<forall>n. Rep_sprop (valid_raw (\<epsilon>::'a)) n)" using Rep_sprop_inverse by simp
also have "... = valid (\<epsilon>::'a)" using valid_def  by metis
also have "... = True" using \<epsilon>_valid by simp
finally show "valid (\<epsilon>::'a auth)" by simp
next
fix a :: "'a auth"
show "op \<epsilon> a = a" apply (simp add: op_auth_def \<epsilon>_auth_def op_prod_def split: auth.splits)
  using \<epsilon>_left_id[simplified ] \<epsilon>_option_def by metis+
next
show "pcore (\<epsilon>::'a auth) = Some \<epsilon>" by (auto simp: \<epsilon>_auth_def pcore_auth_def \<epsilon>_core split: auth.splits)
qed
end

instance auth :: (ducamera) ducamera ..

abbreviation full :: "'m::ucamera \<Rightarrow> 'm auth" where "full \<equiv> \<lambda>a::'m. Auth (Some (Ex a), \<epsilon>)"

lemma fragm_core_id: "pcore_id_pred (fragm (a::'a::{ucamera,core_id}))"
  by (auto simp: core_id_pred core_def pcore_auth_def core_id[unfolded core_def, simplified] 
    split: auth.splits)

lemma auth_frag_op: "fragm (a\<cdot>b) = fragm a \<cdot> fragm b"
  by (auto simp: op_auth_def op_prod_def op_option_def)

lemma auth_comb_opL:"(comb a b) \<cdot> (fragm c) = comb a (b\<cdot>c)"
  by (auto simp: op_auth_def op_prod_def op_option_def)

lemma auth_comb_opR:"(fragm c) \<cdot> (comb a b) = comb a (b\<cdot>c)"
  by (auto simp: op_auth_def op_prod_def op_option_def camera_comm)  
  
lemma auth_valid_def [simp]: 
  "n_valid (Auth (a,b)::('m::ucamera) auth) n \<equiv> (a = None \<and> n_valid b n \<or> (\<exists>c. a = Some (ex.Ex c) 
    \<and> n_incl n b c \<and> n_valid c n))"
  by (auto simp: valid_raw_auth_def Abs_sprop_inverse[OF valid_raw_auth_aux2])

lemma n_incl_fragm[simp]: "n_incl n (fragm a) (Auth (b,c)) = n_incl n a c"
proof (standard; unfold n_incl_def)
  assume "\<exists>ca. n_equiv n (Auth (b, c)) (fragm a \<cdot> ca)"
  then obtain d e where "n_equiv n (Auth (b, c)) (fragm a \<cdot> (Auth (d,e)))"
    by (metis auth.exhaust old.prod.exhaust)
  then have "n_equiv n (Auth (b, c)) (Auth (None\<cdot>d,a\<cdot>e))"
    by (auto simp: op_auth_def op_prod_def)
  then have "n_equiv n c (a\<cdot>e)" by auto
  then show "\<exists>ca. n_equiv n c (a \<cdot> ca)" by auto
next
  assume "\<exists>ca. n_equiv n c (a \<cdot> ca)"
  then obtain d where "n_equiv n c (a \<cdot> d)" by blast
  moreover have "n_equiv n b (None\<cdot>b)" by (metis \<epsilon>_left_id \<epsilon>_option_def ofe_refl)
  ultimately have "n_equiv n (Auth (b,c)) (Auth ((None\<cdot>b),(a\<cdot>d)))"
    by (auto simp: op_auth_def)
  then have "n_equiv n (Auth (b,c)) (fragm a \<cdot> (Auth (b,d)))"
    by (auto simp: op_auth_def op_prod_def)  
  then show "\<exists>ca. n_equiv n (Auth (b, c)) (fragm a \<cdot> ca)" by blast
qed

lemma auth_update_alloc: "(a,f)\<leadsto>\<^sub>L(a',f') \<Longrightarrow> (comb a f) \<leadsto> comb a' f'"
apply (auto simp: lup_def camera_upd_def valid_def op_auth_def op_prod_def opM_def 
  split: auth.splits option.splits)
using n_incl_def apply blast
using n_incl_def apply blast
apply (metis op_option_def option.simps(3) option_opE)
apply (metis op_option_def option.simps(3) option_opE)
apply (auto simp: op_option_def n_incl_def)
proof -
fix n aa b c ca
assume assms: "\<forall>n c. n_valid a n \<and> n_equiv n a (f \<cdot> c) \<longrightarrow> n_valid a' n \<and> n_equiv n a' (f' \<cdot> c)"
  "option_op (Some (ex.Ex a)) aa = Some (ex.Ex c)" "n_valid c n" 
  "\<forall>c. (\<exists>ca. n_equiv n c (f' \<cdot> b \<cdot> ca)) \<longrightarrow> option_op (Some (ex.Ex a')) aa = Some (ex.Ex c) \<longrightarrow>
    \<not> n_valid c n" "n_equiv n c (f \<cdot> b \<cdot> ca)"
from this(2) have 1:"c=a \<and> aa=None" by (cases aa) auto
with assms(1,3,5) have 2:"n_valid a' n \<and> n_equiv n a' (f' \<cdot> b \<cdot> ca)" by (auto simp: camera_assoc)
moreover from 1 have "option_op (Some (ex.Ex a')) aa = Some (ex.Ex a')" by simp
ultimately have "\<not> n_valid a' n" using assms(4) by simp
with 2 have False by simp
then show "option_op (Some (ex.Ex a')) aa = None" by simp
next
fix n aa b c ca
assume assms: "\<forall>n c. n_valid a n \<and> n_equiv n a (f \<cdot> c) \<longrightarrow> n_valid a' n \<and> n_equiv n a' (f' \<cdot> c)"
  "option_op (Some (ex.Ex a)) aa = Some (ex.Ex c)" "n_valid c n" 
  "\<forall>c. (\<exists>ca. n_equiv n c (f' \<cdot> b \<cdot> ca)) \<longrightarrow> option_op (Some (ex.Ex a')) aa = Some (ex.Ex c) \<longrightarrow>
    \<not> n_valid c n" "n_equiv n c (f \<cdot> b \<cdot> ca)"
from this(2) have 1:"c=a \<and> aa=None" by (cases aa) auto
with assms(1,3,5) have 2:"n_valid a' n \<and> n_equiv n a' (f' \<cdot> b \<cdot> ca)" by (auto simp: camera_assoc)
moreover from 1 have "option_op (Some (ex.Ex a')) aa = Some (ex.Ex a')" by simp
ultimately have "\<not> n_valid a' n" using assms(4) by simp
with 2 have False by simp
then show "n_valid (f' \<cdot> b) n " by simp
qed

subsubsection \<open> Function camera \<close>

text \<open>
  As maps are only functions to options and thus can't directly be declared as class instances, 
  we need a bit of class magic. Based on ideas from the AFP entry Separation Logic Algebra.
\<close>
lemma pcore_op_opt[simp]: "(case pcore x of None \<Rightarrow> \<epsilon> | Some a \<Rightarrow> a) \<cdot> (x::'b::ucamera) = x"
  apply (cases "pcore x")
  apply (simp_all add: camera_pcore_id)
  using \<epsilon>_left_id by metis
 
instantiation "fun" :: (type, ucamera) camera begin
lift_definition valid_raw_fun :: "('a\<Rightarrow>'b) \<Rightarrow> sprop" is
  "\<lambda>m n. \<forall>i. n_valid (m i) n" by simp
definition pcore_fun :: "('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) option" where
  "pcore_fun m = Some ((\<lambda>b. case pcore b of Some a \<Rightarrow> a | None \<Rightarrow> \<epsilon>) \<circ> m)"
definition op_fun :: "('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b)" where
  "op_fun m1 m2 = (\<lambda>i. (m1 i) \<cdot> (m2 i))"
instance proof
show "non_expansive (valid_raw::('a\<Rightarrow>'b) \<Rightarrow> sprop)"
  by (rule non_expansiveI; auto simp: valid_raw_fun_def n_equiv_sprop_def Abs_sprop_inverse)
  (meson n_equiv_fun_def n_valid_ne ofe_mono ofe_sym)+
next
show "non_expansive (pcore::('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) option)"
  apply (rule non_expansiveI)
  apply (simp add: pcore_fun_def n_equiv_fun_def split: option.splits)
  using valid_raw_ne
  by (smt (verit, del_insts) comp_def n_equiv_fun_def n_equiv_option_def non_expansive_def ofe_eq_limit option.sel option.simps(5) pcore_ne)
next
show "non_expansive2 (op::('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b))"
  apply (rule non_expansive2I; auto simp: op_fun_def n_equiv_fun_def)
  using op_ne by blast
next
fix a b c :: "'a\<Rightarrow>'b"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (auto simp: op_fun_def camera_assoc)
next
fix a b :: "'a\<Rightarrow>'b"
show "a \<cdot> b = b \<cdot> a" by (auto simp: op_fun_def camera_comm)
next
fix a a' :: "'a\<Rightarrow>'b"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" by (auto simp: op_fun_def pcore_fun_def)
next
fix a a' :: "'a\<Rightarrow>'b"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a" by (auto simp: pcore_fun_def)
  (smt (z3) \<epsilon>_pcore camera_pcore_idem comp_apply comp_assoc fun.map_cong0 option.case_eq_if option.collapse option.simps(5))
next
fix a a' b :: "'a\<Rightarrow>'b"
assume assms: "\<exists>c. b = a \<cdot> c"
then obtain c where c: "b = a \<cdot> c" by blast
then have "\<forall>i. b i = a i \<cdot> c i" by (auto simp: op_fun_def)
then have i: "\<forall>i. \<exists>j. (case pcore (a i \<cdot> c i) of None \<Rightarrow> \<epsilon> | Some a \<Rightarrow> a) = (case pcore (a i) of None \<Rightarrow> \<epsilon> | Some a \<Rightarrow> a) \<cdot> j"
  by (metis option.simps(5) camera_pcore_mono total_pcore)
define cs where cs: "cs \<equiv> {(i,j) | i j. (case pcore (a i \<cdot> c i) of None \<Rightarrow> \<epsilon> | Some a \<Rightarrow> a) = (case pcore (a i) of None \<Rightarrow> \<epsilon> | Some a \<Rightarrow> a) \<cdot> j}"
with i have "\<forall>i. \<exists>j. (i,j) \<in> cs" by simp
then obtain cf where "\<forall>i. (i, cf i) \<in> cs" by metis
with i cs have "\<forall>i. (case pcore (a i \<cdot> c i) of None \<Rightarrow> \<epsilon> | Some a \<Rightarrow> a) = (case pcore (a i) of None \<Rightarrow> \<epsilon> | Some a \<Rightarrow> a) \<cdot> cf i"
  by simp
then have "(\<lambda>b. case pcore b of None \<Rightarrow> \<epsilon> | Some a \<Rightarrow> a) \<circ> (\<lambda>i. a i \<cdot> c i) = (\<lambda>i. (case pcore (a i) of None \<Rightarrow> \<epsilon> | Some a \<Rightarrow> a) \<cdot> cf i)"
  by auto  
then show "pcore a = Some a' \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  by (auto simp: pcore_fun_def op_fun_def c)
next
fix a b :: "'a\<Rightarrow>'b"
fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  apply (simp add: valid_raw_fun_def op_fun_def)
  using Abs_sprop_inverse camera_valid_op by fastforce
next
fix a b c :: "'a\<Rightarrow>'b"
fix n
assume assms: "Rep_sprop (valid_raw a) n" "n_equiv n a (b \<cdot> c)"
then have i_valid: "\<forall>i. n_valid (a i) n" by (auto simp: Abs_sprop_inverse valid_raw_fun_def)
from assms have i_equiv: "\<forall>i. n_equiv n (a i) (b i \<cdot> c i)" by (auto simp: n_equiv_fun_def op_fun_def)
from camera_extend i_valid i_equiv 
  have i12: "\<forall>i. \<exists>i1 i2. a i = i1 \<cdot> i2 \<and> n_equiv n i1 (b i) \<and> n_equiv n i2 (c i)" by blast
then obtain c1 c2 where "\<forall>i. a i = (c1 i) \<cdot> (c2 i) \<and> n_equiv n (c1 i) (b i) \<and> n_equiv n (c2 i) (c i)"
  by metis
then show "\<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c"
  by (auto simp: op_fun_def n_equiv_fun_def)
qed
end

lemma singleton_map_n_valid [simp]: "n_valid [k\<mapsto>v] n \<longleftrightarrow> n_valid v n"
  by (simp add: valid_raw_fun.rep_eq valid_raw_option_def)

lemma singleton_map_valid [simp]: "valid [k\<mapsto>v] \<longleftrightarrow> valid v"
  by (simp add: valid_def)

lemma singleton_map_op [simp]: "[k\<mapsto>v] \<cdot> [k\<mapsto>v'] = [k\<mapsto>(v\<cdot>v')]"
  by (auto simp: op_fun_def op_option_def)

lemma singleton_map_n_equiv [simp]: "n_equiv n [k\<mapsto>x] [k\<mapsto>y] \<longleftrightarrow> n_equiv n x y"
  by (auto simp: n_equiv_fun_def n_equiv_option_def)

lemma singleton_map_only_n_equiv: "n_equiv n [k\<mapsto>x] y \<Longrightarrow> \<exists>y'. y=[k\<mapsto>y'] \<and> n_equiv n x y'" 
proof -
assume assms: "n_equiv n [k\<mapsto>x] y"
then have i: "n_equiv n ([k\<mapsto>x] i) (y i)" for i by (simp add: n_equiv_fun_def)
from this[of k] have k: "n_equiv n (Some x) (y k)" by simp
from i have not_k: "n_equiv n None (y j) \<longleftrightarrow> j\<noteq>k" for j
  by (metis fun_upd_apply n_equiv_option_def option.distinct(1))
from k obtain y' where y': "y k = Some y'" "n_equiv n x y'"
  by (metis n_equiv_option_def option.distinct(1) option.sel)
moreover from not_k have "y j = None \<longleftrightarrow> j\<noteq>k" for j by (simp add: n_equiv_option_def)
ultimately have "y = (\<lambda>i. if i=k then Some y' else None)" by metis
with y' show ?thesis by fastforce
qed
  
lemma singleton_map_n_incl: "n_incl n [k\<mapsto>v] m \<longleftrightarrow> (\<exists> v'. m k = Some v' \<and> n_incl n (Some v) (Some v'))"
proof 
  assume "n_incl n [k\<mapsto>v] m"
  then obtain m' where "n_equiv n m ([k\<mapsto>v]\<cdot>m')" unfolding n_incl_def by blast
  then have "\<forall>i. n_equiv n (m i) (([k\<mapsto>v]\<cdot>m') i)" unfolding n_equiv_fun_def .
  then have "n_equiv n (m k) (Some v \<cdot> (m' k))" unfolding op_fun_def by (metis fun_upd_same)
  moreover from option_n_equiv_Some_op[OF this] obtain v' where "m k = Some v'" by auto
  ultimately show "\<exists> v'. m k = Some v' \<and> n_incl n (Some v) (Some v')" by (auto simp: n_incl_def)
next
  assume "\<exists> v'. m k = Some v' \<and> n_incl n (Some v) (Some v')"
  then obtain v' c where "m k = Some v'" "n_equiv n (m k) (Some v \<cdot> c)" by (auto simp: n_incl_def)
  then have "n_equiv n (m k) (([k\<mapsto>v]\<cdot> (m(k:=c))) k)" unfolding op_fun_def by simp
  then have "n_equiv n m ([k\<mapsto>v]\<cdot> (m(k:=c)))" 
    apply (auto simp: n_equiv_fun_def op_fun_def op_option_def)
    subgoal for i apply (cases "m i") by (auto simp: ofe_refl) done
  then show "n_incl n [k\<mapsto>v] m" by (auto simp: n_incl_def)
qed

lemma pcore_fun_alt: "pcore (f::'a\<rightharpoonup>'b::camera) = Some (\<lambda>i. Option.bind (f i) pcore)"
proof -
have "pcore f = Some (\<lambda>i. case pcore (f i) of Some a \<Rightarrow> a | None \<Rightarrow> None)"
  by (auto simp: pcore_fun_def comp_def) (metis \<epsilon>_option_def)
moreover have "(case pcore (f x) of Some a \<Rightarrow> a | None \<Rightarrow> None) = Option.bind (f x) pcore" for x
  by (cases "f x") (auto simp: pcore_option_def)
ultimately show ?thesis by simp
qed

lemma op_singleton_upd: "g k = None \<Longrightarrow> [k\<mapsto>x] \<cdot> g = g(k\<mapsto>x)"
  by (auto simp: op_fun_def op_option_def)

definition merge :: "('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> ('b\<rightharpoonup>'a) \<Rightarrow> ('b\<rightharpoonup>'a) \<Rightarrow> ('b\<rightharpoonup>'a)" where
  "merge f m1 m2 = (\<lambda>i. (case m1 i of Some x1 \<Rightarrow> (case m2 i of Some x2 \<Rightarrow> Some (f x1 x2) 
    | None \<Rightarrow> Some x1) | None \<Rightarrow> m2 i))"

lemma merge_op: "merge op m1 m2 = m1 \<cdot> m2"
  by (auto simp: merge_def op_fun_def op_option_def split: option.splits) 

lemma merge_dom: "dom (merge f m1 m2) = dom m1 \<union> dom m2"
  by (auto simp: merge_def split: option.splits)

lemma merge_ne: "non_expansive2 f \<Longrightarrow> non_expansive2 (merge f)"
  apply (rule non_expansive2I)
  apply (auto simp: non_expansive2_def merge_def n_equiv_fun_def n_equiv_option_def split: option.splits)
  apply (metis option.distinct(1))+
  by (metis option.discI option.inject)+

instance "fun" :: (type,ducamera) dcamera 
  apply (standard; auto simp: valid_raw_fun.rep_eq valid_def)
  using d_valid[simplified valid_def] by blast

instance "fun" :: (type,core_id_ucamera) core_id by standard (auto simp: pcore_fun_def pcore_id)

instantiation "fun" :: (type, ucamera) ucamera begin
definition \<epsilon>_fun :: "'a\<Rightarrow>'b" where  "\<epsilon>_fun \<equiv> (\<lambda>_. \<epsilon>)"
instance apply (standard)
apply (simp_all add: valid_def valid_raw_fun_def Abs_sprop_inverse valid_raw_option_def)
subgoal using Rep_sprop_inverse \<epsilon>_valid valid_def by (auto simp: \<epsilon>_fun_def)
subgoal by (auto simp: op_fun_def \<epsilon>_left_id \<epsilon>_fun_def)
by (auto simp: pcore_fun_def \<epsilon>_pcore \<epsilon>_fun_def split: option.splits )
end

lemma \<epsilon>_map_equiv [simp]: "n_equiv n (\<epsilon>::('a\<rightharpoonup>'b::camera)) x \<longleftrightarrow> x=\<epsilon>"
  by (auto simp: n_equiv_fun_def \<epsilon>_fun_def n_equiv_option_def \<epsilon>_option_def) 

lemma dcamera_val_\<epsilon>_map [simp]: "dcamera_val (\<epsilon>::('a\<rightharpoonup>'b::camera))"
  by (simp add: dcamera_val_def discrete_val_def ofe_limit valid_def valid_raw_fun.rep_eq)
    (auto simp: \<epsilon>_fun_def \<epsilon>_option_def valid_raw_option_def)

lemma map_empty_left_id: "Map.empty \<cdot> f = (f:: 'a\<rightharpoonup>'b::camera)"
unfolding op_fun_def op_option_def HOL.fun_eq_iff
proof
fix x show "option_op None (f x) = f x" by (cases "f x") auto
qed

lemma ran_pcore_id_pred: "(\<forall>x \<in> ran m. pcore_id_pred x) \<Longrightarrow> pcore_id_pred m"
proof -
  assume assm: "\<forall>x \<in> ran m. pcore_id_pred x"
  then have "\<forall>y. pcore (m y) = Some (m y)" 
    by (auto simp: pcore_id_pred_def ran_def pcore_option_def split: option.splits)
  then show ?thesis unfolding pcore_id_pred_def pcore_fun_def comp_def by simp
qed
  
instance "fun" :: (type,ducamera) ducamera ..

lemma fun_n_incl:
  "n_incl n (f::'a\<Rightarrow>'b::{camera} option) g \<Longrightarrow> dom f \<subseteq> dom g \<and> (\<forall>k. n_incl n (f k) (g k))"
apply (auto simp: n_incl_def incl_def n_equiv_fun_def n_equiv_option_def op_fun_def op_option_def)
subgoal by (metis option_op.elims)
by meson

subsubsection \<open> Set type camera \<close>
instantiation set :: (type) camera begin
definition valid_raw_set :: "'a set \<Rightarrow> sprop" where "valid_raw_set _ = sTrue"
definition pcore_set :: "'a set \<Rightarrow> 'a set option" where "pcore_set \<equiv> Some"
definition op_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where "op_set \<equiv> (\<union>)"
instance proof
show "non_expansive (valid_raw::'a set \<Rightarrow> sprop)"
  by (rule non_expansiveI) (auto simp: valid_raw_set_def n_equiv_sprop_def)
next
show "non_expansive (pcore::'a set \<Rightarrow> 'a set option)"
  by (rule non_expansiveI) (auto simp: pcore_set_def n_equiv_option_def)
next
show "non_expansive2 (op::'a set \<Rightarrow> 'a set \<Rightarrow> 'a set)"
  by (rule non_expansive2I) (auto simp: op_set_def n_equiv_set_def)
qed (auto simp: valid_raw_set_def pcore_set_def op_set_def n_equiv_set_def)
end

instance set :: (type) dcamera by (standard; auto simp: valid_raw_set_def valid_def)

instance set :: (type) core_id by (standard) (auto simp: pcore_set_def)

lemma n_incl_set[simp]: "n_incl n a (b::'a set) = (a\<subseteq>b)"
  by (auto simp: n_incl_def op_set_def n_equiv_set_def)
lemma n_incl_single[simp]: "n_incl n {x} a = (x\<in>a)"
  by auto
  
instantiation set :: (type) ucamera begin
definition \<epsilon>_set :: "'a set" where "\<epsilon>_set = {}"
instance by (standard) (auto simp: op_set_def valid_def valid_raw_set_def pcore_set_def \<epsilon>_set_def)
end

instance set :: (type) ducamera ..

subsubsection \<open> Disjoint set camera \<close>
instantiation dset :: (type) camera begin
definition valid_raw_dset :: "'a dset \<Rightarrow> sprop" where 
  "valid_raw_dset d \<equiv> case d of DSet _ \<Rightarrow> sTrue | DBot \<Rightarrow> sFalse"
definition pcore_dset :: "'a dset \<Rightarrow> 'a dset option" where "pcore_dset d = Some (DSet {})"
definition op_dset :: "'a dset \<Rightarrow> 'a dset \<Rightarrow> 'a dset" where 
  "op_dset x y \<equiv> case (x,y) of (DSet x', DSet y') \<Rightarrow> if x' \<inter> y' = {} then DSet (x'\<union>y') else DBot
    | _ \<Rightarrow> DBot"
instance proof
show "non_expansive (valid_raw::'a dset \<Rightarrow> sprop)"
  by (rule non_expansiveI) (auto simp: d_equiv ofe_refl)
next
show "non_expansive (pcore::'a dset \<Rightarrow> 'a dset option)"
  by (rule non_expansiveI) (auto simp: d_equiv)
next
show "non_expansive2 (op::'a dset \<Rightarrow> 'a dset \<Rightarrow> 'a dset)"
  by (rule non_expansive2I) (auto simp: d_equiv)
qed (auto simp: pcore_dset_def op_dset_def valid_raw_dset_def d_equiv split: dset.splits)
end

lemma dsubs_op_minus: "d1 \<subseteq>\<^sub>d d2 \<Longrightarrow> d2 = d1 \<cdot> (d2 - d1)"
  unfolding op_dset_def using dsubs_dset by fastforce

lemma dsubs_disj_opL: "\<lbrakk>disj d1 d2; d1 \<cdot> d2 \<subseteq>\<^sub>d d3\<rbrakk> \<Longrightarrow> d1 \<subseteq>\<^sub>d d3"
  unfolding disj_def apply (cases d1; cases d2; cases d3) apply auto
  by (smt (verit, ccfv_threshold) Un_iff dset.simps(4) op_dset_def prod.simps(2) subdset_eq.simps(1) subsetD)

lemma dsubs_disj_opR: "\<lbrakk>disj d1 d2; d1 \<cdot> d2 \<subseteq>\<^sub>d d3\<rbrakk> \<Longrightarrow> d2 \<subseteq>\<^sub>d d3"
  unfolding disj_def apply (cases d1; cases d2; cases d3) apply auto
  by (metis camera_comm disj_def disjoint_iff dsubs_disj_opL subdset_eq.simps(1) subsetD)

instance dset :: (type) dcamera 
  by standard (auto simp: valid_def valid_raw_dset_def split: dset.splits)

instantiation dset :: (type) ucamera begin
definition \<epsilon>_dset :: "'a dset" where "\<epsilon>_dset = DSet {}"
instance 
  by standard (auto simp: valid_def valid_raw_dset_def op_dset_def pcore_dset_def \<epsilon>_dset_def split:dset.splits)
end

instance dset :: (type) ducamera ..

subsubsection \<open> Unit type camera \<close>
instantiation unit :: camera begin
definition valid_raw_unit :: "unit \<Rightarrow> sprop" where [simp]: "valid_raw_unit _ = sTrue"
definition pcore_unit :: "unit \<Rightarrow> unit option" where [simp]: "pcore_unit = Some"
definition op_unit :: "unit \<Rightarrow> unit \<Rightarrow> unit" where [simp]: "op_unit _ _ = ()"
instance by standard (auto simp: non_expansive_def non_expansive2_def n_equiv_option_def n_equiv_sprop_def)
end

instance unit :: dcamera by standard (auto simp: valid_def)

instantiation unit :: ucamera begin
definition  \<epsilon>_unit :: unit where [simp]: "\<epsilon>_unit = ()"
instance by standard (auto simp: valid_def)
end

instance unit :: ducamera ..

subsubsection \<open>Finite set camera\<close>
instantiation fset :: (type) camera begin
definition valid_raw_fset :: "'a fset \<Rightarrow> sprop" where "valid_raw_fset _ = sTrue"
definition pcore_fset :: "'a fset \<Rightarrow> 'a fset option" where "pcore_fset \<equiv> Some"
definition op_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where "op_fset \<equiv> (|\<union>|)"
instance proof
show "non_expansive (valid_raw::'a fset \<Rightarrow> sprop)"
  by (rule non_expansiveI) (auto simp: valid_raw_fset_def n_equiv_sprop_def)
next
show "non_expansive (pcore::'a fset \<Rightarrow> 'a fset option)"
  by (rule non_expansiveI) (auto simp: pcore_fset_def n_equiv_option_def)
next
show "non_expansive2 (op::'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset)"
  by (rule non_expansive2I) (auto simp: op_fset_def)
qed (auto simp: valid_raw_fset_def pcore_fset_def op_fset_def)
end

instance fset :: (type) dcamera by (standard; auto simp: valid_raw_fset_def valid_def)

instance fset :: (type) core_id by (standard) (auto simp: pcore_fset_def)

lemma n_incl_fset[simp]: "n_incl n a (b::'a fset) = (a|\<subseteq>|b)"
  by (auto simp: n_incl_def op_fset_def)
lemma n_incl_fsingle[simp]: "n_incl n {|x|} a = (x|\<in>|a)"
  by auto
  
instantiation fset :: (type) ucamera begin
definition \<epsilon>_fset :: "'a fset" where "\<epsilon>_fset = {||}"
instance by (standard) (auto simp: op_fset_def valid_def valid_raw_fset_def pcore_fset_def \<epsilon>_fset_def)
end

subsubsection \<open> Disjoint fset camera \<close>
instantiation dfset :: (type) camera begin
definition valid_raw_dfset :: "'a dfset \<Rightarrow> sprop" where 
  "valid_raw_dfset d \<equiv> case d of DFSet _ \<Rightarrow> sTrue | DFBot \<Rightarrow> sFalse"
definition pcore_dfset :: "'a dfset \<Rightarrow> 'a dfset option" where "pcore_dfset d = Some (DFSet {||})"
definition op_dfset :: "'a dfset \<Rightarrow> 'a dfset \<Rightarrow> 'a dfset" where 
  "op_dfset x y \<equiv> case (x,y) of (DFSet x', DFSet y') \<Rightarrow> if x' |\<inter>| y' = {||} then DFSet (x'|\<union>|y') 
    else DFBot | _ \<Rightarrow> DFBot"
instance proof
show "non_expansive (valid_raw::'a dfset \<Rightarrow> sprop)"
  by (rule non_expansiveI) (auto simp: d_equiv ofe_refl)
next
show "non_expansive (pcore::'a dfset \<Rightarrow> 'a dfset option)"
  by (rule non_expansiveI) (auto simp: d_equiv)
next
show "non_expansive2 (op::'a dfset \<Rightarrow> 'a dfset \<Rightarrow> 'a dfset)"
  by (rule non_expansive2I) (auto simp: d_equiv)
qed (auto simp: pcore_dfset_def op_dfset_def valid_raw_dfset_def d_equiv split: dfset.splits)
end

instance dfset :: (type) dcamera 
  by standard (auto simp: valid_def valid_raw_dfset_def split: dfset.splits)

instantiation dfset :: (type) ucamera begin
definition \<epsilon>_dfset :: "'a dfset" where "\<epsilon>_dfset = DFSet {||}"
instance 
  by standard (auto simp: valid_def \<epsilon>_dfset_def valid_raw_dfset_def op_dfset_def pcore_dfset_def 
    split:dfset.splits)
end

instance dfset :: (type) ducamera ..
subsubsection \<open> Finite map camera \<close>
lemma fmupd_ne: "non_expansive (fmupd l v)"
by (rule non_expansiveI) (auto simp: n_equiv_fmap_def n_equiv_fun_def ofe_refl)

context includes fmap.lifting begin
lift_definition fmpcore :: "('a,'b::camera) fmap \<Rightarrow> ('a,'b) fmap option" is
  "\<lambda>m. Some (\<lambda>i. Option.bind (m i) pcore)"
  by (metis (mono_tags, lifting) bind_eq_None_conv domIff option.pred_inject(2) rev_finite_subset subsetI)
end

lemma option_op_dom:"dom (\<lambda>i. option_op (f i) (g i)) = dom f \<union> dom g"
  apply auto using option_opE by auto

lemma option_op_finite: "\<lbrakk>finite (dom f); finite (dom g)\<rbrakk> \<Longrightarrow> (\<lambda>i. option_op (f i) (g i)) \<in> {m. finite (dom m)}"
  using option_op_dom by (metis finite_Un mem_Collect_eq)
lemmas option_op_fmlookup = option_op_finite[OF dom_fmlookup_finite dom_fmlookup_finite]
lemma upd_dom: "dom (\<lambda>i. if x = i then Some y else fmlookup m2 i) = fmdom' m2 \<union> {x}"
  apply (auto simp: fmlookup_dom'_iff) by (metis domI domIff)
lemma upd_fin: "finite (dom (\<lambda>i. if x = i then Some y else fmlookup m2 i))"
  unfolding upd_dom by simp
lemma drop_dom: "dom (\<lambda>i. if i \<noteq> x then fmlookup m2 i else None) = fmdom' m2 - {x}"
  apply (auto simp: fmlookup_dom'_iff) apply (meson option.distinct(1)) by (meson domI domIff)
lemma drop_fin: "finite (dom (\<lambda>i. if i \<noteq> x then fmlookup m2 i else None))"
  unfolding drop_dom by simp

lemma map_upd_fin: "m \<in> {m. finite (dom m)} \<Longrightarrow> (map_upd a b m) \<in> {m. finite (dom m)}"
  by (simp add: map_upd_def)

instantiation fmap :: (type,camera) camera begin
context includes fmap.lifting begin
lift_definition valid_raw_fmap :: "('a, 'b) fmap \<Rightarrow> sprop" is valid_raw .
lift_definition pcore_fmap :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap option" is pcore
  apply (auto simp: pcore_fun_def comp_def)
  by (metis (mono_tags, lifting) domIff finite_subset option.case(1) option.case(2) pcore_option_def subsetI)
lift_definition op_fmap :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" is "merge op"
  using merge_dom by (metis infinite_Un)
end  
instance proof 
show "non_expansive (valid_raw::('a, 'b) fmap \<Rightarrow> sprop)"
  apply (rule non_expansiveI)
  by (auto simp: valid_raw_fmap.rep_eq)  (simp add: n_equiv_fmap.rep_eq valid_raw_ne)
next
show "non_expansive (pcore::('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap option)"
  apply (rule non_expansiveI)
  apply (auto simp: pcore_fmap_def n_equiv_fmap_def)
  by (smt (verit, ccfv_threshold) camera_props(9) dom_fmlookup_finite eq_onp_same_args 
    map_option_eq_Some n_equiv_fmap.abs_eq n_equiv_option_def option.map_disc_iff pcore_fmap.rep_eq)
next
show "non_expansive2 (op::('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap)"
  apply (auto simp: op_fmap.rep_eq n_equiv_fmap_def non_expansive2_def)
  using non_expansive2E[OF merge_ne[OF op_non_expansive]] by blast
next
fix a b c :: "('a,'b) fmap"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" apply (auto simp: op_fmap_def merge_op)
  by (metis (mono_tags, lifting) Abs_fmap_inverse camera_assoc fmlookup merge_op op_fmap.rep_eq)
next
fix a b :: "('a,'b) fmap"
show "a \<cdot> b = b \<cdot> a"
  by (metis (mono_tags) camera_comm fmlookup_inject merge_op op_fmap.rep_eq)
next
fix a a' :: "('a,'b) fmap"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a"
  by (metis (mono_tags, lifting) DerivedConstructions.op_fmap.rep_eq camera_pcore_id fmlookup_inject 
    merge_op option.simps(9) pcore_fmap.rep_eq)
next
fix a a' :: "('a,'b) fmap"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a"
  by (smt (verit, del_insts) DerivedConstructions.pcore_fmap.abs_eq camera_pcore_idem 
    dom_fmlookup_finite eq_onp_same_args fmlookup_inverse option.simps(9) pcore_fmap.rep_eq)
next
fix a a' b :: "('a,'b) fmap"
assume assms: "pcore a = Some a'" "\<exists>c. b = a \<cdot> c"
let ?b' = "Abs_fmap (\<lambda>x. case pcore (fmlookup b x) of None \<Rightarrow> \<epsilon> | Some x' \<Rightarrow> x')"
have b': "pcore b = Some ?b'" by (auto simp: pcore_fmap_def pcore_fun_def comp_def)
have fmlookup_op: "fmlookup (x\<cdot>y) i = fmlookup x i \<cdot> fmlookup y i" for x y i
  by (auto simp: op_fmap.rep_eq merge_op op_fun_def)
have "dom (\<lambda>x. case case fmlookup m x of None \<Rightarrow> Some None | Some a \<Rightarrow> Some (pcore a) of None \<Rightarrow> \<epsilon> | Some a \<Rightarrow> a)
  \<subseteq> fmdom' m" for m :: "('a,'b) fmap"
  by (auto simp: fmdom'I split: option.splits) 
then have fin: "(\<lambda>x. case case fmlookup m x of None \<Rightarrow> Some None | Some a \<Rightarrow> Some (pcore a) of None \<Rightarrow> \<epsilon> | Some a \<Rightarrow> a)
  \<in> {m. finite (dom m)}" for m :: "('a,'b) fmap"
  by (metis finite_fmdom' mem_Collect_eq rev_finite_subset)
have lookup_pcore: "pcore m = Some m' \<Longrightarrow> Some (fmlookup m' i) = pcore (fmlookup m i)" for m m' i
  apply (cases "fmlookup m i"; cases "fmlookup m' i")
  by (auto simp: pcore_fmap_def pcore_option_def pcore_fun_def comp_def Abs_fmap_inverse[OF fin] split: option.splits)
have fmlookup_pcore: "fmlookup (the (pcore m)) i = the (pcore (fmlookup m i))" for m i
  by (metis lookup_pcore option.distinct(1) option.exhaust_sel option.sel option.simps(8) pcore_fmap.rep_eq total_pcore)
have lookup_incl:"(\<exists>m3. m1 = (m2\<cdot>m3)) \<longleftrightarrow> (\<forall>i. incl (fmlookup m2 i) (fmlookup m1 i))" for m1 m2
apply auto
using fmlookup_op incl_def apply blast
proof (induction m2)
  case fmempty
  then show ?case by (auto simp: op_fmap_def merge_op op_fun_def op_option_def incl_def fmlookup_inverse)
next
  case (fmupd x y m2)
  then have "\<forall>i. \<exists>j. fmlookup m1 i = fmlookup (fmupd x y m2) i \<cdot> j"
    by (simp add: incl_def)
  then have "\<forall>i. \<exists>j. fmlookup m1 i = fmlookup m2 i \<cdot> (if i=x then Some y \<cdot> j else j)"
  using fmupd(2) apply (auto simp: op_option_def) by (metis (full_types))
  then have "\<forall>i. \<exists>j. fmlookup m1 i = fmlookup m2 i \<cdot> j" by auto
  with fmupd(1) obtain m3 where m3: "m1 = (m2 \<cdot> m3)" by (auto simp: incl_def)
  from fmupd(2,3) have "\<exists>y. fmlookup m1 x = Some y"
    apply (auto simp: incl_def) by (metis (mono_tags) ofe_eq_limit option_n_equiv_Some_op)
  then obtain y2 where y2: "fmlookup m1 x = Some y2" by blast
  with m3 fmupd(2) have y2': "fmlookup m3 x = Some y2" by (simp add: fmlookup_op op_option_def)  
  from y2 fmupd(3) have "\<exists>y3. Some y2 = (Some y\<cdot>y3)"
    apply (auto simp: incl_def) by (metis (full_types))
  then obtain y3 where y3: "Some y2 = (Some y\<cdot>y3)" by auto
  define m3' where "m3' = (case y3 of Some y3' \<Rightarrow> fmupd x y3' m3 | None \<Rightarrow> fmdrop x m3)"
  with y2 y2' y3 m3 fmupd(2) have "m1 = ((fmupd x y m2)\<cdot> m3')" 
  apply (cases y3) apply (auto simp: op_option_def op_fmap_def merge_op op_fun_def split: option.splits)
  unfolding Abs_fmap_inverse[OF option_op_fmlookup] 
    Abs_fmap_inject[OF option_op_fmlookup option_op_finite[OF upd_fin drop_fin]]
  apply auto
  unfolding Abs_fmap_inject[OF option_op_fmlookup option_op_finite[OF upd_fin upd_fin]]
  by force
  then show ?case by auto  
  qed
have core_mono: "(\<exists>m3. (the (pcore m1)) = (the (pcore m2) \<cdot> m3))" if wo_pcore: "(\<exists>m3. m1 = (m2\<cdot>m3))"
for m1 m2 :: "('a,'b) fmap"
  apply (auto simp: lookup_incl fmlookup_pcore) using camera_core_mono wo_pcore[unfolded lookup_incl]
  core_def by (simp add: pcore_mono total_pcore)
from this[OF assms(2)] assms(1) show "\<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)" by (simp add: b')
next
fix a b :: "('a,'b) fmap" and n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  including fmap.lifting apply transfer unfolding merge_op using camera_valid_op by blast
next
fix a b1 b2 :: "('a,'b) fmap" and n
assume assms: "Rep_sprop (valid_raw a) n" "n_equiv n a (b1 \<cdot> b2)" 
then show "\<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b1 \<and> n_equiv n c2 b2"
proof (induction a arbitrary: b1 b2)
  case fmempty
  then have "\<forall>i. n_equiv n None (fmlookup b1 i \<cdot> fmlookup b2 i)"
    by (auto simp: n_equiv_fmap_def op_fmap.rep_eq merge_op n_equiv_fun_def op_fun_def)
  then have "b1 = fmempty \<and> b2 = fmempty" apply (auto simp: n_equiv_option_def op_option_def)
    using option_opE by (metis fmap_ext fmempty_lookup)+
  then have "fmempty = b1 \<cdot> b2 \<and> n_equiv n b1 b1 \<and> n_equiv n b2 b2"
    apply (auto simp: ofe_refl op_fmap_def merge_op op_fun_def op_option_def) 
    by (simp add:  fmempty_def)
  then show ?case by auto
next
  case (fmupd x y a)
  from fmupd(2,3) have valid_a: "Rep_sprop (valid_raw a) n"
    apply (auto simp: valid_raw_fmap.rep_eq valid_raw_fun.rep_eq valid_raw_option_def split: option.splits)
    by (metis option.distinct(1))
  from fmupd(3) have valid_y: "n_valid y n"
    apply (auto simp: valid_raw_fmap.rep_eq valid_raw_fun.rep_eq valid_raw_option_def split: option.splits)
    by presburger  
  let ?b1x = "fmlookup b1 x" let ?b2x = "fmlookup b2 x"
  from fmupd(4) have y:"n_equiv n (Some y) (?b1x \<cdot> ?b2x)"
    apply (auto simp: n_equiv_fmap_def op_fmap.rep_eq merge_op n_equiv_fun_def op_fun_def) by presburger
  from fmupd(2,4) have equiv_a: "n_equiv n a (fmdrop x b1 \<cdot> fmdrop x b2)"
    apply (auto simp: n_equiv_fmap_def op_fmap.rep_eq merge_op n_equiv_fun_def op_fun_def op_option_def ofe_refl)
    by presburger
  from fmupd(1)[OF valid_a this] obtain c1 c2 where c12: 
    "a = c1 \<cdot> c2 \<and> n_equiv n c1 (fmdrop x b1) \<and> n_equiv n c2 (fmdrop x b2)" by blast
  { fix i
  from fmupd(3) have validi: "n_valid (fmlookup (fmupd x y a) i) n" 
      by (auto simp: valid_raw_fmap.rep_eq valid_raw_fun.rep_eq)
  from fmupd(4) have equivi: "n_equiv n (fmlookup (fmupd x y a) i) (fmlookup b1 i \<cdot> fmlookup b2 i)"
    by (auto simp: n_equiv_fmap_def op_fmap.rep_eq merge_op n_equiv_fun_def op_fun_def)
  from camera_extend[OF validi equivi] have "\<exists>c1 c2. fmlookup (fmupd x y a) i = c1 \<cdot> c2 
    \<and> n_equiv n c1 (fmlookup b1 i) \<and> n_equiv n c2 (fmlookup b2 i)" .}
  then have "\<forall>i. \<exists>c1 c2. fmlookup (fmupd x y a) i = c1 \<cdot> c2 \<and> n_equiv n c1 (fmlookup b1 i) 
    \<and> n_equiv n c2 (fmlookup b2 i)" by blast
  then have "\<exists>c1 c2. Some y = c1 \<cdot> c2 \<and> n_equiv n c1 ?b1x \<and> n_equiv n c2 ?b2x"
    by (metis fmupd_lookup)
  then obtain c1x c2x where c12x: "Some y = c1x \<cdot> c2x \<and> n_equiv n c1x ?b1x \<and> n_equiv n c2x?b2x"
    by auto
  then have cx_none: "c1x \<noteq> None \<or> c2x \<noteq> None" by (auto simp: op_option_def)
  have eq_onp_op:
    "eq_onp (\<lambda>m. finite (dom m)) (\<lambda>i. option_op (fmlookup c1 i) (fmlookup c2 i)) (\<lambda>i. option_op (fmlookup c1 i) (fmlookup c2 i))"
    using option_op_finite by (auto simp: eq_onp_def)
  define c1' where c1': "c1' \<equiv> (case c1x of Some y' \<Rightarrow> fmupd x y' c1 | None \<Rightarrow> c1)"
  define c2' where c2': "c2' \<equiv> (case c2x of Some y' \<Rightarrow> fmupd x y' c2 | None \<Rightarrow> c2)"  
  with c1' c12 cx_none y c12x have "fmupd x y a = c1' \<cdot> c2' \<and> n_equiv n c1' b1 \<and> n_equiv n c2' b2"
  apply (cases c1x; cases c2x) 
  apply (auto simp: op_option_def op_fmap_def merge_op op_fun_def split: option.splits)
  unfolding fmupd.abs_eq[OF eq_onp_op] Abs_fmap_inject[OF map_upd_fin[OF option_op_fmlookup] option_op_finite[OF dom_fmlookup_finite upd_fin]]
  subgoal apply (rule ext) by (smt (verit) Abs_fmap_inverse camera_comm eq_onp_def eq_onp_op fmupd(2) fmupd.rep_eq fmupd_lookup mem_Collect_eq op_option_def option_op.simps(2) option_opE)
  subgoal by (metis c12 fmap_ext fmlookup_drop is_none_code(2) is_none_simps(1) n_equiv_option_def)
  subgoal apply (auto simp: n_equiv_fmap_def n_equiv_fun_def) by presburger
  subgoal unfolding Abs_fmap_inject[OF map_upd_fin[OF option_op_fmlookup] option_op_finite[OF upd_fin dom_fmlookup_finite]]
    proof -
    assume "c1x = Some y"
    assume "a = Abs_fmap (\<lambda>i. option_op (fmlookup c1 i) (fmlookup c2 i))"
    then have "\<forall>a. option_op (if x = a then Some y else fmlookup c1 a) (fmlookup c2 a) = map_upd x y (\<lambda>a. option_op (fmlookup c1 a) (fmlookup c2 a)) a"
    by (smt (z3) Abs_fmap_inverse camera_comm eq_onp_def eq_onp_op fmupd.hyps fmupd.rep_eq fmupd_lookup mem_Collect_eq op_option_def option_opE option_op_none_unit(1))
    then show "map_upd x y (\<lambda>a. option_op (fmlookup c1 a) (fmlookup c2 a)) = (\<lambda>a. option_op (if x = a then Some y else fmlookup c1 a) (fmlookup c2 a))"
    by presburger qed
  subgoal by (smt (verit, del_insts) fmlookup_drop fmupd_lookup n_equiv_fmap.rep_eq n_equiv_fun_def)
  subgoal by (metis (mono_tags, lifting) fmfilter_alt_defs(1) fmfilter_true n_equiv_option_def option.distinct(1))  
  subgoal unfolding Abs_fmap_inject[OF map_upd_fin[OF option_op_fmlookup] option_op_finite[OF upd_fin upd_fin]]
    apply (rule ext) by (smt (verit) Abs_fmap_inverse c12x eq_onp_def eq_onp_op fmupd.rep_eq fmupd_lookup mem_Collect_eq op_option_def)
  subgoal apply (auto simp: n_equiv_fmap_def n_equiv_fun_def) by presburger
  apply (auto simp: n_equiv_fmap_def n_equiv_fun_def) by presburger  
  then show ?case by auto
  qed
qed
end

instance fmap :: (type,dcamera) dcamera apply standard
  apply (auto simp: valid_def valid_raw_fmap_def)
  using dcamera_valid_iff by blast

lemma empty_finite: " \<epsilon> \<in> {m. finite (dom m)} "
  by (auto simp: \<epsilon>_fun_def \<epsilon>_option_def)

instantiation fmap :: (type, camera) ucamera begin
context includes fmap.lifting begin
lift_definition \<epsilon>_fmap :: "('a, 'b) fmap" is "\<epsilon>::'a\<rightharpoonup>'b" by (auto simp: \<epsilon>_fun_def \<epsilon>_option_def)
end
instance apply standard
by (auto simp: \<epsilon>_fmap_def valid_def valid_raw_fmap_def op_fmap_def pcore_fmap_def Abs_fmap_inverse[OF empty_finite]
  \<epsilon>_valid[unfolded valid_def] \<epsilon>_left_id fmlookup_inverse \<epsilon>_pcore merge_op)
end

instance fmap :: (type, dcamera) ducamera ..

subsubsection \<open>Bool camera\<close>
instantiation bool :: camera begin
  lift_definition valid_raw_bool :: "bool \<Rightarrow> sprop" is "\<lambda>_ _. True" .
  definition pcore_bool :: "bool \<Rightarrow> bool option" where "pcore_bool b \<equiv> Some b"
  definition op_bool :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "op_bool \<equiv> HOL.disj"
instance proof (standard)
show "non_expansive (valid_raw::bool \<Rightarrow> sprop)"
  by (rule non_expansiveI) (auto simp: valid_raw_bool_def n_equiv_sprop_def)
next
show "non_expansive (pcore::bool \<Rightarrow> bool option)"
  by (rule non_expansiveI) (auto simp: pcore_bool_def n_equiv_option_def)
next
show "non_expansive2 (op::bool\<Rightarrow>bool\<Rightarrow>bool)" by (rule non_expansive2I) (auto)
next
fix a b c :: bool
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (auto simp: op_bool_def)
next
fix a b :: bool
show "a \<cdot> b = b \<cdot> a" by (auto simp: op_bool_def)
next
fix a a' :: bool
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" by (auto simp: op_bool_def pcore_bool_def)
next
fix a a' :: bool
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a" by (auto simp: pcore_bool_def)
next
fix a a' b :: bool
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  by (auto simp: op_bool_def pcore_bool_def)
next
fix a b :: bool and n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  by (auto simp: valid_raw_bool_def op_bool_def)
next
fix a b1 b2 :: bool and n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b1 \<cdot> b2) \<Longrightarrow> \<exists>c1 c2. a = c1 \<cdot> c2 \<and> 
  n_equiv n c1 b1 \<and> n_equiv n c2 b2"
  by (auto simp: valid_raw_bool_def)
qed
end

lemma bool_upd_neg: "P \<longleftrightarrow> \<not>Q \<Longrightarrow> P \<leadsto>Q"
  by (auto simp: camera_upd_def op_bool_def valid_raw_bool_def)

instance bool :: dcamera by (standard) (auto simp: valid_def valid_raw_bool_def)

instantiation bool :: ucamera begin
definition "\<epsilon>_bool \<equiv> False"
instance by standard (auto simp: \<epsilon>_bool_def valid_def valid_raw_bool_def op_bool_def pcore_bool_def)
end

instance bool :: ducamera ..

instance bool :: core_id by standard (auto simp: pcore_bool_def)

subsubsection \<open>Int camera\<close>
instantiation int :: camera begin
  definition valid_raw_int :: "int \<Rightarrow> sprop" where "valid_raw_int i = sTrue"
  definition pcore_int :: "int \<Rightarrow> int option" where "pcore_int _ \<equiv> Some 0"
  definition op_int :: "int \<Rightarrow> int \<Rightarrow> int" where "op_int \<equiv> (+)"
instance by standard 
  (auto simp: valid_raw_int_def pcore_int_def op_int_def n_equiv_sprop_def n_equiv_option_def 
    intro!: non_expansiveI non_expansive2I)
end

lemma int_op_plus: "(p::int) \<cdot> q = p + q" by (simp add: op_int_def)

instance int :: dcamera by (standard) (auto simp: valid_def valid_raw_int_def)

instantiation int :: ucamera begin
definition "\<epsilon>_int \<equiv> 0::int"
instance by standard (auto simp: \<epsilon>_int_def valid_def valid_raw_int_def op_int_def pcore_int_def)
end

instance int :: ducamera ..

subsubsection \<open>Multiset camera\<close>
instantiation multiset :: (type) camera begin
definition valid_raw_multiset :: "'a multiset \<Rightarrow> sprop" where "valid_raw_multiset \<equiv> \<lambda>_. sTrue"
definition pcore_multiset :: "'a multiset \<Rightarrow> 'a multiset option" where "pcore_multiset \<equiv> \<lambda>_. Some {#}"
definition op_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" where "op_multiset x y = x + y"
instance proof
show "non_expansive (valid_raw::'a multiset \<Rightarrow> sprop)"
  by (rule non_expansiveI) (auto simp: valid_raw_multiset_def n_equiv_sprop_def)
next
show "non_expansive (pcore::'a multiset \<Rightarrow> 'a multiset option)"
  by (rule non_expansiveI) (auto simp: pcore_multiset_def n_equiv_option_def d_equiv)
next
show "non_expansive2 (op::'a multiset\<Rightarrow>'a multiset\<Rightarrow>'a multiset)" 
  by (rule non_expansive2I) (auto simp: d_equiv)
next
fix a b c :: "'a multiset"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (auto simp: op_multiset_def)
next
fix a b :: "'a multiset"
show "a \<cdot> b = b \<cdot> a" by (auto simp: op_multiset_def)
next
fix a a' :: "'a multiset"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" by (auto simp: op_multiset_def pcore_multiset_def)
next
fix a a' :: "'a multiset"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a" by (auto simp: pcore_multiset_def)
next
fix a a' b :: "'a multiset"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  by (auto simp: op_multiset_def pcore_multiset_def)
next
fix a b :: "'a multiset" and n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  by (auto simp: valid_raw_multiset_def)
next
fix a b1 b2 :: "'a multiset" and n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b1 \<cdot> b2) \<Longrightarrow> \<exists>c1 c2. a = c1 \<cdot> c2 \<and> 
  n_equiv n c1 b1 \<and> n_equiv n c2 b2"
  by (auto simp: valid_raw_multiset_def d_equiv)
qed
end

instance multiset :: (type) dcamera by (standard) (auto simp: valid_def valid_raw_multiset_def)

instantiation multiset :: (type) ucamera begin
definition \<epsilon>_multiset :: "'a multiset" where "\<epsilon>_multiset = {#}"
instance by standard (auto simp: \<epsilon>_multiset_def valid_def valid_raw_multiset_def op_multiset_def pcore_multiset_def)
end

instance multiset :: (type) ducamera ..

lemma multiset_local_update_dealloc: "(x'::'a multiset) \<subseteq># y \<Longrightarrow> (x,y) \<leadsto>\<^sub>L (x-x',y-x')"
  by (auto simp: lup_def valid_raw_multiset_def d_equiv op_multiset_def)

lemma multiset_local_update_alloc: "(x,y::'a multiset) \<leadsto>\<^sub>L (x+x',y+x')"
  by (auto simp: lup_def valid_raw_multiset_def d_equiv op_multiset_def)
end