theory DerivedConstructions
imports CoreStructures
begin
text \<open> A few basic camera constructions \<close>

text \<open> Tuple/Product type \<close>
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

instance prod :: (core_id,core_id) core_id by standard (auto simp: pcore_prod_def pcore_id)

instance prod :: (dcamera,dcamera) dcamera 
  apply (standard; auto simp: valid_raw_prod_def valid_def sprop_conj.rep_eq)
  using d_valid[simplified valid_def] by blast+

instantiation prod :: (ucamera,ucamera) ucamera begin
definition \<epsilon>_prod :: "'a \<times> 'b" where [simp]: "\<epsilon>_prod = (\<epsilon>,\<epsilon>)"
instance by standard 
  (auto simp: valid_raw_prod_def sprop_conj.rep_eq pcore_prod_def op_prod_def valid_def 
    \<epsilon>_left_id \<epsilon>_pcore \<epsilon>_valid[unfolded valid_def]) 
end

instance prod :: (ducamera,ducamera) ducamera ..

text \<open> Sum type \<close>
datatype ('a::camera,'b::camera) sum_camera = Inl 'a | Inr 'b | Inv
instantiation sum_camera :: (camera,camera) ofe begin
  fun ofe_eq_sum_camera :: "('a, 'b) sum_camera \<Rightarrow> ('a, 'b) sum_camera \<Rightarrow> bool" where
    "ofe_eq_sum_camera (Inl a) (Inl b) = ofe_eq a b"
  | "ofe_eq_sum_camera (Inr a) (Inr b) = ofe_eq a b"
  | "ofe_eq_sum_camera Inv Inv = True"
  | "ofe_eq_sum_camera _ _ = False"
  fun n_equiv_sum_camera :: "nat \<Rightarrow> ('a,'b) sum_camera \<Rightarrow> ('a,'b) sum_camera \<Rightarrow> bool" where
    "n_equiv_sum_camera n (Inl x) (Inl y) = n_equiv n x y"
  | "n_equiv_sum_camera n (Inr x) (Inr y) =  n_equiv n x y"
  | "n_equiv_sum_camera _ Inv Inv = True"
  | "n_equiv_sum_camera _ _ _ = False"
instance proof
  fix n x
  show "n_equiv n x (x::('a,'b) sum_camera)" by (cases x) (auto simp: ofe_refl)
next
  fix n x y
  show "n_equiv n x y = n_equiv n y (x::('a,'b) sum_camera)" 
    by (cases x; cases y) (auto simp: ofe_sym)
next
  fix n x y z 
  show "n_equiv n x y \<Longrightarrow> n_equiv n y z \<Longrightarrow> n_equiv n x (z::('a,'b) sum_camera)"
    by (cases x; cases y; cases z) (auto intro: ofe_trans)
next
  fix m n x y
  show "m \<le> n \<Longrightarrow> n_equiv n x y \<Longrightarrow> n_equiv m x (y::('a,'b) sum_camera)"
  by (cases x; cases y) (auto intro: ofe_mono)
next
  fix x y :: "('a,'b) sum_camera"
  show "ofe_eq x y \<longleftrightarrow> (\<forall>n. n_equiv n x y)"
  apply (cases x; cases y) apply (auto intro: ofe_limit)
  using ofe_limit by blast+
next
  fix x y :: "('a,'b) sum_camera" 
  show "(x=y) \<Longrightarrow> ofe_eq x y" by (cases x; cases y) (auto intro: ofe_eq_eq)
qed
end
instance sum_camera :: (dcamera,dcamera) discrete 
proof
fix a b :: "('a,'b) sum_camera" fix n
show "n_equiv n a b = (a = b)" by (cases a; cases b) (auto simp: d_equiv)
next
fix a b :: "('a,'b) sum_camera"
show "ofe_eq a b = (a = b)" by (cases a; cases b) (auto simp: d_eq)
qed

fun sum_pcore :: "('a::camera,'b::camera) sum_camera \<Rightarrow> ('a,'b) sum_camera option" where
  "sum_pcore (Inl x) = (case pcore x of Some x' \<Rightarrow> Some (Inl x') | None \<Rightarrow> None)"
| "sum_pcore (Inr x) = (case pcore x of Some x' \<Rightarrow> Some (Inr x') | None \<Rightarrow> None)"
| "sum_pcore Inv = Some Inv"  

lemma sum_pcore_ne: "non_expansive sum_pcore"
proof (rule non_expansiveI)
fix n x y
assume "n_equiv n x (y::('a,'b) sum_camera)"
then show "n_equiv n (sum_pcore x) (sum_pcore y)" 
  by (cases x; cases y; auto simp: ofe_refl ofe_sym n_equiv_option_def split: option.splits)
  (metis option.distinct(1) option.sel pcore_ne n_equiv_option_def)+
qed

instantiation sum_camera :: (camera,camera) camera begin
  definition valid_raw_sum_camera :: "('a,'b) sum_camera \<Rightarrow> sprop" where
    "valid_raw_sum_camera s \<equiv> case s of (Inl a) \<Rightarrow> valid_raw a | Inr b \<Rightarrow> valid_raw b | Inv \<Rightarrow> sFalse"
  definition "pcore_sum_camera \<equiv> sum_pcore"
  definition op_sum_camera :: "('a,'b) sum_camera \<Rightarrow> ('a,'b) sum_camera \<Rightarrow> ('a,'b) sum_camera" where
    "op_sum_camera x y = (case (x,y) of (Inl x', Inl y') \<Rightarrow> Inl (x' \<cdot> y') 
    | (Inr x', Inr y') \<Rightarrow> Inr (x' \<cdot> y') | _ \<Rightarrow> Inv)"
instance proof
show "non_expansive (valid_raw::('a,'b) sum_camera \<Rightarrow> sprop)"
  by (rule non_expansiveI;auto simp: valid_raw_sum_camera_def split: sum_camera.splits)
  (auto simp: n_equiv_sprop_def)
next
show "non_expansive (pcore::('a,'b) sum_camera \<Rightarrow> ('a,'b) sum_camera option)"
  by (simp add: sum_pcore_ne pcore_sum_camera_def)
next
show "non_expansive2 (op::('a,'b) sum_camera \<Rightarrow> ('a,'b) sum_camera \<Rightarrow> ('a,'b) sum_camera)"
proof (rule non_expansive2I)
fix x y a b :: "('a,'b) sum_camera"
fix n
assume " n_equiv n x y" "n_equiv n a b"
then show "n_equiv n (x \<cdot> a) (y \<cdot> b)"
  by (cases x; cases y; cases a; cases b) (auto simp: ofe_refl ofe_sym op_sum_camera_def)
qed
next
fix a b c :: "('a,'b) sum_camera"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" 
  by (cases a; cases b; cases c) (auto simp: op_sum_camera_def camera_assoc)
next
fix a b :: "('a,'b) sum_camera"
show "a \<cdot> b = b \<cdot> a" by (cases a; cases b) (auto simp: op_sum_camera_def camera_comm)
next
fix a a' :: "('a,'b) sum_camera"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" by (cases a; cases a') 
  (auto simp: pcore_sum_camera_def op_sum_camera_def camera_pcore_id split: option.splits)
next
fix a a' :: "('a,'b) sum_camera"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a" by (cases a; cases a')
  (auto simp: pcore_sum_camera_def camera_pcore_idem split: option.splits)
next
fix a a' b :: "('a,'b) sum_camera"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  apply (cases a; cases a'; cases b) 
  apply (auto simp: pcore_sum_camera_def op_sum_camera_def split: option.splits sum_camera.splits)
  using camera_pcore_mono apply blast
  apply (metis camera_pcore_mono option.inject sum_camera.inject(1) sum_camera.simps(4) sum_camera.simps(6))
  using camera_pcore_mono apply blast
  by (metis  camera_pcore_mono option.inject sum_camera.distinct(1) sum_camera.inject(2) sum_camera.simps(8))
next
fix a b :: "('a,'b) sum_camera"
fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n" by (cases a; cases b) 
  (auto simp: valid_raw_sum_camera_def op_sum_camera_def camera_valid_op split: sum_camera.splits)
next
fix a b c :: "('a,'b) sum_camera"
fix n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b \<cdot> c) \<Longrightarrow> 
  \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c" apply (cases a; cases b; cases c) 
  apply (auto simp: valid_raw_sum_camera_def op_sum_camera_def split: sum_camera.splits)
  using camera_extend by fast+
qed
end

instance sum_camera :: (dcamera,dcamera) dcamera
  apply (standard; auto simp: valid_raw_sum_camera_def valid_def split: sum_camera.splits)
  using d_valid[simplified valid_def] by blast+

instance sum_camera :: (core_id,core_id) core_id 
proof
fix a :: "('a,'b) sum_camera"
show "pcore a = Some a" by (cases a) (auto simp: pcore_sum_camera_def pcore_id)
qed

lemma sum_update_l: "a\<leadsto>B \<Longrightarrow> (Inl a) \<leadsto> {Inl b |b. b\<in>B}"
by (auto simp: fup_def op_sum_camera_def valid_def valid_raw_sum_camera_def split: sum_camera.splits)
  blast

lemma sum_update_r: "a\<leadsto>B \<Longrightarrow> (Inr a) \<leadsto> {Inr b |b. b\<in>B}"
by (auto simp: fup_def op_sum_camera_def valid_def valid_raw_sum_camera_def split: sum_camera.splits)

lemma sum_swap_l: "\<lbrakk>\<forall>c n. \<not> n_valid (op a c) n; valid b\<rbrakk> \<Longrightarrow> (Inl a) \<leadsto> {Inr b}"
by (auto simp: valid_def fup_def valid_raw_sum_camera_def op_sum_camera_def split: sum_camera.splits)

lemma sum_swap_r: "\<lbrakk>\<forall>c n. \<not> Rep_sprop (valid_raw (op a c)) n; valid b\<rbrakk> \<Longrightarrow> (Inr a) \<leadsto> {Inl b}"
by (auto simp: valid_def fup_def valid_raw_sum_camera_def op_sum_camera_def split: sum_camera.splits)

text \<open> Option type \<close>
fun option_op :: "('a::camera) option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "option_op (Some a) (Some b) = Some (op a b)"
| "option_op (Some a) (None) = Some a"
| "option_op (None) (Some a) = Some a"  
| "option_op _ _ = None"

lemma option_op_ne: "non_expansive2 option_op"
proof (rule non_expansive2I)
fix x y a b :: "'a option"
fix n
show "n_equiv n x y \<Longrightarrow> n_equiv n a b \<Longrightarrow> n_equiv n (option_op x a) (option_op y b)"
  by (cases x; cases y; cases a; cases b) (auto simp: n_equiv_option_def split: option.splits)
qed

instantiation option :: (camera) camera begin
  definition valid_raw_option :: "'a option \<Rightarrow> sprop" where
    "valid_raw_option x = (case x of Some a \<Rightarrow> valid_raw a | None \<Rightarrow> sTrue)"
  definition pcore_option :: "'a option \<Rightarrow> 'a option option" where
    "pcore_option x = (case x of Some a \<Rightarrow> Some (pcore a) | None \<Rightarrow> Some None)"
  definition "op_option \<equiv> option_op"
instance proof
show "non_expansive (valid_raw::'a option \<Rightarrow> sprop)" by (rule non_expansiveI) 
  (auto simp: valid_raw_option_def ofe_refl n_equiv_option_def valid_raw_ne split: option.splits)
next
show "non_expansive (pcore::'a option \<Rightarrow> 'a option option)" 
  by (rule non_expansiveI;auto simp: pcore_option_def ofe_refl pcore_ne n_equiv_option_def split: option.split)
  (meson n_equiv_option_def pcore_ne)+
next
show "non_expansive2 (op::'a option \<Rightarrow> 'a option \<Rightarrow> 'a option)"
  by (simp add: op_option_def option_op_ne)
next
fix a b c :: "'a option"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (cases a; cases b; cases c) (auto simp: op_option_def camera_assoc)
next
fix a b :: "'a option"
show "a \<cdot> b = b \<cdot> a" by (cases a; cases b) (auto simp: op_option_def camera_comm)
next
fix a a' :: "'a option"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a"
  by (cases a; cases a') (auto simp: op_option_def pcore_option_def camera_pcore_id)
next
fix a a' :: "'a option"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a"
  by (cases a; cases a') (auto simp: pcore_option_def camera_pcore_idem)
next
fix a a' b :: "'a option"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  apply (cases a; cases a'; cases b)
  apply (auto simp: pcore_option_def op_option_def)
  apply (metis option.exhaust option_op.simps(3) option_op.simps(4))
  apply (metis option_op.simps(4))
  apply (metis option.exhaust option_op.simps(3) option_op.simps(4))
  apply (metis option.distinct(1) option_op.elims)
  by (metis camera_pcore_mono not_Some_eq option.inject option_op.simps(1) option_op.simps(2))
next
fix a b :: "'a option"
fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  by (cases a; cases b) (auto simp: valid_raw_option_def op_option_def camera_valid_op)
next
fix a b c :: "'a option"
fix n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b \<cdot> c) \<Longrightarrow> 
  \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c"
  apply (cases a; cases b; cases c; auto simp: valid_raw_option_def op_option_def n_equiv_option_def)
  using camera_extend by force+
qed
end

instance option :: (dcamera) dcamera
  apply (standard; auto simp: valid_raw_option_def valid_def split: option.splits)
  using d_valid[simplified valid_def] by blast

instance option :: (core_id) core_id 
  by standard(auto simp: pcore_option_def  pcore_id split: option.splits)

instantiation option :: (camera) ucamera begin
definition [simp]: "\<epsilon>_option \<equiv> None"
instance by (standard; auto simp: valid_def valid_raw_option_def op_option_def pcore_option_def)
  (metis not_Some_eq option_op.simps(3) option_op.simps(4))
end

instance option :: (dcamera) ducamera ..

text \<open> Agreement camera functor \<close>
typedef 'a::ofe ag = "{a::'a set | a. finite a \<and> a\<noteq>{} }"
  by auto
setup_lifting type_definition_ag  

instantiation ag :: (ofe) ofe begin
lift_definition n_equiv_ag :: "nat \<Rightarrow> ('a::ofe) ag \<Rightarrow> 'a ag \<Rightarrow> bool" is
  "\<lambda>n a b. (\<forall>x\<in>a. \<exists>y\<in>b. n_equiv n x y) \<and> (\<forall>y\<in>b. \<exists>x\<in>a. n_equiv n x y)" .
definition ofe_eq_ag :: "('a::ofe) ag \<Rightarrow> 'a ag \<Rightarrow> bool" where
  "ofe_eq_ag a b \<equiv> \<forall>n. n_equiv n a b"
lemmas defs = n_equiv_ag.rep_eq ofe_eq_ag_def
instance by (standard) (auto 4 4 simp: defs ofe_sym intro: ofe_refl ofe_trans ofe_mono)
end
instance ag :: (discrete) discrete apply standard
  apply (auto simp: n_equiv_ag.rep_eq d_equiv ofe_eq_ag_def)
  using Rep_ag_inject by blast+

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
  apply auto
  apply (metis equals0D ofe_refl singleton_Un_iff)
  by (metis equals0D ofe_refl singleton_Un_iff)
from assms have "Rep_sprop (valid_raw (b\<cdot>c)) n"
  by transfer (metis empty_iff insert_iff ofe_sym ofe_trans)
from assms have "n_equiv n a b" by (transfer;auto;meson UnI1 ofe_trans)
moreover from assms have "n_equiv n a c" by (transfer;auto;meson UnI2 ofe_trans)
moreover have "a=a\<cdot>a" by (auto simp: op_ag_def Rep_ag_inverse)
ultimately show "\<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c"
  by blast
qed
end

instance ag :: (dcamera) dcamera
  by standard (auto simp: valid_raw_ag.rep_eq valid_def d_equiv split: option.splits)
  
instance ag :: (ofe) core_id by standard (auto simp: pcore_ag_def)

lift_definition to_ag :: "'a::ofe \<Rightarrow> 'a ag" is "\<lambda>a::'a. {a}" by simp
lemma to_ag_valid: "valid (to_ag a)"
  by (auto simp: to_ag.rep_eq valid_def valid_raw_ag.rep_eq)
  
lemma to_ag_op: "(to_ag a) = b\<cdot>c \<Longrightarrow> (b=to_ag a) \<and> (c=to_ag a)"
proof -
  assume assm: "to_ag a = b\<cdot>c"
  then have "{a} = Rep_ag b \<union> Rep_ag c" by (metis assm op_ag.rep_eq to_ag.rep_eq)
  then have "Rep_ag b = {a}" "Rep_ag c = {a}" using Rep_ag by fast+
  then show "(b=to_ag a) \<and> (c=to_ag a)" by (metis Rep_ag_inverse to_ag.abs_eq)
qed
  
text \<open> Exclusive camera functor\<close>

datatype 'a::ofe ex = Ex 'a | Inv
instantiation ex :: (ofe) ofe begin
fun n_equiv_ex :: "nat \<Rightarrow> 'a ex \<Rightarrow> 'a ex \<Rightarrow> bool" where
  "n_equiv_ex n (Ex a) (Ex b) = n_equiv n a b"
| "n_equiv_ex _ Inv Inv = True"
| "n_equiv_ex _ _ _ = False"
fun ofe_eq_ex :: "'a ex \<Rightarrow> 'a ex \<Rightarrow> bool" where
  "ofe_eq_ex (Ex a) (Ex b) = ofe_eq a b"
| "ofe_eq_ex Inv Inv = True"
| "ofe_eq_ex _ _ = False"
instance proof
fix x n show "n_equiv n x (x::'a ex)" by (cases x) (auto intro: ofe_refl)
next fix n x y show "n_equiv n x y = n_equiv n y (x::'a ex)" by (cases x; cases y) (auto simp: ofe_sym)
next fix n x y z show "n_equiv n x y \<Longrightarrow> n_equiv n y z \<Longrightarrow> n_equiv n x (z::'a ex)"
  by (cases x; cases y; cases z) (auto intro: ofe_trans)
next fix m n x y show "m \<le> n \<Longrightarrow> n_equiv n x y \<Longrightarrow> n_equiv m x (y::'a ex)" 
  by (cases x; cases y) (auto intro: ofe_mono)
next fix x y show "ofe_eq x y \<longleftrightarrow> (\<forall>n. n_equiv n x (y::'a ex))" 
  apply (cases x; cases y) apply (auto) using ofe_limit by blast+
next fix x y show "x = y \<Longrightarrow> ofe_eq x (y::'a ex)" by (cases x; cases y) (auto intro: ofe_eq_eq)
qed
end
instance ex :: (discrete) discrete
proof
fix a b :: "'a ex" fix n
show "n_equiv n a b = (a = b)" by (cases a; cases b) (auto simp: d_equiv)
next
fix a b :: "'a ex"
show "ofe_eq a b = (a = b)" by (cases a; cases b) (auto simp: d_eq)
qed

instantiation ex :: (ofe) camera begin
definition valid_raw_ex :: "'a ex \<Rightarrow> sprop" where 
  "valid_raw_ex x = (case x of Ex _ \<Rightarrow> sTrue | Inv \<Rightarrow> sFalse)" 
definition pcore_ex :: "'a ex \<Rightarrow> 'a ex option" where
  "pcore_ex x = (case x of Ex _ \<Rightarrow> None | Inv \<Rightarrow> Some Inv)"
definition op_ex :: "'a ex \<Rightarrow> 'a ex \<Rightarrow> 'a ex" where [simp]: "op_ex _ _ = Inv"
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

instance ex :: (discrete) dcamera by (standard; auto simp: valid_raw_ex_def valid_def split: ex.splits)

text \<open> Authoritative camera functor \<close>
datatype 'm auth = Auth "('m ex option\<times>'m)"
instantiation auth :: (ucamera) ofe begin
fun n_equiv_auth :: "nat \<Rightarrow> 'a auth \<Rightarrow> 'a auth \<Rightarrow> bool" where
  "n_equiv_auth n (Auth a) (Auth b) = n_equiv n a b"
fun ofe_eq_auth :: "'a auth \<Rightarrow> 'a auth \<Rightarrow> bool" where
  "ofe_eq_auth (Auth a) (Auth b) = ofe_eq a b"
instance proof
fix n x show "n_equiv n x (x::'a auth)" by (cases x) (auto intro: ofe_refl) next
fix n x y show "n_equiv n x y \<longleftrightarrow> n_equiv n y (x::'a auth)" 
  by (cases x; cases y) (auto simp: ofe_sym) next
fix n x y z show "n_equiv n x y \<Longrightarrow> n_equiv n y z \<Longrightarrow> n_equiv n x (z::'a auth)"
  by (cases x; cases y; cases z) (auto intro: ofe_trans) next 
fix m n x y show "m \<le> n \<Longrightarrow> n_equiv n x y \<Longrightarrow> n_equiv m x (y::'a auth)"
  by (cases x; cases y) (auto intro: ofe_mono) next
fix x y show "ofe_eq x y \<longleftrightarrow> (\<forall>n. n_equiv n x (y::'a auth))" apply (cases x; cases y; auto)
  using ofe_limit by blast+ next
fix x y show " x = y \<Longrightarrow> ofe_eq x (y::'a auth)" by (cases x; cases y) (auto intro: ofe_eq_eq)
qed
end
instance auth :: (ducamera) discrete
proof
fix a b :: "'a auth" fix n
show "n_equiv n a b = (a = b)" by (cases a; cases b) (auto simp: d_equiv)
next
fix a b :: "'a auth"
show "ofe_eq a b = (a = b)" by (cases a; cases b) (auto simp: d_eq)
qed

lemma valid_raw_auth_aux: "(\<lambda>n. \<exists>c. x = ex.Ex c \<and> n_incl n (y::'a::ucamera) c \<and> n_valid c n) \<in> 
  {s. \<forall>n m. m \<le> n \<longrightarrow> s n \<longrightarrow> s m}" apply (auto simp: n_incl_def) using ofe_mono by blast

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
apply (auto simp: n_incl_def)
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
  apply (auto simp: pcore_auth_def op_auth_def op_prod_def split: auth.splits)
  apply (metis \<epsilon>_left_id \<epsilon>_option_def)
  using camera_core_id by auto
next
fix a a' :: "'a auth"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a"
by (auto simp: pcore_auth_def camera_pcore_idem core_def total_pcore split: auth.splits)
next
fix a a' b :: "'a auth"
assume assms: "pcore a = Some a'" "\<exists>c. b = a \<cdot> c"
obtain c d where a:"a = Auth (c,d)" using auth.exhaust by auto
then have a': "a' = Auth (None, core d)" using assms(1) pcore_auth_def by force
from assms(2) a obtain x y where c: "b = Auth ((c,d)\<cdot>(x,y))" apply (auto simp: op_auth_def split: auth.splits)
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
    using a b c n apply (auto simp: op_auth_def op_prod_def op_option_def)
    apply (metis n_equiv_option_def not_Some_eq option_op.elims)
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
  apply (auto simp: valid_raw_auth_def Abs_sprop_inverse[OF valid_raw_auth_aux2] valid_def n_incl_def 
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
show "op \<epsilon> a = a" apply (auto simp: op_auth_def \<epsilon>_auth_def op_prod_def split: auth.splits)
  using \<epsilon>_left_id[simplified ] \<epsilon>_option_def by metis+
next
show "pcore (\<epsilon>::'a auth) = Some \<epsilon>" by (auto simp: \<epsilon>_auth_def pcore_auth_def \<epsilon>_core split: auth.splits)
qed
end

instance auth :: (ducamera) ducamera ..

abbreviation full :: "'m::ucamera \<Rightarrow> 'm auth" where "full \<equiv> \<lambda>a::'m. Auth (Some (Ex a), \<epsilon>)"
abbreviation fragm :: "'m::ucamera \<Rightarrow> 'm auth" where "fragm \<equiv> \<lambda>a::'m. Auth (None, a)"
abbreviation comb :: "'m::ucamera \<Rightarrow> 'm \<Rightarrow> 'm auth" where "comb \<equiv> \<lambda>(a::'m) b. Auth (Some (Ex a), b)"

lemma auth_frag_op: "fragm (a\<cdot>b) = fragm a \<cdot> fragm b"
  by (auto simp: op_auth_def op_prod_def op_option_def)

lemma [simp]: "n_valid (Auth (a,b)::('m::ucamera) auth) n \<equiv> (a = None \<and> n_valid b n \<or> (\<exists>c. a = Some (ex.Ex c) \<and> n_incl n b c \<and> n_valid c n))"
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

text \<open> Map functors, based on a simple wrapper type \<close>

text \<open>
  As maps are only functions to options and thus can't directly be declared as class instances, 
  we need a bit of class magic. Based on ideas from the AFP entry Separation Logic Algebra.
\<close>
class opt = ucamera + fixes none assumes none_\<epsilon>: "\<epsilon> = none"
instantiation option :: (camera) opt begin definition [simp]: "none \<equiv> None" instance 
  by standard (auto simp: ofe_eq_option_def)
end

instantiation "fun" :: (type,ofe) ofe begin
definition n_equiv_fun :: "nat \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool" where
  "n_equiv_fun n m1 m2 \<equiv> \<forall>i. n_equiv n (m1 i) (m2 i)"
definition ofe_eq_fun :: "('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool" where
  "ofe_eq_fun m1 m2 \<equiv> \<forall>i. ofe_eq (m1 i) (m2 i)"
instance by (standard, unfold n_equiv_fun_def ofe_eq_fun_def) 
  (auto simp: ofe_sym  ofe_limit intro: ofe_refl ofe_trans ofe_mono ofe_limit ofe_eq_eq)
end

instance "fun" :: (type,discrete) discrete 
  by standard (auto simp: n_equiv_fun_def d_equiv ofe_eq_fun_def d_eq)

(* No cofe instantiation because I have no idea how the Coq maps work for this one. *)

lemma pcore_op_opt[simp]: "(case pcore x of None \<Rightarrow> none | Some a \<Rightarrow> a) \<cdot> (x::'b::opt) = x"
  apply (cases "pcore x")
  apply (auto simp: camera_pcore_id)
  using \<epsilon>_left_id none_\<epsilon> by metis
  
instantiation "fun" :: (type, opt) camera begin
lift_definition valid_raw_fun :: "('a\<Rightarrow>'b) \<Rightarrow> sprop" is
  "\<lambda>m n. \<forall>i. n_valid (m i) n" by simp
definition pcore_fun :: "('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) option" where
  "pcore_fun m = Some ((\<lambda>b. case pcore b of Some a \<Rightarrow> a | None \<Rightarrow> none) \<circ> m)"
definition op_fun :: "('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b)" where
  "op_fun m1 m2 = (\<lambda>i. (m1 i) \<cdot> (m2 i))"
instance proof
show "non_expansive (valid_raw::('a\<Rightarrow>'b) \<Rightarrow> sprop)"
  by (rule non_expansiveI; auto simp: valid_raw_fun_def n_equiv_sprop_def Abs_sprop_inverse)
  (meson n_equiv_fun_def n_valid_ne ofe_mono ofe_sym)+
next
show "non_expansive (pcore::('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) option)"
  apply (rule non_expansiveI)
  apply (auto simp: pcore_fun_def n_equiv_fun_def split: option.splits)
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
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" by (auto simp: pcore_fun_def op_fun_def)
next
fix a a' :: "'a\<Rightarrow>'b"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a" by (auto simp: pcore_fun_def)
  (smt (z3) \<epsilon>_pcore camera_pcore_idem comp_apply comp_assoc fun.map_cong0 none_\<epsilon> option.case_eq_if option.collapse option.simps(5))
next
fix a a' b :: "'a\<Rightarrow>'b"
assume assms: "\<exists>c. b = a \<cdot> c"
then obtain c where c: "b = a \<cdot> c" by blast
then have "\<forall>i. b i = a i \<cdot> c i" by (auto simp: op_fun_def)
then have i: "\<forall>i. \<exists>j. (case pcore (a i \<cdot> c i) of None \<Rightarrow> none | Some a \<Rightarrow> a) = (case pcore (a i) of None \<Rightarrow> none | Some a \<Rightarrow> a) \<cdot> j"
  by (metis option.simps(5) camera_pcore_mono total_pcore)
define cs where cs: "cs \<equiv> {(i,j) | i j. (case pcore (a i \<cdot> c i) of None \<Rightarrow> none | Some a \<Rightarrow> a) = (case pcore (a i) of None \<Rightarrow> none | Some a \<Rightarrow> a) \<cdot> j}"
with i have "\<forall>i. \<exists>j. (i,j) \<in> cs" by simp
then obtain cf where "\<forall>i. (i, cf i) \<in> cs" by metis
with i cs have "\<forall>i. (case pcore (a i \<cdot> c i) of None \<Rightarrow> none | Some a \<Rightarrow> a) = (case pcore (a i) of None \<Rightarrow> none | Some a \<Rightarrow> a) \<cdot> cf i"
  by simp
then have "(\<lambda>b. case pcore b of None \<Rightarrow> none | Some a \<Rightarrow> a) \<circ> (\<lambda>i. a i \<cdot> c i) = (\<lambda>i. (case pcore (a i) of None \<Rightarrow> none | Some a \<Rightarrow> a) \<cdot> cf i)"
  by auto  
then show "pcore a = Some a' \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  by (auto simp: pcore_fun_def op_fun_def c)
next
fix a b :: "'a\<Rightarrow>'b"
fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  apply (auto simp: valid_raw_fun_def op_fun_def)
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

class d_opt = opt + dcamera
instance option :: (dcamera) d_opt ..

instance "fun" :: (type,d_opt) dcamera 
  apply (standard; auto simp: valid_raw_fun.rep_eq valid_def)
  using d_valid[simplified valid_def] by blast

class opt_core_id = opt + core_id
instance "fun" :: (type,opt_core_id) core_id by standard (auto simp: pcore_fun_def pcore_id)

instantiation "fun" :: (type, opt) ucamera begin
definition \<epsilon>_fun :: "'a\<Rightarrow>'b" where [simp]: "\<epsilon>_fun \<equiv> (\<lambda>_. \<epsilon>)"
instance apply (standard)
apply (auto simp: valid_def valid_raw_fun_def Abs_sprop_inverse valid_raw_option_def)
subgoal using Rep_sprop_inverse \<epsilon>_valid valid_def by auto
subgoal by (auto simp: op_fun_def \<epsilon>_left_id)
by (auto simp: pcore_fun_def \<epsilon>_pcore split: option.splits)
end

instance "fun" :: (type,d_opt) ducamera ..

text \<open> Set type camera \<close>
instantiation set :: (type) ofe begin
definition n_equiv_set :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "n_equiv_set _ \<equiv> (=)"
definition ofe_eq_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "ofe_eq_set \<equiv> (=)"
instance by (standard) (auto simp: n_equiv_set_def ofe_eq_set_def)
end
instance set :: (type) discrete by standard (auto simp: n_equiv_set_def ofe_eq_set_def)

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
definition \<epsilon>_set :: "'a set" where [simp]: "\<epsilon>_set = {}"
instance by (standard) (auto simp: op_set_def valid_def valid_raw_set_def pcore_set_def)
end

instance set :: (type) ducamera ..


text \<open> Unit type camera \<close>
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
end