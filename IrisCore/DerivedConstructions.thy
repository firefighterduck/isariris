theory DerivedConstructions
imports CoreStructures
begin
text \<open> A few basic camera constructions \<close>

text \<open> Tuple/Product type \<close>
instantiation prod :: (camera,camera) camera begin
  lift_definition valid_raw_prod :: "('a \<times> 'b, sprop) non_expansive" is
    "\<lambda>(x,y). Abs_sprop (\<lambda>n. Rep_sprop (rep_valid_raw x) n \<and> Rep_sprop (rep_valid_raw y) n)"
   sorry   
  lift_definition core_prod :: "('a \<times> 'b, ('a \<times> 'b) option) non_expansive" is
    "\<lambda>(x,y). case rep_core x of Some x' \<Rightarrow> (case rep_core y of Some y' \<Rightarrow> Some (x,y) | None \<Rightarrow> None) | None \<Rightarrow> None"
    sorry    
  lift_definition comp_prod :: "(('a \<times> 'b) \<times> 'a \<times> 'b, 'a \<times> 'b) non_expansive" is
    "\<lambda>((x,y),(a,b)). (rep_comp (x,a),rep_comp (y,b))"
    sorry
instance sorry
end

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
  | "n_equiv_sum_camera n Inv Inv = True"
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
  using ofe_limit apply blast using ofe_limit apply blast using ofe_limit apply blast
  using ofe_limit by blast
next
  fix x y :: "('a,'b) sum_camera" 
  show "(x=y) \<Longrightarrow> ofe_eq x y" by (cases x; cases y) (auto intro: ofe_eq_eq)
qed
end

fun sum_core :: "('a::camera,'b::camera) sum_camera \<Rightarrow> ('a,'b) sum_camera option" where
  "sum_core (Inl x) = (case rep_core x of Some x' \<Rightarrow> Some (Inl x') | None \<Rightarrow> None)"
| "sum_core (Inr x) = (case rep_core x of Some x' \<Rightarrow> Some (Inr x') | None \<Rightarrow> None)"
| "sum_core Inv = None"  

fun sum_comp :: "(('a::camera,'b::camera) sum_camera\<times>('a,'b) sum_camera) \<Rightarrow> ('a,'b) sum_camera" where
  "sum_comp (Inl x,Inl y) = Inl (rep_comp (x,y))"
| "sum_comp (Inr x,Inr y) = Inr (rep_comp (x,y))"
| "sum_comp _ = Inv"

instantiation sum_camera :: (camera,camera) camera begin
  lift_definition valid_raw_sum_camera :: "(('a, 'b) sum_camera, sprop) non_expansive" is
    "\<lambda>sum::('a, 'b) sum_camera. (case sum of Inl a \<Rightarrow> rep_valid_raw a | Inr b \<Rightarrow> rep_valid_raw b | Inv \<Rightarrow> sFalse)"
      apply (auto simp: rep_valid_raw_def split: sum_camera.splits)
      using Rep_non_expansive apply blast using Rep_non_expansive apply blast
      by (rule ofe_refl)
  lift_definition core_sum_camera :: "(('a, 'b) sum_camera, ('a, 'b) sum_camera option) non_expansive" is
    "sum_core"
    proof - fix m1 m2 n assume assm: "n_equiv n m1 (m2::('a, 'b) sum_camera)"
    thus "n_equiv n (sum_core m1) (sum_core m2)"
    apply (cases m1; cases m2) apply (auto simp: rep_core_def ofe_refl split: option.splits)
    apply (smt (verit, ccfv_threshold) Rep_non_expansive mem_Collect_eq n_equiv_option_def option.distinct(1))
    apply (smt (verit, ccfv_threshold) Rep_non_expansive mem_Collect_eq n_equiv_option_def option.distinct(1))
    apply (smt (verit) Rep_non_expansive mem_Collect_eq n_equiv_option_def n_equiv_sum_camera.simps(1) option.distinct(1) option.sel)
    apply (smt (verit, best) Rep_non_expansive mem_Collect_eq n_equiv_option_def option.distinct(1))
    apply (smt (verit, best) Rep_non_expansive mem_Collect_eq n_equiv_option_def option.distinct(1))
    by (smt (verit, del_insts) Rep_non_expansive mem_Collect_eq n_equiv_option_def n_equiv_sum_camera.simps(2) option.distinct(1) option.inject)
    qed
  lift_definition comp_sum_camera :: "(('a,'b) sum_camera\<times>('a,'b) sum_camera,('a,'b) sum_camera) non_expansive" is
    "sum_comp"
    proof - fix m1 m2 n 
    assume assm: "n_equiv n m1 (m2::(('a, 'b) sum_camera\<times>('a, 'b) sum_camera))"
    obtain a1 b1 a2 b2 where "m1=(a1,b1)" "m2=(a2,b2)" by fastforce
    thus "n_equiv n (sum_comp m1) (sum_comp m2)"
    apply (cases a1; cases a2; cases b1; cases b2) using assm apply (auto simp: rep_comp_def)
    apply (smt (verit, ccfv_threshold) Rep_non_expansive mem_Collect_eq n_equiv_prod.simps)
    by (smt (verit, ccfv_threshold) Rep_non_expansive mem_Collect_eq n_equiv_prod.simps)
    qed
instance proof (standard)
fix a b c :: "('a,'b) sum_camera"
show "Rep_non_expansive comp (Rep_non_expansive comp (a, b), c) = Rep_non_expansive comp (a, Rep_non_expansive comp (b, c))"
by (cases a; cases b; cases c) (auto simp: rep_comp_def comp_sum_camera.rep_eq camera_assoc)
next
fix a b :: "('a,'b) sum_camera"
show "Rep_non_expansive comp (a, b) = Rep_non_expansive comp (b, a)"
by (cases a; cases b) (auto simp: rep_comp_def comp_sum_camera.rep_eq camera_comm)
next
fix a :: "('a,'b) sum_camera"
show "\<exists>a'. Rep_non_expansive core a = Some a' \<Longrightarrow> Rep_non_expansive comp (the (Rep_non_expansive core a), a) = a"
apply (cases a) unfolding rep_comp_def rep_core_def 
apply (auto simp: core_sum_camera.rep_eq comp_sum_camera.rep_eq camera_core_id split: option.splits)
by (metis camera_core_id option.sel rep_comp_def rep_core_def)+
next
fix a :: "('a,'b) sum_camera"
show "\<exists>a'. Rep_non_expansive core a = Some a' \<Longrightarrow> Rep_non_expansive core (the (Rep_non_expansive core a)) = Rep_non_expansive core a"
apply (cases a) apply (auto simp: rep_core_def core_sum_camera.rep_eq intro: camera_core_idem split: option.splits)
using camera_core_idem apply fastforce using camera_core_idem apply fastforce using camera_core_idem apply fastforce
using camera_core_idem by fastforce
next
fix a b :: "('a,'b) sum_camera"
show "\<lbrakk>\<exists>a'. Rep_non_expansive core a = Some a';\<exists>c. b = Rep_non_expansive comp (a, c)\<rbrakk> \<Longrightarrow>
  \<exists>b'. Rep_non_expansive core b = Some b' \<and>
  (\<exists>c. the (Rep_non_expansive core b) = Rep_non_expansive comp (the (Rep_non_expansive core a), c))"
  sorry
next
fix a b :: "('a,'b) sum_camera"
fix n  
show "Rep_sprop (Rep_non_expansive valid_raw (Rep_non_expansive comp (a, b))) n \<Longrightarrow> Rep_sprop (Rep_non_expansive valid_raw a) n"
by (cases a; cases b) 
(auto simp: rep_valid_raw_def rep_comp_def comp_sum_camera.rep_eq Abs_sprop_inverse valid_raw_sum_camera.rep_eq intro: camera_valid_op split: option.splits)
next
fix a b1 b2 :: "('a,'b) sum_camera"
fix n
show "Rep_sprop (Rep_non_expansive valid_raw a) n \<Longrightarrow>
  n_equiv n a (Rep_non_expansive comp (b1, b2)) \<Longrightarrow> \<exists>c1 c2. a = Rep_non_expansive comp (c1, c2) \<and> n_equiv n c1 b2 \<and> n_equiv n c2 b2"
  apply (cases a; cases b1; cases b2) 
  apply (auto simp: rep_valid_raw_def rep_comp_def comp_sum_camera.rep_eq Abs_sprop_inverse valid_raw_sum_camera.rep_eq intro: camera_extend split: option.splits)
  apply (metis camera_extend n_equiv_sum_camera.simps(1) rep_comp_def sum_comp.simps(1))
  by (metis camera_extend n_equiv_sum_camera.simps(2) rep_comp_def sum_comp.simps(2))
qed
end

lemma sum_update_l: "a\<leadsto>B \<Longrightarrow> (Inl a) \<leadsto> {Inl b |b. b\<in>B}"
apply (auto simp: fup_def rep_comp_def valid_def rep_valid_raw_def comp_sum_camera.rep_eq valid_raw_sum_camera.rep_eq Abs_sprop_inverse split: sum_camera.splits)
apply (smt (z3) rep_comp_def sum_camera.distinct(1) sum_camera.distinct(3) sum_camera.inject(1) sum_comp.simps(1) sum_comp.simps(6) sum_comp.simps(8) sum_core.cases)
by (metis (no_types, lifting) camera_assoc camera_comm comp_sum_camera.rep_eq sum_camera.distinct(5) sum_comp.simps(2) sum_comp.simps(6) sum_comp.simps(8))

lemma sum_update_r: "a\<leadsto>B \<Longrightarrow> (Inr a) \<leadsto> {Inr b |b. b\<in>B}"
sorry (* Same as above *)

lemma sum_swap_l: "\<lbrakk>\<forall>c n. \<not> Rep_sprop (rep_valid_raw (rep_comp (a,c))) n; valid b\<rbrakk> \<Longrightarrow> (Inl a) \<leadsto> {Inr b}"
apply (auto simp: valid_def rep_comp_def rep_valid_raw_def fup_def)
apply (auto simp: rep_valid_raw_def comp_sum_camera.rep_eq valid_raw_sum_camera.rep_eq Abs_sprop_inverse split: sum_camera.splits)
apply (metis (no_types, lifting) camera_assoc camera_comm comp_sum_camera.rep_eq sum_camera.simps(6) sum_comp.simps(1) sum_comp.simps(3))
subgoal for x y z d
proof -
assume assm1:"\<forall>c n. \<not> Rep_sprop (Rep_non_expansive valid_raw (Rep_non_expansive comp (a, c))) n"
assume assms2: "sum_comp (Inl a, x) = sum_camera.Inl z" "All (Rep_sprop (Rep_non_expansive valid_raw z))"
from assm1 have neg: "\<not> Rep_sprop (Rep_non_expansive valid_raw (Rep_non_expansive comp (a, c))) n" for c n
  by blast
from assms2 obtain x' where "x=Inl x'" 
    by (metis sum_camera.distinct(3) sum_comp.simps(6) sum_comp.simps(8) sum_core.cases)
with assms2 have "Rep_non_expansive comp (a,x') = z" 
  by (metis rep_comp_def sum_camera.inject(1) sum_comp.simps(1))
with assms2 have "Rep_sprop (Rep_non_expansive valid_raw (Rep_non_expansive comp (a, x'))) n" for n
  by auto
with neg have False by simp
then show "Rep_sprop (Rep_non_expansive valid_raw d) y" by simp
qed
apply (smt (z3) camera_assoc comp_sum_camera.rep_eq rep_comp_def sum_camera.inject(1) sum_camera.simps(4) sum_comp.simps(1) sum_comp.simps(6) sum_core.cases)
apply (metis (no_types, lifting) camera_assoc camera_comm comp_sum_camera.rep_eq sum_camera.distinct(3) sum_comp.simps(1) sum_comp.simps(3) sum_comp.simps(8))
apply (metis (no_types, lifting) camera_assoc camera_comm comp_sum_camera.rep_eq sum_camera.distinct(5) sum_comp.simps(2) sum_comp.simps(6))
by (metis (no_types, lifting) camera_assoc camera_comm comp_sum_camera.rep_eq sum_camera.simps(8) sum_comp.simps(2) sum_comp.simps(8))

lemma sum_swap_r: "\<lbrakk>\<forall>c n. \<not> Rep_sprop (rep_valid_raw (rep_comp (a,c))) n; valid b\<rbrakk> \<Longrightarrow> (Inr a) \<leadsto> {Inl b}"
sorry (* Same as above *)

fun option_comp :: "(('a::camera) option\<times>'a option) \<Rightarrow> 'a option" where
  "option_comp (Some a, Some b) = Some (rep_comp (a,b))"
| "option_comp _ = None"

text \<open> Option type \<close>
instantiation option :: (camera) camera begin
  definition \<epsilon>_option :: "'a option" where "\<epsilon>_option = None"
  lift_definition valid_raw_option :: "('a option, sprop) non_expansive" is
    "\<lambda>x. (case x of Some a \<Rightarrow> rep_valid_raw a | None \<Rightarrow> sFalse)"
    apply (auto simp: ofe_refl rep_valid_raw_def n_equiv_sprop_def n_equiv_option_def split: option.splits)
    using Rep_non_expansive n_equiv_sprop_def by fastforce+
  lift_definition core_option :: "('a option, 'a option option) non_expansive" is
    "\<lambda>x. (case x of Some a \<Rightarrow> case (rep_core a) of Some a' \<Rightarrow> Some (Some a') | None \<Rightarrow> None | None \<Rightarrow> None)"
    apply (auto simp: rep_core_def n_equiv_option_def split: option.splits)
    apply (metis (mono_tags, lifting) Rep_non_expansive mem_Collect_eq n_equiv_option_def option.simps(3))
    apply (smt (verit, best) Rep_non_expansive mem_Collect_eq n_equiv_option_def option.distinct(1))
    by (smt (verit, ccfv_SIG) Rep_non_expansive mem_Collect_eq n_equiv_option_def option.distinct(1) option.sel)
  lift_definition comp_option :: "('a option \<times> 'a option, 'a option) non_expansive" is
    "option_comp"
    apply (auto simp: n_equiv_option_def rep_comp_def)
    apply (metis (no_types, lifting) Rep_non_expansive mem_Collect_eq n_equiv_prod.simps)
    by (metis (no_types, lifting) Rep_non_expansive mem_Collect_eq n_equiv_prod.simps)
instance proof 
fix a b c :: "'a option"
show "Rep_non_expansive comp (Rep_non_expansive comp (a, b), c) = Rep_non_expansive comp (a, Rep_non_expansive comp (b, c))"
  by (cases a; cases b; cases c) (auto simp: comp_option.rep_eq rep_comp_def camera_assoc)
next
fix a b :: "'a option"
show "Rep_non_expansive comp (a, b) = Rep_non_expansive comp (b, a)"
  by (cases a; cases b) (auto simp: comp_option.rep_eq rep_comp_def camera_comm)
next
fix a :: "'a option"
show "\<exists>a'. Rep_non_expansive core a = Some a' \<Longrightarrow> Rep_non_expansive comp (the (Rep_non_expansive core a), a) = a"
apply (cases a) 
apply (auto simp: comp_option.rep_eq core_option.rep_eq rep_comp_def rep_core_def)
by (metis (mono_tags, lifting) is_none_code(2) is_none_simps(1) camera_core_id option.case_eq_if option.inject option.split_sel option_comp.simps(1) rep_comp_def)
next
fix a :: "'a option"
show "\<exists>a'. Rep_non_expansive core a = Some a' \<Longrightarrow> Rep_non_expansive core (the (Rep_non_expansive core a)) = Rep_non_expansive core a"
apply (cases a) apply (auto simp: core_option.rep_eq rep_core_def split: option.splits)
using camera_core_idem by fastforce+
next
fix a b :: "'a option"
show "\<lbrakk>\<exists>a'. Rep_non_expansive core a = Some a'; \<exists>c. b = Rep_non_expansive comp (a, c)\<rbrakk> \<Longrightarrow>
  \<exists>b'. Rep_non_expansive core b = Some b' 
  \<and> (\<exists>c. the (Rep_non_expansive core b) = Rep_non_expansive comp (the (Rep_non_expansive core a), c))"
  sorry
next
fix a b :: "'a option"
fix n
show "Rep_sprop (Rep_non_expansive valid_raw (Rep_non_expansive comp (a, b))) n \<Longrightarrow> Rep_sprop (Rep_non_expansive valid_raw a) n"
  by (cases a; cases b) (auto simp: comp_option.rep_eq rep_comp_def valid_raw_option.rep_eq rep_valid_raw_def intro: camera_valid_op)
next
fix a b1 b2 :: "'a option"
fix n
show "\<lbrakk>Rep_sprop (Rep_non_expansive valid_raw a) n; n_equiv n a (Rep_non_expansive comp (b1, b2))\<rbrakk>
   \<Longrightarrow> \<exists>c1 c2. a = Rep_non_expansive comp (c1, c2) \<and> n_equiv n c1 b2 \<and> n_equiv n c2 b2"
   apply (cases a; cases b1; cases b2) 
   apply (auto simp: comp_option.rep_eq rep_comp_def valid_raw_option.rep_eq rep_valid_raw_def n_equiv_option_def)
   by (metis camera_extend option_comp.simps(1) rep_comp_def)
qed
end  
end
