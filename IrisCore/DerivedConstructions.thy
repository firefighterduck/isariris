theory DerivedConstructions
imports CoreStructures HOL.Rat
begin
text \<open> A few basic camera constructions \<close>

text \<open> Tuple/Product type \<close>
instantiation prod :: (camera,camera) camera begin
  lift_definition valid_raw_prod :: "('a \<times> 'b, sprop) non_expansive" is
    "\<lambda>(x,y). Abs_sprop (\<lambda>n. valid_n x n \<and> valid_n y n)"
    apply (auto simp: n_equiv_sprop_def ne_sprop_weaken ofe_mono ofe_sym split: prod.splits)
    apply (smt (z3) Abs_sprop_inverse mem_Collect_eq ne_sprop_weaken ofe_mono ofe_refl order_refl)
    proof -
    fix nat :: nat and x1 :: 'a and x2 :: 'b and x1a :: 'a and x2a :: 'b and m :: nat
    assume a1: "m \<le> nat"
    assume a2: "n_equiv nat x2 x2a"
    assume a3: "Rep_sprop (Abs_sprop (\<lambda>n. valid_n x1a n \<and> valid_n x2a n)) m"
    assume "n_equiv nat x1 x1a"
    then have f4: "n_equiv nat (rep_valid_raw x1) (rep_valid_raw x1a)"
    using Rep_non_expansive by blast
    have "n_equiv m x2a x2"
    using a2 a1 by (meson ofe_mono ofe_sym)
    then show "Rep_sprop (Abs_sprop (\<lambda>n. valid_n x1 n \<and> valid_n x2 n)) m"
    using f4 a3 a1 by (simp add: Abs_sprop_inverse n_equiv_sprop_def ne_sprop_weaken)
    qed
  lift_definition core_prod :: "('a \<times> 'b, ('a \<times> 'b) option) non_expansive" is
    "\<lambda>(x,y). case rep_core x of Some x' \<Rightarrow> (case rep_core y of Some y' \<Rightarrow> Some (x,y) | None \<Rightarrow> None) | None \<Rightarrow> None"
    apply (auto simp: n_equiv_option_def ofe_refl split: option.splits)
    apply (metis option.distinct(1) core_ne)
    apply (metis option.distinct(1) core_ne)
    by (metis core_ne not_None_eq ofe_sym)+
  lift_definition comp_prod :: "(('a \<times> 'b) \<times> 'a \<times> 'b, 'a \<times> 'b) non_expansive" is
    "\<lambda>((x,y),(a,b)). (rep_comp (x,a),rep_comp (y,b))" by auto
instance sorry
end

instantiation prod :: (total_camera,total_camera) total_camera begin
definition \<epsilon>_prod :: "'a \<times> 'b" where [simp]: "\<epsilon>_prod = (\<epsilon>,\<epsilon>)"
instance apply standard 
apply (auto simp: valid_raw_prod.rep_eq core_prod.rep_eq comp_prod.rep_eq valid_def total_camera_class.\<epsilon>_left_id total_camera_class.\<epsilon>_core)
proof -
fix n
have "valid_n (\<epsilon>::'a) m" for m using \<epsilon>_valid valid_def by blast
moreover have "valid_n (\<epsilon>::'b) m" for m using \<epsilon>_valid valid_def by blast
ultimately show "Rep_sprop (Abs_sprop (\<lambda>n. valid_n \<epsilon> n \<and> valid_n \<epsilon> n)) n"
by (smt (z3) Abs_sprop_inverse \<epsilon>_valid mem_Collect_eq valid_def)
qed
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
      by (auto split: sum_camera.splits) (rule ofe_refl)
  lift_definition core_sum_camera :: "(('a, 'b) sum_camera, ('a, 'b) sum_camera option) non_expansive" is
    "sum_core"
    proof - fix m1 m2 n assume assm: "n_equiv n m1 (m2::('a, 'b) sum_camera)"
    thus "n_equiv n (sum_core m1) (sum_core m2)"
    apply (cases m1; cases m2) apply (auto simp: ofe_refl split: option.splits)
    apply (metis core_ne ofe_sym option.simps(3))
    apply (metis core_ne option.simps(3))
    using core_ne n_equiv_option_def apply fastforce
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
    apply (cases a1; cases a2; cases b1; cases b2) using assm by (auto)
    qed
instance proof (standard)
fix a b c :: "('a,'b) sum_camera"
show "Rep_non_expansive comp (Rep_non_expansive comp (a, b), c) = Rep_non_expansive comp (a, Rep_non_expansive comp (b, c))"
by (cases a; cases b; cases c) (auto simp:  comp_sum_camera.rep_eq camera_assoc)
next
fix a b :: "('a,'b) sum_camera"
show "Rep_non_expansive comp (a, b) = Rep_non_expansive comp (b, a)"
by (cases a; cases b) (auto simp:  comp_sum_camera.rep_eq camera_comm)
next
fix a :: "('a,'b) sum_camera"
show "\<exists>a'. Rep_non_expansive core a = Some a' \<Longrightarrow> Rep_non_expansive comp (the (Rep_non_expansive core a), a) = a"
apply (cases a)  
apply (auto simp: core_sum_camera.rep_eq comp_sum_camera.rep_eq camera_core_id split: option.splits)
by (metis camera_core_id option.sel  )+
next
fix a :: "('a,'b) sum_camera"
show "\<exists>a'. Rep_non_expansive core a = Some a' \<Longrightarrow> Rep_non_expansive core (the (Rep_non_expansive core a)) = Rep_non_expansive core a"
apply (cases a) apply (auto simp:  core_sum_camera.rep_eq split: option.splits)
using camera_core_idem by fastforce+
next
fix a b a' c :: "('a,'b) sum_camera"
show "\<lbrakk>Rep_non_expansive core a = Some a'; \<exists>c. b = Rep_non_expansive comp (a, c)\<rbrakk> \<Longrightarrow>
  \<exists>b'. Rep_non_expansive core b = Some b' \<and> (\<exists>c. b' = Rep_non_expansive comp (a', c))"
  apply (cases a; cases b; cases c; cases a')
  apply (auto simp: core_sum_camera.rep_eq comp_sum_camera.rep_eq split: option.splits)
  sorry
next
fix a b :: "('a,'b) sum_camera"
fix n  
show "Rep_sprop (Rep_non_expansive valid_raw (Rep_non_expansive comp (a, b))) n \<Longrightarrow> Rep_sprop (Rep_non_expansive valid_raw a) n"
by (cases a; cases b) 
(auto simp:   comp_sum_camera.rep_eq Abs_sprop_inverse valid_raw_sum_camera.rep_eq intro: camera_valid_op split: option.splits)
next
fix a b1 b2 :: "('a,'b) sum_camera"
fix n
show "Rep_sprop (Rep_non_expansive valid_raw a) n \<Longrightarrow>
  n_equiv n a (Rep_non_expansive comp (b1, b2)) \<Longrightarrow> \<exists>c1 c2. a = Rep_non_expansive comp (c1, c2) \<and> n_equiv n c1 b1 \<and> n_equiv n c2 b2"
  apply (cases a; cases b1; cases b2) 
  apply (auto simp:   comp_sum_camera.rep_eq Abs_sprop_inverse valid_raw_sum_camera.rep_eq intro: camera_extend split: option.splits)
  apply (metis camera_extend n_equiv_sum_camera.simps(1)  sum_comp.simps(1))
  by (metis camera_extend n_equiv_sum_camera.simps(2)  sum_comp.simps(2))
qed
end

lemma sum_update_l: "a\<leadsto>B \<Longrightarrow> (Inl a) \<leadsto> {Inl b |b. b\<in>B}"
apply (auto simp: fup_def valid_def comp_sum_camera.rep_eq valid_raw_sum_camera.rep_eq Abs_sprop_inverse split: sum_camera.splits)
apply (smt (z3)  sum_camera.distinct(1) sum_camera.distinct(3) sum_camera.inject(1) sum_comp.simps(1) sum_comp.simps(6) sum_comp.simps(8) sum_core.cases)
by (smt (verit, best) camera_assoc camera_comm comp_sum_camera.rep_eq sum_camera.distinct(5) sum_comp.simps(2) sum_comp.simps(6) sum_comp.simps(8))

lemma sum_update_r: "a\<leadsto>B \<Longrightarrow> (Inr a) \<leadsto> {Inr b |b. b\<in>B}"
sorry (* Same as above *)

lemma sum_swap_l: "\<lbrakk>\<forall>c n. \<not> valid_n (rep_comp (a,c)) n; valid b\<rbrakk> \<Longrightarrow> (Inl a) \<leadsto> {Inr b}"
apply (auto simp: valid_def fup_def )
apply (auto simp:  comp_sum_camera.rep_eq valid_raw_sum_camera.rep_eq Abs_sprop_inverse split: sum_camera.splits)
apply (smt (z3) camera_assoc camera_comm comp_sum_camera.rep_eq sum_camera.simps(6) sum_comp.simps(1) sum_comp.simps(3))
subgoal for x y z d
proof -
assume assm1:"\<forall>c n. \<not> Rep_sprop (Rep_non_expansive valid_raw (Rep_non_expansive comp (a, c))) n"
assume assms2: "sum_comp (Inl a, x) = sum_camera.Inl z" "All (Rep_sprop (Rep_non_expansive valid_raw z))"
from assm1 have neg: "\<not> Rep_sprop (Rep_non_expansive valid_raw (Rep_non_expansive comp (a, c))) n" for c n
  by blast
from assms2 obtain x' where "x=Inl x'" 
    by (metis sum_camera.distinct(3) sum_comp.simps(6) sum_comp.simps(8) sum_core.cases)
with assms2 have "Rep_non_expansive comp (a,x') = z" 
  by (metis  sum_camera.inject(1) sum_comp.simps(1))
with assms2 have "Rep_sprop (Rep_non_expansive valid_raw (Rep_non_expansive comp (a, x'))) n" for n
  by auto
with neg have False by simp
then show "Rep_sprop (Rep_non_expansive valid_raw d) y" by simp
qed
apply (smt (z3) camera_assoc comp_sum_camera.rep_eq  sum_camera.inject(1) sum_camera.simps(4) sum_comp.simps(1) sum_comp.simps(6) sum_core.cases)
apply (smt (z3) camera_assoc camera_comm comp_sum_camera.rep_eq sum_camera.distinct(5) sum_comp.simps(2) sum_comp.simps(6) sum_comp.simps(8))
apply (smt (z3) camera_assoc camera_comm comp_sum_camera.rep_eq sum_camera.distinct(5) sum_comp.simps(2) sum_comp.simps(6))
by (smt (verit, ccfv_SIG) camera_assoc camera_comm comp_sum_camera.rep_eq sum_camera.simps(8) sum_comp.simps(2) sum_comp.simps(8))

lemma sum_swap_r: "\<lbrakk>\<forall>c n. \<not> Rep_sprop (rep_valid_raw (rep_comp (a,c))) n; valid b\<rbrakk> \<Longrightarrow> (Inr a) \<leadsto> {Inl b}"
sorry (* Same as above *)

fun option_comp :: "(('a::camera) option\<times>'a option) \<Rightarrow> 'a option" where
  "option_comp (Some a, Some b) = Some (rep_comp (a,b))"
| "option_comp (Some a, None) = Some a"
| "option_comp (None, Some a) = Some a"  
| "option_comp _ = None"

text \<open> Option type \<close>
instantiation option :: (camera) camera begin
  lift_definition valid_raw_option :: "('a option, sprop) non_expansive" is
    "\<lambda>x. (case x of Some a \<Rightarrow> rep_valid_raw a | None \<Rightarrow> sTrue)"
    apply (auto simp: ofe_refl  n_equiv_sprop_def n_equiv_option_def split: option.splits)
    using Rep_non_expansive n_equiv_sprop_def by fastforce+
  lift_definition core_option :: "('a option, 'a option option) non_expansive" is
    "\<lambda>x. (case x of Some a \<Rightarrow> Some (rep_core a) | None \<Rightarrow> Some None)"
    apply (auto simp:  n_equiv_option_def split: option.splits)
    apply (metis (no_types, lifting) Rep_non_expansive mem_Collect_eq n_equiv_option_def)
    by (metis (no_types, lifting) Rep_non_expansive mem_Collect_eq n_equiv_option_def)
  lift_definition comp_option :: "('a option \<times> 'a option, 'a option) non_expansive" is
    "option_comp" by (auto simp: n_equiv_option_def )
instance proof 
fix a b c :: "'a option"
show "Rep_non_expansive comp (Rep_non_expansive comp (a, b), c) = Rep_non_expansive comp (a, Rep_non_expansive comp (b, c))"
  by (cases a; cases b; cases c) (auto simp: comp_option.rep_eq  camera_assoc)
next
fix a b :: "'a option"
show "Rep_non_expansive comp (a, b) = Rep_non_expansive comp (b, a)"
  by (cases a; cases b) (auto simp: comp_option.rep_eq  camera_comm)
next
fix a :: "'a option"
show "\<exists>a'. Rep_non_expansive core a = Some a' \<Longrightarrow> Rep_non_expansive comp (the (Rep_non_expansive core a), a) = a"
apply (cases a) 
apply (auto simp: comp_option.rep_eq core_option.rep_eq  )
by (metis camera_core_id option.exhaust_sel option_comp.simps(1) option_comp.simps(3) )
next
fix a :: "'a option"
show "\<exists>a'. Rep_non_expansive core a = Some a' \<Longrightarrow> Rep_non_expansive core (the (Rep_non_expansive core a)) = Rep_non_expansive core a"
apply (cases a) apply (auto simp: core_option.rep_eq  split: option.splits)
using camera_core_idem by fastforce+
next
fix a b a' c :: "'a option"
show "\<lbrakk>Rep_non_expansive core a = Some a'; b=Rep_non_expansive comp (a,c)\<rbrakk> \<Longrightarrow> 
      (\<exists>b'. (Rep_non_expansive core b = Some b') \<and> (b' = Rep_non_expansive comp (a',c)))"
  sorry  
next
fix a b :: "'a option"
fix n
show "Rep_sprop (Rep_non_expansive valid_raw (Rep_non_expansive comp (a, b))) n \<Longrightarrow> Rep_sprop (Rep_non_expansive valid_raw a) n"
by (cases a; cases b)  (auto simp: comp_option.rep_eq  valid_raw_option.rep_eq  intro: camera_valid_op)
next
fix a b1 b2 :: "'a option"
fix n
show "\<lbrakk>Rep_sprop (Rep_non_expansive valid_raw a) n; n_equiv n a (Rep_non_expansive comp (b1, b2))\<rbrakk>
   \<Longrightarrow> \<exists>c1 c2. a = Rep_non_expansive comp (c1, c2) \<and> n_equiv n c1 b1 \<and> n_equiv n c2 b2"
   apply (cases a; cases b1; cases b2) 
   apply  (auto simp: valid_raw_option.rep_eq comp_option.rep_eq)
   using ofe_refl apply force+
   apply (simp_all add: n_equiv_option_def)
   apply force
   apply force
   by (metis camera_extend option_comp.simps(1)  )
qed
end  

instantiation option :: (camera) total_camera begin
definition [simp]: "\<epsilon>_option \<equiv> None"
instance apply (standard) 
apply (auto simp: valid_def valid_raw_option_def comp_option.rep_eq core_option.rep_eq)
apply (metis option.simps(4) sTrue_def sPure.rep_eq valid_raw_option.abs_eq valid_raw_option.rep_eq)
by (metis not_None_eq option_comp.simps(3) option_comp.simps(4))
end

text \<open> Agreement camera functor \<close>
typedef 'a::ofe raw_ag = "{a::'a set | a. finite a \<and> a\<noteq>{} }"
  by auto
setup_lifting type_definition_raw_ag  
lift_definition raw_ag_n_equiv :: "nat \<Rightarrow> ('a::ofe) raw_ag \<Rightarrow> 'a raw_ag \<Rightarrow> bool" is
  "\<lambda>n a b. (\<forall>x\<in>a. \<exists>y\<in>b. n_equiv n x y) \<and> (\<forall>y\<in>b. \<exists>x\<in>a. n_equiv n y x)" .
lift_definition raw_ag_equiv :: "('a::ofe) raw_ag \<Rightarrow> 'a raw_ag \<Rightarrow> bool" is
  "\<lambda>a b. \<forall>n. raw_ag_n_equiv n a b" .

instantiation raw_ag :: (ofe) ofe begin
definition n_equiv_raw_ag where "n_equiv_raw_ag \<equiv> raw_ag_n_equiv"
definition ofe_eq_raw_ag where "ofe_eq_raw_ag \<equiv> raw_ag_equiv"
lemmas defs = raw_ag_n_equiv.rep_eq raw_ag_equiv.rep_eq n_equiv_raw_ag_def ofe_eq_raw_ag_def
instance by (standard) (auto 4 4 simp: defs ofe_sym intro: ofe_refl ofe_trans ofe_mono)
end

quotient_type (overloaded) 'a ag = "('a::ofe) raw_ag" / raw_ag_equiv
by (simp add: raw_ag_equiv.rep_eq raw_ag_n_equiv.rep_eq equivp_reflp_symp_transp reflp_def symp_def transp_def)  
  (meson ofe_refl ofe_sym ofe_trans)
  
instantiation ag :: (ofe) ofe begin
lift_definition n_equiv_ag :: "nat \<Rightarrow> ('a::ofe) ag \<Rightarrow> 'a ag \<Rightarrow> bool" is "raw_ag_n_equiv"   
  by (auto simp: raw_ag_n_equiv.rep_eq raw_ag_equiv.rep_eq) (metis ofe_sym ofe_trans)+
lift_definition ofe_eq_ag :: "'a ag \<Rightarrow> 'a ag \<Rightarrow> bool" is "raw_ag_equiv"
  by (auto simp: raw_ag_equiv.rep_eq raw_ag_n_equiv.rep_eq) (metis ofe_sym ofe_trans)+
instance by (standard; transfer) (auto 4 4 simp: defs ofe_sym intro: ofe_refl ofe_trans ofe_mono)
end

definition ag_rep :: "'a::ofe ag \<Rightarrow> 'a set" where "ag_rep \<equiv> Rep_raw_ag \<circ> rep_ag"

instantiation ag :: (ofe) camera begin
lift_definition valid_raw_ag :: "('a ag, sprop) non_expansive" is
  "\<lambda>a. Abs_sprop (\<lambda>n. \<forall>x y. (x\<in> ag_rep a\<and>y\<in> ag_rep a) \<longrightarrow> n_equiv n x y)"
  by (auto simp: ag_rep_def n_equiv_ag.rep_eq n_equiv_sprop_def raw_ag_n_equiv.rep_eq)
  (smt (verit, ccfv_threshold) Abs_sprop_inverse mem_Collect_eq ofe_mono ofe_sym ofe_trans)+
lift_definition core_ag :: "('a ag, 'a ag option) non_expansive" is "Some"
  by (smt (verit, best) conversep.intros n_equiv_option_def option.ctr_transfer(2) relcomppI)
lift_definition comp_ag :: "('a ag \<times> 'a ag, 'a ag) non_expansive" is 
  "\<lambda>(x,y::'a ag). Abs_raw_ag ((ag_rep x)\<union>(ag_rep y))"
  sorry
instance sorry
end

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

instantiation ex :: (ofe) camera begin
lift_definition valid_raw_ex :: "('a ex, sprop) non_expansive" is
  "\<lambda>x::'a ex. Abs_sprop (\<lambda>n. \<not> n_equiv n x Inv)" 
  using n_equiv_ex.elims(2) n_equiv_sprop_def by fastforce 
lift_definition core_ex :: "('a ex, 'a ex option) non_expansive" is 
  "\<lambda>x. (case x of Ex _ \<Rightarrow> None | Inv \<Rightarrow> Some Inv)" by (auto split: ex.splits intro: ofe_refl)
lift_definition comp_ex :: "('a ex \<times> 'a ex, 'a ex) non_expansive" is "\<lambda>_. Inv" by (rule ofe_refl)
instance apply (standard) apply (auto simp: core_ex.rep_eq comp_ex.rep_eq valid_raw_ex.rep_eq split: ex.splits intro: ofe_refl)
by (metis ex.distinct(1) n_equiv_ex.elims(2))
end

text \<open> Authoritative camera functor \<close>
datatype 'm auth = Auth "('m ex option\<times>'m)"
instantiation auth :: (total_camera) ofe begin
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

instantiation auth :: (total_camera) camera begin
lift_definition valid_raw_auth :: "('a auth, sprop) non_expansive" is
  "\<lambda>a. case a of Auth (x,b) \<Rightarrow> Abs_sprop (\<lambda>n. (x=None\<and>Rep_sprop (rep_valid_raw b) n) \<or> 
    (\<exists>c. x=Some(Ex c) \<and> n_incl n b c \<and> Rep_sprop (rep_valid_raw c) n))"
    sorry
lift_definition core_auth :: "('a auth, 'a auth option) non_expansive" is
  "\<lambda>a. case a of Auth (_,b) \<Rightarrow> Some (Auth (None,total_core b))"
  apply (auto simp: total_core_def  split: auth.splits option.splits intro: ofe_refl)
  apply (metis \<epsilon>_core \<epsilon>_left_id camera_core_mono option.distinct(1)  )
  apply (metis \<epsilon>_core \<epsilon>_left_id camera_core_mono option.distinct(1)  )
  by (smt (verit, best) Rep_non_expansive mem_Collect_eq n_equiv_auth.simps n_equiv_option_def n_equiv_prod.simps option.discI option.inject)
lift_definition comp_auth :: "('a auth \<times> 'a auth, 'a auth) non_expansive" is
  "\<lambda>a. case a of (Auth (x1,b1),Auth (x2,b2)) \<Rightarrow> Auth (rep_comp ((x1,b1),(x2,b2)))"
  by (auto simp:  comp_prod.rep_eq split: auth.splits) 
instance apply (standard)
apply (auto simp: comp_auth.rep_eq  core_auth.rep_eq valid_raw_auth.rep_eq   split: auth.splits)
apply (rule camera_assoc)
apply (rule camera_comm)
apply (auto simp: total_core_def  split: option.splits)
apply (metis \<epsilon>_core \<epsilon>_left_id camera_core_mono option.distinct(1)  )
subgoal for a b b' proof (auto simp: comp_prod.rep_eq)
show "rep_comp (None, a) = a" by (rule \<epsilon>_left_id[of a, simplified \<epsilon>_option_def])
next assume "Rep_non_expansive camera_class.core b = Some b'"
with camera_core_id[of b, simplified  this] show "rep_comp (b', b) = b"
by (metis option.sel ) qed
apply (metis (mono_tags) \<epsilon>_core option.simps(3))+
apply (metis \<epsilon>_core option.inject)
using camera_core_idem apply force+
apply (metis \<epsilon>_core \<epsilon>_left_id camera_core_mono option.distinct(1))
apply (metis \<epsilon>_core \<epsilon>_left_id camera_core_mono option.distinct(1))
apply (metis \<epsilon>_core \<epsilon>_left_id camera_core_mono option.distinct(1))
sorry
end

instantiation auth :: (total_camera) total_camera begin
definition "\<epsilon>_auth \<equiv> Auth (None, \<epsilon>)"
instance proof (standard)
have "valid (\<epsilon>::'a auth) = valid (Auth (None, \<epsilon>::'a))" by (simp add: \<epsilon>_auth_def)
also have "... = (\<forall>n. Rep_sprop (rep_valid_raw (Auth (None, \<epsilon>::'a))) n)" by (simp add: valid_def)
also have "... = (\<forall>n. Rep_sprop (Abs_sprop (\<lambda>n. Rep_sprop (rep_valid_raw  (\<epsilon>::'a)) n)) n)"
  by (auto simp:  valid_raw_auth.rep_eq)
also have "... = (\<forall>n. Rep_sprop (rep_valid_raw (\<epsilon>::'a)) n)" using Rep_sprop_inverse by simp
also have "... = valid (\<epsilon>::'a)" using valid_def  by metis
also have "... = True" using \<epsilon>_valid by simp
finally show "valid (\<epsilon>::'a auth)" by simp
next
fix a :: "'a auth"
have rep_abs_comp: "Rep_non_expansive (Abs_non_expansive (\<lambda>((x, y), a, b). (rep_comp (x, a), rep_comp (y, b)))) 
  = (\<lambda>((x, y), a, b). (rep_comp (x, a), rep_comp (y, b)))"
  by (metis comp_prod.rep_eq comp_prod_def)
show "rep_comp (\<epsilon>,a) = a" 
  apply (auto simp:  comp_auth.rep_eq \<epsilon>_auth_def comp_prod_def rep_abs_comp[simplified ] split: auth.splits)
  using \<epsilon>_left_id[simplified ] \<epsilon>_option_def by metis+
next
show "rep_core (\<epsilon>::'a auth) = Some \<epsilon>" 
  by (auto simp: \<epsilon>_auth_def  core_auth.rep_eq split: auth.splits)
qed
end

abbreviation full :: "'m::total_camera \<Rightarrow> 'm auth" where "full \<equiv> \<lambda>a::'m. Auth (Some (Ex a), \<epsilon>)"
abbreviation fragm :: "'m::total_camera \<Rightarrow> 'm auth" where "fragm \<equiv> \<lambda>a::'m. Auth (None, a)"
abbreviation comb :: "'m::total_camera \<Rightarrow> 'm \<Rightarrow> 'm auth" where "comb \<equiv> \<lambda>(a::'m) b. Auth (Some (Ex a), b)"

text \<open> Map functors, based on a simple wrapper type \<close>

text \<open>
  As maps are only functions to options and thus can't directly be declared as class instances, 
  we need a bit of class magic. Based on ideas from the AFP entry Separation Logic Algebra.
\<close>
class opt = fixes none :: 'a begin definition "domain f \<equiv> {x. f x \<noteq> none}" end
instantiation option :: (type) opt begin definition [simp]: "none \<equiv> None" instance .. end
class opt_ofe = opt + ofe
instance option :: (ofe) opt_ofe ..
class opt_camera = opt_ofe + camera
instance option :: (camera) opt_camera ..
class opt_total_camera = opt_camera + total_camera
instance option :: (camera) opt_total_camera ..

instantiation "fun" :: (type,opt_ofe) ofe begin
definition n_equiv_fun :: "nat \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool" where
  "n_equiv_fun n m1 m2 \<equiv> \<forall>i. n_equiv n (m1 i) (m2 i)"
definition ofe_eq_fun :: "('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool" where
  "ofe_eq_fun m1 m2 \<equiv> \<forall>i. ofe_eq (m1 i) (m2 i)"
instance by (standard, unfold n_equiv_fun_def ofe_eq_fun_def) 
  (auto simp: ofe_sym  ofe_limit intro: ofe_refl ofe_trans ofe_mono ofe_limit ofe_eq_eq)
end

(* No cofe instantiation because I have no idea how the Coq maps work for this one. *)

instantiation "fun" :: (type, opt_camera) camera begin
lift_definition valid_raw_fun :: "(('a\<Rightarrow>'b), sprop) non_expansive" is
  "\<lambda>m. Abs_sprop (\<lambda>n. \<forall>i. valid_n (m i) n)" sorry
lift_definition core_fun :: "(('a\<Rightarrow>'b), ('a\<Rightarrow>'b) option) non_expansive" is
  "\<lambda>m. Some ((\<lambda>b. case rep_core b of Some a \<Rightarrow> a | None \<Rightarrow> none) \<circ> m)" sorry
lift_definition comp_fun :: "(('a\<Rightarrow>'b)\<times>('a\<Rightarrow>'b), ('a\<Rightarrow>'b)) non_expansive" is
  "\<lambda>(m1, m2). (\<lambda>i. rep_comp (m1 i,m2 i))"
  by (auto simp: comp_equiv n_equiv_fun_def split: prod.splits)
instance sorry
end

instantiation "fun" :: (type, opt_total_camera) total_camera begin
definition \<epsilon>_fun :: "'a\<Rightarrow>'b" where [simp]: "\<epsilon>_fun \<equiv> (\<lambda>_. \<epsilon>)"
instance apply (standard) 
apply (auto simp: valid_def valid_raw_fun.rep_eq Abs_sprop_inverse valid_raw_option.rep_eq)
subgoal using Rep_sprop_inverse \<epsilon>_valid valid_def by auto
subgoal by (auto simp: comp_fun.rep_eq \<epsilon>_left_id)
by (auto simp: core_fun.rep_eq \<epsilon>_core split: option.splits)
end

text \<open> Fractions camera/RA \<close>
text \<open> Based on the interval (0,1] together with an invalid element for computations outside of this
    interval. \<close>
typedef frac_raw = "{p::rat. 0<p \<and> p\<le>1}" by force
datatype frac = Frac frac_raw | Inv

(* Addition within the interval. *)
fun frac_add :: "frac \<Rightarrow> frac \<Rightarrow> frac" where
  "frac_add (Frac p) (Frac q) = (let pq = (Rep_frac_raw p + Rep_frac_raw q) in
    (if pq\<le>1 then Frac (Abs_frac_raw pq) else Inv))"
| "frac_add _ _ = Inv"

lemma frac_add_comm: "frac_add a b = frac_add b a" 
  by (cases a; cases b) (auto simp: add.commute)
  
lemma frac_add_assoc: "frac_add (frac_add a b) c = frac_add a (frac_add b c)"
  apply (cases a; cases b; cases c) apply auto 
proof-
fix a' b' c'
assume assms: " a = Frac a'" "b = Frac b'" "c = Frac c'"
show "frac_add (let pq = Rep_frac_raw a' + Rep_frac_raw b' in if pq \<le> 1 then Frac (Abs_frac_raw pq) else frac.Inv) (Frac c') =
       frac_add (Frac a') (let pq = Rep_frac_raw b' + Rep_frac_raw c' in if pq \<le> 1 then Frac (Abs_frac_raw pq) else frac.Inv)"
  apply (cases "Rep_frac_raw a' + Rep_frac_raw b'\<le>1")
  apply (cases "Rep_frac_raw b' + Rep_frac_raw c'\<le>1")
  apply auto
  apply (smt (z3) Abs_frac_raw_inverse Rep_frac_raw group_cancel.add1 le_add_same_cancel1 less_le_trans mem_Collect_eq order_less_imp_le)
  apply (smt (z3) Abs_frac_raw_inverse Rep_frac_raw add_le_same_cancel2 dual_order.trans le_diff_eq linear mem_Collect_eq not_le)     
  by (smt (verit, del_insts) Abs_frac_raw_inverse Rep_frac_raw add_le_same_cancel1 add_mono_thms_linordered_semiring(1) add_nonneg_nonneg diff_add_cancel frac_add.simps(1) frac_add.simps(3) le_diff_eq less_eq_rat_def mem_Collect_eq not_le)
qed  
  
instantiation frac :: ofe begin
lift_definition n_equiv_frac :: "nat \<Rightarrow> frac \<Rightarrow> frac \<Rightarrow> bool" is "\<lambda>_. (=)" .
lift_definition ofe_eq_frac :: "frac \<Rightarrow> frac \<Rightarrow> bool" is "(=)" .
instance by standard (auto simp: n_equiv_frac.rep_eq ofe_eq_frac.rep_eq)
end

instantiation frac :: camera begin
lift_definition valid_raw_frac :: "(frac, sprop) non_expansive" is "\<lambda>p. sPure (p\<noteq>Inv)" 
  by (simp add: n_equiv_frac.abs_eq ofe_refl)
lift_definition core_frac :: "(frac, frac option) non_expansive" is 
  "\<lambda>p. case p of Frac _ \<Rightarrow> None | Inv \<Rightarrow> Some Inv" 
  by (auto simp: n_equiv_frac.rep_eq n_equiv_option_def split: frac.splits)
lift_definition comp_frac :: "(frac \<times> frac, frac) non_expansive" is "\<lambda>(x,y). frac_add x y" 
  by (smt (z3) n_equiv_frac.abs_eq n_equiv_prod.elims(2))
instance 
  apply standard 
  apply (auto simp: valid_raw_frac.rep_eq core_frac.rep_eq comp_frac.rep_eq n_equiv_frac.rep_eq split: frac.splits)
  using frac_add_assoc frac_add_comm by auto
end

text \<open> Set type camera \<close>
instantiation set :: (type) ofe begin
definition n_equiv_set :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "n_equiv_set _ \<equiv> (=)"
definition ofe_eq_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "ofe_eq_set \<equiv> (=)"
instance by (standard) (auto simp: n_equiv_set_def ofe_eq_set_def)
end

instantiation set :: (type) camera begin
lift_definition valid_raw_set :: "('a set, sprop) non_expansive" is "\<lambda>_. sTrue" by (rule ofe_refl)
lift_definition core_set :: "('a set, 'a set option) non_expansive" is "Some"
  by (simp add: n_equiv_set_def ofe_refl)
lift_definition comp_set :: "('a set \<times> 'a set, 'a set) non_expansive" is "\<lambda>(x,y). x \<union> y"
  by (metis (full_types) n_equiv_prod.elims(2) n_equiv_set_def)
instance by (standard) (auto simp: valid_raw_set.rep_eq core_set.rep_eq comp_set.rep_eq n_equiv_set_def)
end

instantiation set :: (type) total_camera begin
definition \<epsilon>_set :: "'a set" where [simp]: "\<epsilon>_set = {}"
instance by (standard) (auto simp: comp_set.rep_eq valid_def valid_raw_set.rep_eq core_set.rep_eq)
end
end