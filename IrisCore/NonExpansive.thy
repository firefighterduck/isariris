theory NonExpansive
imports OFEs
begin
subsection \<open>Non-expansive functions\<close>
subsubsection \<open>Non expansiveness predicate\<close>
text \<open>Non-expansive functions, i.e. equivalence persisting functions from one OFE to another.\<close>
definition non_expansive :: "('a::ofe \<Rightarrow>'b::ofe) \<Rightarrow> bool" where 
  "non_expansive ne \<equiv> \<forall>x y n. n_equiv n x y \<longrightarrow> n_equiv n (ne x) (ne y)"

lemma non_expansiveI[intro?]: "\<lbrakk>\<And>n x y. n_equiv n x y \<Longrightarrow> n_equiv n (f x) (f y)\<rbrakk> \<Longrightarrow> non_expansive f"
  unfolding non_expansive_def by simp
lemma non_expansiveE[elim]: "non_expansive f \<Longrightarrow> 
  (\<And>n x y. \<lbrakk>n_equiv n x y; f x=x'; f y=y'\<rbrakk> \<Longrightarrow> n_equiv n x' y')"
  using non_expansive_def by blast

definition non_expansive2 :: "('a::ofe \<Rightarrow> 'b::ofe \<Rightarrow> 'c::ofe) \<Rightarrow> bool" where
  "non_expansive2 ne \<equiv> \<forall>x y a b n. n_equiv n x y \<longrightarrow> n_equiv n a b \<longrightarrow> n_equiv n (ne x a) (ne y b)"

lemma non_expansive2I[intro?]: "(\<And>x y a b n. n_equiv n x y \<Longrightarrow> n_equiv n a b \<Longrightarrow> 
  n_equiv n (f x a) (f y b)) \<Longrightarrow> non_expansive2 f"
  using non_expansive2_def by blast
lemma non_expansive2E[elim]: "non_expansive2 f \<Longrightarrow> 
  (\<And>n x y a b. \<lbrakk>n_equiv n x y; n_equiv n a b; f x a=x'; f y b=y'\<rbrakk> \<Longrightarrow> n_equiv n x' y')"
  using non_expansive2_def by blast

lemma non_expansive2_ne:"non_expansive2 f \<Longrightarrow> non_expansive (f x)"
  by (auto simp: non_expansive_def non_expansive2_def ofe_eq_limit)

lemma sprop_ne: "non_expansive (Rep_sprop P)"
  unfolding non_expansive_def n_equiv_nat_def n_equiv_bool_def by simp
  
lemma ne_sprop_weaken: 
  "\<lbrakk>n_equiv n x y; m\<le>n; non_expansive P; Rep_sprop (P x) n\<rbrakk> \<Longrightarrow> Rep_sprop (P y) m"
  using Rep_sprop n_equiv_sprop_def non_expansive_def by blast

lemma ne_sprop_weaken2:
  "\<lbrakk>n_equiv n x y; n_equiv n a b; m\<le>n; non_expansive2 P; Rep_sprop (P x a) n\<rbrakk> \<Longrightarrow> Rep_sprop (P y b) m"
  using Rep_sprop n_equiv_sprop_def non_expansive2_def by fast

lemma ne_comp: "\<lbrakk>non_expansive f; non_expansive g\<rbrakk> \<Longrightarrow> non_expansive (f \<circ> g)"
  by (auto simp: non_expansive_def)

lemma discrete_ne: "non_expansive (f::'a::discrete\<Rightarrow>'b::discrete)"
  by (rule non_expansiveI) (simp add: d_equiv)

subsubsection \<open>Non expansive function type\<close>
text \<open>The corresponding subtype of non-expansive functions.\<close>
typedef (overloaded) ('a, 'b) ne = "{f::'a::ofe\<Rightarrow>'b::ofe. non_expansive f}"
  using sprop_ne[of sTrue] apply simp by (metis non_expansiveI ofe_refl)
type_notation ne (infix "-n>" 60)
setup_lifting type_definition_ne
lemmas [simp] = Rep_ne_inverse Rep_ne_inject
lemmas [simp, intro!] = Rep_ne[unfolded mem_Collect_eq]

instantiation ne :: (ofe,ofe) ofe begin
lift_definition n_equiv_ne :: "nat \<Rightarrow> 'a-n>'b \<Rightarrow> 'a-n>'b \<Rightarrow> bool" is
  "\<lambda>n f g. \<forall>x. n_equiv n (f x) (g x)" .
lift_definition ofe_eq_ne :: "'a-n>'b \<Rightarrow> 'a-n>'b \<Rightarrow> bool" is
  "\<lambda>f g. \<forall>x. ofe_eq  (f x) (g x)" .
instance by (standard; transfer) (auto simp: ofe_refl ofe_sym ofe_limit intro: ofe_trans ofe_mono)
end

lift_definition ne_id :: "'a::ofe -n> 'a" is "id" by (rule non_expansiveI) simp
lift_definition ne_const :: "'b::ofe \<Rightarrow> 'a::ofe -n> 'b" is "\<lambda>b _. b" 
  by (rule non_expansiveI) (rule ofe_refl)

lift_definition ne_comp :: "'b::ofe -n> 'c::ofe \<Rightarrow> 'a::ofe -n> 'b \<Rightarrow> 'a-n>'c" is
  "\<lambda>f g. f \<circ> g" by (rule ne_comp)

definition ne_map :: "('a2::ofe-n>'a1::ofe) \<Rightarrow> ('b1::ofe-n>'b2::ofe) \<Rightarrow> ('a1-n>'b1) \<Rightarrow> ('a2-n>'b2)" where
  "ne_map f g h = ne_comp g (ne_comp h f)"

lift_definition ne_map_ne :: "('a2::ofe-n>'a1::ofe) \<Rightarrow> ('b1::ofe-n>'b2::ofe) \<Rightarrow> (('a1-n>'b1)-n>('a2-n>'b2))" is
  "\<lambda>f g. ne_map f g" unfolding ne_map_def ne_comp_def apply simp using ne_comp Rep_ne_inverse
  by (smt (verit) Rep_ne mem_Collect_eq n_equiv_ne.rep_eq ne_comp.rep_eq non_expansive_def o_def)
  
subsection \<open>Contractive functions\<close>
subsubsection \<open>Contractiveness predicate\<close>
definition contractive :: "('a::ofe \<Rightarrow> 'b::ofe) \<Rightarrow> bool" where
  "contractive con \<equiv> \<forall>n x y. (\<forall>m<n. n_equiv m x y) \<longrightarrow> n_equiv n (con x) (con y)"  

definition contractive_alt :: "('a::ofe \<Rightarrow> 'b::ofe) \<Rightarrow> bool" where
  "contractive_alt f \<equiv> \<forall>n x y. (case n of 0 \<Rightarrow> True | Suc n' \<Rightarrow> n_equiv n' x y) \<longrightarrow> n_equiv n (f x) (f y)"

lemma contr_contr_alt: "contractive f \<longleftrightarrow> contractive_alt f"
  apply (simp add: contractive_def contractive_alt_def split: nat.splits)
  by (smt (verit, ccfv_SIG) bot_nat_0.extremum_strict ex_least_nat_less less_Suc_eq_le nat_less_le ofe_down_contr order.refl)

lemma contractiveI: "(\<And>n x y. (\<forall>m<n. n_equiv m x y) \<Longrightarrow> n_equiv n (f x) (f y)) \<Longrightarrow> contractive f"
  by (auto simp: contractive_def)

lemma contractiveE: "contractive f \<Longrightarrow> (\<And>n x y. (\<forall>m<n. n_equiv m x y) \<Longrightarrow> n_equiv n (f x) (f y))"
  by (auto simp: contractive_def)
  
lemma contractive_non_expansive: "contractive f \<Longrightarrow> non_expansive f"
  by (auto simp: less_imp_le_nat intro: non_expansiveI ofe_mono[OF less_imp_le_nat] elim!: contractiveE)

lemma next_contr: "contractive Next"
  apply (rule contractiveI) 
  apply (simp add: n_equiv_later_def)
  using diff_Suc_less by blast

subsubsection \<open>Contractive function type\<close>
text \<open>The corresponding subtype of contractive functions.\<close>
typedef (overloaded) ('a::ofe,'b::ofe) contr = "{f::'a\<Rightarrow>'b. contractive f}"
  using contractiveI ofe_eq_limit by fastforce
setup_lifting type_definition_contr
lemmas [simp] = Rep_contr_inverse Rep_contr_inject
lemmas [simp, intro!] = Rep_contr[unfolded mem_Collect_eq]
end