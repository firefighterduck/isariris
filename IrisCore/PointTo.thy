theory PointTo
imports DerivedConstructions Frac BaseLogicShallow
begin

(* 
  What do we need? - a points-to fact for HeapLang
  What does Iris/Coq provide? - a generic heap with points-to based on ghost maps
  What would we need to port this? - the view, gmap_view, ghost_map, resercation_map, dfrac
    and gen_heap cameras (HeapLang also uses gen_heap_inv)
  Is it possible to simplify this by loosing generality? - I guess so
  
  What does gen_heap do? 
    - standard point-to connective that tracks value at a location
    - meta/ghost data at location
    - meta-token to symbolize that no meta data has been associated with location
    - meta-token can be split for different masks
    - given a token for a mask, one can add meta data for a masked namespace
    - meta data can be associated with multiple ghost names
    - implementation:
    - a gmap_view for the raw locations and values
    - a gmap_view that associates locations with ghost names
    - a reservation_map that holds the actual meta data
    - meta data is encoded as integers (requires class countable)
    - the reservation_map maps a namespace (list of integers) to meta data

  Functions:

  fun points_to :: "loc \<Rightarrow> dfrac \<Rightarrow> val \<Rightarrow> \<Sigma> iProp" where "points_to l dq v = mapsto l dg (Some v)"
  fun mapsto :: "'loc \<Rightarrow> dfrac \<Rightarrow> 'val \<Rightarrow> \<Sigma> iProp" where 
    "mapsto l dq v = ghost_map_elem gen_heap_name l dq v"
  fun ghost_map_elem :: "gname \<Rightarrow> 'key \<Rightarrow> dfrac \<Rightarrow> 'val \<Rightarrow> \<Sigma> iProp" where 
    "ghost_map_elem \<gamma> k dq v = Own_\<gamma>(gmap_view_frag k dq v)" <----------------- This is problematic!
  fun gmap_view_frag :: "'key \<Rightarrow> dfrac \<Rightarrow> 'val \<Rightarrow> ('key,'val) gmap_view" where
    "gmap_view_frag k dq v = view_frag [k\<mapsto>(dq,Abs_ag v)]"
  fun view_frag :: "'b \<Rightarrow> ('a,'b) view" where "view_frag b = View None b"
  
  Types:

  type_synonym ('key, 'val::ofe) gmap_view = 'key\<rightharpoonup>(dfrac\<times>'val ag)
  datatype ('a,'b) view = View (view_auth_proj: "(dfrac\<times>'a ag) option") (view_frag_proj: 'b)

  NOTE: view is a dependent type that has a relation function between 'a and 'b.
  This can be more or less ported to being a type class, I think?

  PROBLEM!!!! 
  The way that meta data is included in the gen_heap can not simply be transferred to Isabelle.
  This is because the heap tracks meta data from arbitrarily many different cameras.
  They are only known by gname, which is then used to decode the saved meta data correctly.
  But there is no simple way of obtaining a type dynamically based on a constant like a gname in Isabelle.
  The exact gname to camera type translation is done by Own_\<gamma> which picks the correct camera for \<gamma>.

  This doesn't seem to be a problem for the spanning tree example, as it doesn't make use of meta
  data but it is a real big issue for a complete port to Isabelle!
*)

subsubsection \<open>View based heap\<close>
text \<open> An own heap camera that is a simplification of the one used in the Coq implementation. \<close>
datatype ('l,'v::ofe) heap = Heap "'l \<rightharpoonup> (dfrac\<times>'v ag)"

instantiation heap :: (type, ofe) ofe begin
fun n_equiv_heap :: "nat \<Rightarrow> ('a, 'b) heap \<Rightarrow> ('a, 'b) heap \<Rightarrow> bool" where
  "n_equiv_heap n (Heap x) (Heap y) = n_equiv n x y"
fun ofe_eq_heap :: "('a, 'b) heap \<Rightarrow> ('a, 'b) heap \<Rightarrow> bool" where
  "ofe_eq_heap (Heap x) (Heap y) = ofe_eq x y"
instance proof
  show "\<And>n (x::('a, 'b) heap). n_equiv n x x" by (cases rule: heap.induct) (auto simp: ofe_refl)
next
  fix x y :: "('a, 'b) heap" fix n
  show "n_equiv n x y = n_equiv n y x" by (cases x; cases y) (auto simp: ofe_sym)
next
  fix x y z :: "('a, 'b) heap" fix n
  show "n_equiv n x y \<Longrightarrow> n_equiv n y z \<Longrightarrow> n_equiv n x z"
    by (cases x; cases y; cases z) (auto intro: ofe_trans)
next
  fix x y :: "('a, 'b) heap" fix n m
  show "m \<le> n \<Longrightarrow> n_equiv n x y \<Longrightarrow> n_equiv m x y" by (cases x; cases y) (auto simp: ofe_mono)
next
  fix x y :: "('a, 'b) heap"
  show "ofe_eq x y = (\<forall>n. n_equiv n x y)" by (cases x; cases y) (auto simp: ofe_limit)
next
  fix x y :: "('a, 'b) heap"
  show "x = y \<Longrightarrow> ofe_eq x y" by (cases x; cases y) (auto simp: ofe_eq_eq)
qed
end
instance heap :: (type, discrete) discrete
proof
  fix a b :: "('a, 'b) heap" fix n
  show "n_equiv n a b = (a = b)" by (cases a; cases b) (auto simp: d_equiv)
next
  fix a b :: "('a, 'b) heap"
  show "ofe_eq a b = (a = b)" by (cases a; cases b) (auto simp: d_eq)
qed

abbreviation "heap_rel \<equiv> \<lambda>m n.
  \<forall>l a b. Some(a,b) = (m::'l \<rightharpoonup> (dfrac\<times>'v::ofe ag)) l \<longrightarrow> (valid a \<and> (\<exists>ag. n_equiv n b (to_ag ag)))"

lemma heap_valid: "heap_rel m n \<Longrightarrow> n_valid m n"
  apply (auto simp: valid_raw_fun.rep_eq valid_raw_option_def valid_raw_prod_def sprop_conj.rep_eq split: option.splits)
  apply (metis valid_dfrac)
  by (metis n_valid_ne ofe_sym to_ag.rep_eq valid_raw_ag.rep_eq)

lemma heap_rel_mono: "\<lbrakk>heap_rel m1 n; n_incl m m2 m1; m\<le>n\<rbrakk> \<Longrightarrow> heap_rel m2 m"
proof (auto simp: n_incl_def)
  fix a b c l
  assume assms: "heap_rel m1 n" "m\<le>n" "n_equiv m m1 (m2\<cdot>c)" "Some (a,b) = m2 l" 
  then have "\<forall>i. n_equiv m (m1 i) ((m2 i) \<cdot> (c i))" by (simp add: n_equiv_fun_def op_fun_def)
  with assms(4) have equiv: "n_equiv m (m1 l) ((Some (a,b)) \<cdot> (c l))" by simp
  moreover obtain a2 b2 where ab2: "Some (a2,b2) = (Some (a,b)) \<cdot> (c l)" by (auto simp: op_option_def)
    (metis option_op.elims surj_pair)
  ultimately obtain a1 b1 where ab1: "Some (a1,b1) = m1 l" by (auto simp: n_equiv_option_def)
  from ab1 assms(1) have "valid a1" by simp
  from equiv ab1 ab2 have "n_equiv m a1 a2" by (auto simp: n_equiv_option_def)
  with \<open>valid a1\<close> have "valid a2" by simp
  show "valid a" proof (cases "c l")
    case None
    with ab2 have "a2 = a" by (simp add: op_option_def)
    with \<open>valid a2\<close> show ?thesis by simp
  next
    case (Some cl)
    then obtain ac bc where abc: "cl = (ac,bc)" by fastforce
    with Some ab2 have "a2 = a \<cdot> ac" by (simp add: op_option_def op_prod_def)
    with \<open>valid a2\<close> show ?thesis using camera_valid_op valid_dfrac by blast
  qed
next
  fix a b c l
  assume assms: "heap_rel m1 n" "m\<le>n" "n_equiv m m1 (m2\<cdot>c)" "Some (a,b) = m2 l" 
  then have "\<forall>i. n_equiv m (m1 i) ((m2 i) \<cdot> (c i))" by (simp add: n_equiv_fun_def op_fun_def)
  with assms(4) have equiv: "n_equiv m (m1 l) ((Some (a,b)) \<cdot> (c l))" by simp
  moreover obtain a2 b2 where ab2: "Some (a2,b2) = (Some (a,b)) \<cdot> (c l)" by (auto simp: op_option_def)
    (metis option_op.elims surj_pair)
  ultimately obtain a1 b1 where ab1: "Some (a1,b1) = m1 l" by (auto simp: n_equiv_option_def)
  from assms(1) ab1 obtain ag1 where ag1: "n_equiv m b1 (to_ag ag1)" using assms(2) ofe_mono by blast
  from equiv ab1 ab2 have "n_equiv m b1 b2" by (auto simp: n_equiv_option_def)
  with ag1 have ag2:"n_equiv m b2 (to_ag ag1)" using ofe_trans ofe_sym by blast
  show "\<exists>ag. n_equiv m b (to_ag ag)" proof (cases "c l")
    case None
    with ab2 have "b2=b" by (simp add: op_option_def)
    with ag2 show ?thesis by auto
  next
    case (Some cl)
    then obtain ac bc where abc: "cl = (ac,bc)" by fastforce
    with Some ab2 have "b2 = b \<cdot> bc" by (simp add: op_option_def op_prod_def)
    with ag2 have ag_equiv: "n_equiv m (to_ag ag1) (b\<cdot>bc)" by (simp add: ofe_sym)
    from to_ag_valid have "n_valid (to_ag ag1) m" by (auto simp: valid_def)
    from camera_extend[OF this ag_equiv] obtain c1 c2 where cag:
      "to_ag ag1 = c1 \<cdot> c2 \<and> n_equiv m c1 b \<and> n_equiv m c2 bc" by auto
    with to_ag_op have "c1 = to_ag ag1" "c2 = to_ag ag1" by blast+
    with cag show ?thesis by (auto simp: ofe_sym)
  qed
qed
  
instantiation heap :: (type, ofe) camera begin
lift_definition valid_raw_heap :: "('a, 'b) heap \<Rightarrow> sprop" is
  "\<lambda>x n. case x of Heap m \<Rightarrow> heap_rel m n"
  apply (auto split: heap.splits) using ofe_refl ofe_mono by blast
definition pcore_heap :: "('a, 'b) heap \<Rightarrow> ('a, 'b) heap option" where
  "pcore_heap x = (case x of Heap x \<Rightarrow> Some (Heap (core x)))"
fun op_heap :: "('a, 'b) heap \<Rightarrow> ('a, 'b) heap \<Rightarrow> ('a, 'b) heap" where
  "op_heap (Heap x) (Heap y) = Heap (x \<cdot> y)"
instance proof
show "non_expansive (valid_raw::('a, 'b) heap \<Rightarrow> sprop)" proof (rule non_expansiveI)
  fix x y :: "('a,'b) heap" fix n
  assume assm: "n_equiv n x y"
  then obtain xm ym where m: "x=Heap xm" "y=Heap ym" by (rule n_equiv_heap.elims) simp
  with assm have "n_equiv n xm ym" by simp
  then have l_equiv: "\<forall>l. n_equiv n (xm l) (ym l)" by (auto simp: n_equiv_fun_def)
  then have xy_val: "\<forall>a b. Some (a, b) = xm l \<longrightarrow> valid a \<Longrightarrow> \<forall>c d. Some (c, d) = ym l \<longrightarrow> valid c" for l
    by (smt (verit, ccfv_SIG) Pair_inject n_equiv_option_def n_equiv_prod.elims(2) n_valid_ne option.sel valid_dfrac)
  have xy_ag: "m\<le>n \<Longrightarrow> \<forall>l a b. Some (a, b) = xm l \<longrightarrow> valid a \<and> (\<exists>ag. n_equiv m b (to_ag ag)) 
    \<Longrightarrow> Some (c, d) = ym l \<longrightarrow> (\<exists>ag. n_equiv m d (to_ag ag))" for l c d m
    by (smt (verit, ccfv_threshold) l_equiv n_equiv_option_def n_equiv_prod.elims(2) ofe_mono ofe_sym ofe_trans old.prod.inject option.inject)
  from l_equiv have yx_val: "\<forall>a b. Some (a, b) = ym l \<longrightarrow> valid a \<Longrightarrow> \<forall>c d. Some (c, d) = xm l \<longrightarrow> valid c" for l
    by (smt (verit, ccfv_SIG) Pair_inject d_equiv n_equiv_option_def n_equiv_prod.elims(2) option.inject)
  have yx_ag: "m\<le>n \<Longrightarrow> \<forall>a b. Some (a, b) = ym l \<longrightarrow> (\<exists>ag. n_equiv m b (to_ag ag)) 
    \<Longrightarrow> Some (c, d) = xm l \<longrightarrow> (\<exists>ag. n_equiv m d (to_ag ag))" for c d l m
    by (smt (verit, ccfv_SIG) Pair_inject l_equiv n_equiv_option_def n_equiv_prod.elims(2) ofe_mono ofe_trans option.sel)
  show "n_equiv n (valid_raw x) (valid_raw y)"
    apply (auto simp: valid_raw_heap.rep_eq n_equiv_sprop_def split: heap.splits)
    using m xy_val xy_ag yx_val yx_ag apply blast+
    using m yx_ag by blast
  qed
next    
show "non_expansive (pcore::('a, 'b) heap \<Rightarrow> ('a, 'b) heap option)" by (rule non_expansiveI)
  (auto simp: pcore_heap_def n_equiv_option_def core_ne[unfolded non_expansive_def] split: heap.splits)
next
show " non_expansive2 (op::('a, 'b) heap \<Rightarrow> ('a, 'b) heap \<Rightarrow> ('a, 'b) heap)" by (rule non_expansive2I)
  (smt (verit, best) heap.inject n_equiv_heap.elims(2) n_equiv_heap.elims(3) op_heap.simps op_ne)
next
fix a b c :: "('a, 'b) heap"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (cases a; cases b; cases c) (auto simp: camera_assoc)
next
fix a b :: "('a, 'b) heap"
show "a \<cdot> b = b \<cdot> a" by (cases a; cases b) (auto simp: camera_comm)
next
fix a a' :: "('a, 'b) heap"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" by (cases a; cases a') 
  (auto simp: pcore_heap_def camera_core_id)
next
fix a a' :: "('a, 'b) heap"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a" 
  by (cases a; cases a') (auto simp: pcore_heap_def camera_core_idem)
next
fix a a' b :: "('a, 'b) heap"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  apply (cases a; cases a'; cases b) apply (auto simp: pcore_heap_def)
  using camera_core_mono[unfolded incl_def] heap.inject
  by (metis (no_types, opaque_lifting) PointTo.op_heap.elims PointTo.op_heap.simps)
next
fix a b :: "('a, 'b) heap" fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  proof (cases a; cases b; simp add: valid_raw_heap.rep_eq)
  fix x y
  assume assms: "heap_rel (x\<cdot>y) n" "a=Heap x" "b=Heap y"
  from heap_rel_mono[OF assms(1), of n x] show "heap_rel x n"  by (simp add: n_incl_op_extend)
  qed
next
fix a b c :: "('a, 'b) heap" fix n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b \<cdot> c)
  \<Longrightarrow> \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c"
  proof (cases a; cases b; cases c ; auto simp: valid_raw_heap.rep_eq)
  fix x y z
  assume assms: "\<forall>l a b. Some (a, b) = x l \<longrightarrow>camera_class.valid a \<and> (\<exists>ag. n_equiv n b (to_ag ag))" 
  "n_equiv n x (y \<cdot> z)" "a = Heap x" "b = Heap y" "c = Heap z"
  from heap_valid[OF assms(1)] have "n_valid x n" .
  from camera_extend[OF this assms(2)] have "\<exists>c1 c2. x = c1 \<cdot> c2 \<and> n_equiv n c1 y \<and> n_equiv n c2 z" .
  then show "\<exists>c1 c2. Heap x = c1 \<cdot> c2 \<and> n_equiv n c1 (Heap y) \<and> n_equiv n c2 (Heap z)"
    by (metis n_equiv_heap.simps op_heap.simps)
  qed
qed
end

instance heap :: (type, discrete) dcamera by standard 
  (auto simp: valid_raw_heap.rep_eq valid_def d_equiv split: heap.splits)

instantiation heap :: (type, ofe) ucamera begin
  definition \<epsilon>_heap :: "('a, 'b) heap" where "\<epsilon>_heap \<equiv> Heap \<epsilon>"
instance proof 
  fix a :: "('a,'b) heap" 
  have "Map.empty = \<epsilon>" by simp
  with \<epsilon>_left_id have "Map.empty \<cdot> (x::('a \<rightharpoonup> (dfrac\<times>'b option ag))) = x" for x by (smt (verit))
  then show "\<epsilon>\<cdot>a = a" by (cases a; auto simp: \<epsilon>_heap_def) (metis \<epsilon>_left_id \<open>Map.empty = \<epsilon>\<close>)
next
  have "Map.empty = \<epsilon>" by simp  
  show "pcore \<epsilon> = Some (\<epsilon>::('a,'b) heap)" by (auto simp: pcore_heap_def \<epsilon>_heap_def)
    (metis \<epsilon>_core \<open>Map.empty = \<epsilon>\<close>)
qed (auto simp: \<epsilon>_heap_def valid_raw_heap.rep_eq valid_def split: heap.splits)
end

instance heap :: (type, discrete) ducamera ..

text \<open>The modular heap camera\<close>
type_synonym ('l,'v,'c) heapCmra = "('l,'v) heap\<times>'c"
abbreviation own_heap :: "('l,'v::ofe) heap \<Rightarrow> ('l,'v,'c::ucamera) heapCmra iprop" ("Own\<^sub>h _") where
   "own_heap \<equiv> \<lambda>h. Own(h,\<epsilon>)"

definition points_to :: "'l \<Rightarrow> dfrac \<Rightarrow> 'v::ofe \<Rightarrow> ('l,'v option,'c::ucamera) heapCmra iprop" where
  "points_to l dq v = Own\<^sub>h(Heap [l\<mapsto>(dq, to_ag (Some v))])"
abbreviation points_to_disc :: "'l \<Rightarrow> 'v::ofe \<Rightarrow> ('l,'v option,'c::ucamera) heapCmra iprop" where 
  "points_to_disc \<equiv> \<lambda>l v. points_to l DfracDiscarded v"
abbreviation points_to_own :: "'l \<Rightarrow> frac \<Rightarrow> 'v::ofe \<Rightarrow> ('l,'v option,'c::ucamera) heapCmra iprop" where
  "points_to_own \<equiv> \<lambda>l p v. points_to l (DfracOwn p) v"
abbreviation points_to_full :: "'l \<Rightarrow> 'v::ofe \<Rightarrow> ('l,'v option,'c::ucamera) heapCmra iprop" where
  "points_to_full \<equiv> \<lambda>l v. points_to_own l 1 v"

bundle points_to_syntax begin
  notation points_to ("_ \<mapsto>{_} _" 60)
  notation points_to_disc (infix "\<mapsto>\<box>" 60)
  notation points_to_own ("_\<mapsto>{#_}_" 60)
  notation points_to_full (infix "\<mapsto>\<^sub>u" 60)
end

context includes points_to_syntax assumes "SORT_CONSTRAINT('c::ucamera)" begin
lemma frag_heap_valid: "valid (Heap [k\<mapsto>(dq,to_ag v)]) \<longleftrightarrow> valid dq"
  apply (auto simp: valid_def valid_raw_heap.rep_eq) using ofe_refl by blast
  
lemma points_to_valid: "upred_holds (((l \<mapsto>{dq} v)::('a,'v::discrete option,'c) heapCmra iprop) -\<^emph> \<upharpoonleft>(valid dq))"
proof -
  have "((l \<mapsto>{dq} v)::('a,'v option,'c) heapCmra iprop) 
    \<turnstile> \<V>(Heap [l\<mapsto>(dq,to_ag (Some v))],\<epsilon>::'c)" by (auto simp: points_to_def own_valid)
  moreover have "\<V>(Heap [l\<mapsto>(dq,to_ag (Some v))],\<epsilon>::'c)\<turnstile>\<V>(Heap [l\<mapsto>(dq,to_ag (Some v))])"
    by (auto simp: upred_valid_def valid_def valid_raw_prod_def sprop_conj.rep_eq \<epsilon>_n_valid)
  moreover have "\<V>(Heap [l\<mapsto>(dq,to_ag (Some v))]) \<turnstile> \<upharpoonleft>(valid(Heap [l\<mapsto>(dq,to_ag (Some v))]))"
    using discrete_valid[of "Heap [l\<mapsto>(dq,to_ag (Some v))]"] upred_entail_eq_def 
    by (auto simp: valid_raw_prod_def \<epsilon>_n_valid valid_def)
  ultimately have "((l \<mapsto>{dq} v)::('a,'v option,'c) heapCmra iprop) \<turnstile> \<upharpoonleft>(valid dq)" 
    by (auto simp: frag_heap_valid intro: upred_entails_trans)
  from upred_wand_holdsI [OF this] show ?thesis .
qed

lemma heap_op: "[l\<mapsto>(dq1, to_ag v1)]\<cdot>[l\<mapsto>(dq2, to_ag v2)] = [l\<mapsto>(dq1, to_ag v1)\<cdot>(dq2, to_ag v2)]"
  by (auto simp: op_fun_def op_option_def)

lemma heap_op_val_eq: "[l\<mapsto>(dq1, to_ag v)]\<cdot>[l\<mapsto>(dq2, to_ag v)] = [l\<mapsto>(dq1\<cdot>dq2, to_ag v)]" 
  unfolding heap_op by (auto simp: op_prod_def op_ag_def to_ag_def Rep_ag_inverse)

lemma heap_valid_op: "valid (Heap [l1\<mapsto>(dq1,v1)] \<cdot> Heap [l2\<mapsto>(dq2,v2)]) \<longleftrightarrow>
  (l1\<noteq>l2 \<and> valid (Heap [l1\<mapsto>(dq1,v1)]) \<and> valid (Heap [l2\<mapsto>(dq2,v2)])) \<or>
  (l1=l2 \<and> (\<forall>n. heap_rel ([l1\<mapsto>(dq1,v1)\<cdot>(dq2,v2)]) n))"
  by (auto simp: heap_op valid_raw_heap.rep_eq valid_def op_fun_def op_option_def)
  
lemma points_to_agree: "upred_holds ((l \<mapsto>{dq1} (v1::'v::discrete)) -\<^emph> 
  ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> \<upharpoonleft>(v1 = v2))"
proof -
  have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> 
    \<V>((Heap [l\<mapsto>(dq1, to_ag (Some v1))],\<epsilon>::'c)\<cdot>(Heap [l\<mapsto>(dq2, to_ag (Some v2))],\<epsilon>)))"
    apply (auto simp: points_to_def) using own_valid2 by blast
  then have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> 
    \<V>((Heap ([l\<mapsto>(dq1, to_ag (Some v1))\<cdot>(dq2, to_ag (Some v2))]),\<epsilon>::'c)))"
    by (auto simp: heap_op \<epsilon>_left_id op_prod_def)
  then have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> 
    \<V>(Heap ([l\<mapsto>(dq1, to_ag (Some v1))\<cdot>(dq2, to_ag (Some v2))])))"
    by (auto simp: upred_valid_def valid_def valid_raw_prod_def \<epsilon>_n_valid sprop_conj.rep_eq)
  from upred_entails_wand_holdsR2[OF upred_entail_eqL[OF discrete_valid] this]
  have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph>
    \<upharpoonleft>(All (heap_rel [l\<mapsto>(dq1\<cdot>dq2, to_ag (Some v1)\<cdot>to_ag (Some v2))])))" 
    by (auto simp: valid_raw_heap.rep_eq valid_def op_prod_def)
  then have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph>
    \<upharpoonleft>(valid (dq1\<cdot>dq2) \<and> (\<forall>n. \<exists>ag. n_equiv n (to_ag (Some v1)\<cdot>to_ag (Some v2)) (to_ag ag))))"
    by (smt (verit, ccfv_threshold) camera_comm camera_valid_op dcamera_valid_iff fun_upd_same 
      points_to_valid upred_entails_wand_holdsR upred_holds_entails)
  then have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph>
    \<upharpoonleft>(\<forall>n. \<exists>ag. n_equiv n (to_ag (Some v1)\<cdot>to_ag (Some v2)) (to_ag ag)))"
    using upred_entails_wand_holdsR2 pure_entailsI by (metis (no_types, lifting))
  then have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph>
    \<upharpoonleft>(\<exists>ag. to_ag (Some v1)\<cdot>to_ag (Some v2) = to_ag ag))" using d_equiv by (smt (verit, ccfv_SIG))
  then show ?thesis 
    by (smt (z3) option.inject pure_entailsI singleton_inject to_ag.rep_eq to_ag_op upred_entails_wand_holdsR2)
qed

lemma points_to_combine_same:"((l \<mapsto>{dq1} v)::('a,'v::discrete option,'c) heapCmra iprop) \<^emph> (l \<mapsto>{dq2} v) \<turnstile> (l \<mapsto>{dq1 \<cdot> dq2} v)"
  apply (unfold points_to_def)
  apply (unfold heap_op_val_eq[symmetric])
  by (rule upred_entail_eqR[OF own_op, of "(Heap [l \<mapsto> (dq1, to_ag (Some v))],\<epsilon>::'c)" 
    "(Heap [l \<mapsto> (dq2, to_ag (Some v))],\<epsilon>)", unfolded op_prod_def, simplified, unfolded \<epsilon>_left_id])

lemma points_to_combine: "upred_holds ((l\<mapsto>{dq1} (v1::'v::discrete)) -\<^emph> 
  ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> (l\<mapsto>{dq1\<cdot>dq2} v1) \<^emph> \<upharpoonleft>(v1=v2))"
  apply (rule upred_wand_holds2I)
  apply (rule upred_sep_pure)
  apply (rule entails_pure_extend[OF upred_wandE[OF upred_wand_holdsE[OF points_to_agree]]])
  apply (unfold points_to_def)[1]
  apply (metis points_to_def points_to_combine_same)
  by (rule upred_wandE[OF upred_wand_holdsE[OF points_to_agree]])

lemma points_to_frac_ne: 
  assumes "\<not> (valid (dq1\<cdot>dq2))"
  shows "upred_holds ((l1 \<mapsto>{dq1} (v1::'v::discrete)) -\<^emph> 
    ((l2 \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> \<upharpoonleft>(l1\<noteq>l2))"
proof -
  have valid_drop : 
    "valid ((Heap [l1\<mapsto>(dq1,to_ag (Some v1))],\<epsilon>::'c) \<cdot> (Heap [l2\<mapsto>(dq2,to_ag (Some v2))],\<epsilon>::'c)) =
      valid ((Heap [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (Heap [l2\<mapsto>(dq2,to_ag (Some v2))]))"
    by (auto simp: camera_valid_op prod_valid_def op_prod_def \<epsilon>_left_id \<epsilon>_valid)
  have "\<V>(((Heap [l1\<mapsto>(dq1,to_ag (Some v1))],\<epsilon>::'c) \<cdot> (Heap [l2\<mapsto>(dq2,to_ag (Some v2))],\<epsilon>::'c))) \<turnstile>
    \<upharpoonleft>(valid ((Heap [l1\<mapsto>(dq1,to_ag (Some v1))],\<epsilon>::'c) \<cdot> (Heap [l2\<mapsto>(dq2,to_ag (Some v2))],\<epsilon>::'c)))"
    apply (auto simp: op_prod_def)
    apply (auto simp: prod_valid_def \<epsilon>_left_id \<epsilon>_valid upred_valid_def)
    apply (auto simp: valid_raw_prod_def sprop_conj.rep_eq \<epsilon>_n_valid)
    by (rule upred_entail_eqL[OF discrete_valid[unfolded upred_valid_def], simplified])    
  then have base: "upred_holds ((l1 \<mapsto>{dq1} v1) -\<^emph> 
    ((l2 \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> 
    \<upharpoonleft>(valid ((Heap [l1\<mapsto>(dq1,to_ag (Some v1))],\<epsilon>::'c) \<cdot> (Heap [l2\<mapsto>(dq2,to_ag (Some v2))],\<epsilon>::'c))))"
    using upred_wand_holds2I[OF upred_entails_trans[OF upred_wand_holds2E[OF own_valid2]]]
    by (smt (verit, del_insts) points_to_def)
  from assms have "\<not> (\<forall>n. heap_rel ([l1\<mapsto>(dq1,to_ag (Some v1))\<cdot>(dq2,to_ag (Some v2))]) n)"
    by (auto simp: op_fun_def valid_def op_prod_def)
  with heap_valid_op have "valid ((Heap [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (Heap [l2\<mapsto>(dq2,to_ag (Some v2))])) =
    (l1\<noteq>l2 \<and> valid (Heap [l1\<mapsto>(dq1,to_ag (Some v1))]) \<and> valid (Heap [l2\<mapsto>(dq2,to_ag (Some v2))]))"
    by metis
  then have "\<upharpoonleft>(valid ((Heap [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (Heap [l2\<mapsto>(dq2,to_ag (Some v2))]))) \<turnstile>
    \<upharpoonleft>(l1\<noteq>l2)" using pure_entailsI by blast
  with valid_drop have 
    "\<upharpoonleft>(valid ((Heap [l1\<mapsto>(dq1,to_ag (Some v1))],\<epsilon>::'c) \<cdot> (Heap [l2\<mapsto>(dq2,to_ag (Some v2))],\<epsilon>::'c))) \<turnstile>
    \<upharpoonleft>(l1\<noteq>l2)" by simp
    from upred_entails_wand_holdsR2[OF this base] show ?thesis .
qed

lemma points_to_ne: "upred_holds ((l1\<mapsto>\<^sub>u(v1::'v::discrete)) -\<^emph> 
  ((l2 \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> \<upharpoonleft>(l1\<noteq>l2))"
  by (rule points_to_frac_ne[OF dfrac_not_valid_own])
end
end