theory RecordCameras
imports Graph
  "../IrisCore/Frac"
  "../HeapLang/HeapLang"
  "../HeapLang/PrimitiveLaws"
  "../IrisCore/BaseLogicShallow"
begin

(* Children locations, in Coq it's a leibniz0 structure*)
type_synonym chl = "loc option\<times>loc option"

(* The graph camera, a unital camera. *)
type_synonym graphUR = "((loc\<rightharpoonup>(chl ex))\<times>frac) option"

(* A camera for duplicatable markings *)
type_synonym markingUR = "loc set"


record graphG =
  graph :: "graphUR auth"
  markings :: "markingUR auth"

instantiation graphG_ext :: (ofe) ofe begin
definition n_equiv_graphG_ext :: "nat \<Rightarrow> 'a graphG_scheme \<Rightarrow> 'a graphG_scheme \<Rightarrow> bool" where
  "n_equiv_graphG_ext n x y \<equiv> n_equiv n (graph x) (graph y) \<and> n_equiv n (markings x) (markings y)
    \<and> n_equiv n (graphG.more x) (graphG.more y)"
definition ofe_eq_graphG_ext :: "'a graphG_scheme \<Rightarrow> 'a graphG_scheme \<Rightarrow> bool" where
  "ofe_eq_graphG_ext x y \<equiv> ofe_eq (graph x) (graph y) \<and> ofe_eq (markings x) (markings y) 
    \<and> ofe_eq (graphG.more x) (graphG.more y)"
instance by standard 
(auto simp: n_equiv_graphG_ext_def ofe_eq_graphG_ext_def ofe_refl ofe_sym ofe_limit intro: ofe_trans ofe_mono)
end

instance graphG_ext :: (discrete) discrete 
  by standard (auto simp: n_equiv_graphG_ext_def ofe_eq_graphG_ext_def ofe_refl d_equiv d_eq)

instantiation graphG_ext :: (camera) camera begin
lift_definition valid_raw_graphG_ext :: "'a graphG_scheme \<Rightarrow> sprop" is
  "\<lambda>g n. n_valid (graph g) n \<and> n_valid (markings g) n \<and> n_valid (more g) n" by simp
definition pcore_graphG_ext :: "'a graphG_scheme \<Rightarrow> 'a graphG_scheme option" where
  "pcore_graphG_ext x = (case pcore (graph x) of Some g \<Rightarrow> 
    (case pcore (markings x) of Some m \<Rightarrow> (case pcore (more x) of Some y \<Rightarrow> 
      Some \<lparr>graph=g,markings=m,\<dots>=y\<rparr> | None \<Rightarrow> None) | None \<Rightarrow> None) | None \<Rightarrow> None)"
definition op_graphG_ext :: "'a graphG_scheme \<Rightarrow> 'a graphG_scheme \<Rightarrow> 'a graphG_scheme" where
  "op_graphG_ext x y = \<lparr>graph=(graph x)\<cdot>(graph y),markings=(markings x)\<cdot>(markings y),\<dots>=(more x)\<cdot>(more y)\<rparr>"
instance proof
show "non_expansive (valid_raw::'a graphG_scheme \<Rightarrow> sprop)"
  apply (rule non_expansiveI)
  apply (auto simp: valid_raw_graphG_ext.rep_eq n_equiv_graphG_ext_def n_equiv_sprop_def d_equiv)
  using n_valid_ne ofe_mono ofe_sym  by blast+
next
show "non_expansive (pcore::'a graphG_scheme \<Rightarrow> 'a graphG_scheme option)"
  by (rule non_expansiveI; auto simp: n_equiv_graphG_ext_def pcore_graphG_ext_def ofe_refl 
    n_equiv_option_def d_equiv split: option.splits)
  (metis n_equiv_option_def option.discI option.inject pcore_ne)+
next 
show "non_expansive2 (op::'a graphG_scheme \<Rightarrow> 'a graphG_scheme \<Rightarrow> 'a graphG_scheme)"
  by (rule non_expansive2I) (auto simp: n_equiv_graphG_ext_def op_graphG_ext_def)
next
fix a b c :: "'a graphG_ext"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (auto simp: op_graphG_ext_def camera_assoc)
next
fix a b :: "'a graphG_ext"
show "a \<cdot> b = b \<cdot> a" by (auto simp: op_graphG_ext_def camera_comm)
next
fix a a' :: "'a graphG_ext"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" 
  by (auto simp: op_graphG_ext_def pcore_graphG_ext_def camera_pcore_id split: option.splits)
next
fix a a' :: "'a graphG_ext"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a" 
  by (auto simp: pcore_graphG_ext_def camera_pcore_idem split: option.splits)
next
fix a a' b :: "'a graphG_ext"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  apply (auto simp: pcore_graphG_ext_def op_graphG_ext_def camera_pcore_mono total_pcore split: option.splits)
  apply (metis option.distinct(1) total_pcore)
  apply (metis camera_pcore_mono option.distinct(1))
  by (metis (no_types, opaque_lifting) camera_pcore_mono option.inject select_convs(1) select_convs(2) select_convs(3))
next
fix a b :: "'a graphG_ext" fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  by (auto simp: valid_raw_graphG_ext.rep_eq op_graphG_ext_def camera_valid_op)
next
fix a b c :: "'a graphG_ext" fix n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b \<cdot> c) \<Longrightarrow> 
  \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c"
  by (auto simp: valid_raw_graphG_ext.rep_eq op_graphG_ext_def n_equiv_graphG_ext_def)
  (metis select_convs(1) select_convs(2) select_convs(3) surjective  camera_extend)
qed
end

instance graphG_ext :: (dcamera) dcamera 
  apply (standard; auto simp: valid_def valid_raw_graphG_ext.rep_eq)
  using dcamera_valid_iff by blast+

instantiation graphG_ext :: (ucamera) ucamera begin
definition \<epsilon>_graphG_ext :: "'a graphG_scheme" where [simp]: "\<epsilon>_graphG_ext \<equiv> \<lparr>graph=\<epsilon>,markings=\<epsilon>,\<dots>=\<epsilon>\<rparr>"
instance apply standard 
  apply (auto simp: valid_raw_graphG_ext.rep_eq valid_def \<epsilon>_valid[unfolded valid_def])
  apply (auto simp: op_graphG_ext_def \<epsilon>_left_id)
  by (auto simp: pcore_graphG_ext_def \<epsilon>_pcore)
end

instance graphG_ext :: (ducamera) ducamera ..

record heapG = graphG +
  heap :: heapGS  
setup_lifting type_definition_heapG_ext
  
lemma heapG_ext_abs: "(\<lparr>heap=h,\<dots>=m\<rparr>::'a heapG_ext) = Abs_heapG_ext (h,m)"
  unfolding heapG_ext_def Record.iso_tuple_cons_def heapG_ext_Tuple_Iso_def Record.abst_def
  by simp

instantiation heapG_ext :: (ofe) ofe begin
definition n_equiv_heapG_ext :: "nat \<Rightarrow> 'a heapG_ext \<Rightarrow> 'a heapG_ext \<Rightarrow> bool" where 
  "n_equiv_heapG_ext n hG1 hG2 \<equiv> (case Rep_heapG_ext hG1 of (h1,m1) \<Rightarrow> case Rep_heapG_ext hG2 of (h2,m2) \<Rightarrow> 
     n_equiv n h1  h2 \<and> n_equiv n m1 m2)"
definition ofe_eq_heapG_ext :: "'a heapG_ext \<Rightarrow> 'a heapG_ext \<Rightarrow> bool" where 
  "ofe_eq_heapG_ext hG1 hG2 \<equiv> (case Rep_heapG_ext hG1 of (h1,m1) \<Rightarrow> case Rep_heapG_ext hG2 of (h2,m2) \<Rightarrow> 
    ofe_eq h1  h2 \<and> ofe_eq m1 m2)"
instance by standard 
(auto simp: n_equiv_heapG_ext_def ofe_eq_heapG_ext_def ofe_refl ofe_sym ofe_limit intro: ofe_trans ofe_mono ofe_eq_eq) 
end
  
instance heapG_ext :: (discrete) discrete 
  by (standard; auto simp: n_equiv_heapG_ext_def ofe_eq_heapG_ext_def ofe_refl d_equiv d_eq)
  (metis Rep_heapG_ext_inject)+
  
instantiation heapG_ext :: (camera) camera begin
lift_definition valid_raw_heapG_ext :: "'a heapG_ext \<Rightarrow> sprop" is
  "\<lambda>(h,m) n. n_valid h n \<and> n_valid m n" by auto
definition pcore_heapG_ext :: "'a heapG_ext \<Rightarrow> 'a heapG_ext option" where
  "pcore_heapG_ext hG \<equiv> case Rep_heapG_ext hG of (h,m) \<Rightarrow> 
    (case pcore h of Some h' \<Rightarrow> 
      (case pcore m of Some m' \<Rightarrow> Some (heapG_ext h' m') 
      | _ \<Rightarrow> None) 
    | _ \<Rightarrow> None)"
definition op_heapG_ext :: "'a heapG_ext \<Rightarrow> 'a heapG_ext \<Rightarrow> 'a heapG_ext" where
  "op_heapG_ext hG1 hG2 \<equiv> case Rep_heapG_ext hG1 of (h1,m1) \<Rightarrow> case Rep_heapG_ext hG2 of (h2,m2) \<Rightarrow>
    heapG_ext (h1\<cdot>h2) (m1\<cdot>m2)"
instance proof
show "non_expansive (valid_raw::'a heapG_ext \<Rightarrow> sprop)"
  apply (rule non_expansiveI)
  apply (auto simp: n_equiv_heapG_ext_def valid_raw_heapG_ext_def n_equiv_sprop_def d_equiv Abs_sprop_inverse)
  using n_valid_ne ofe_mono ofe_sym by blast+
next
show "non_expansive (pcore::'a heapG_ext \<Rightarrow> 'a heapG_ext option)"
  apply (rule non_expansiveI)
  apply (auto simp: n_equiv_heapG_ext_def pcore_heapG_ext_def n_equiv_option_def d_equiv heapG_ext_abs Abs_heapG_ext_inverse split: option.splits)
  by (metis camera_props(9) n_equiv_option_def option.distinct(1) option.sel pcore_ne)+
next
show "non_expansive2 (op::'a heapG_ext \<Rightarrow> 'a heapG_ext \<Rightarrow> 'a heapG_ext)" by (rule non_expansive2I) 
  (auto simp: n_equiv_heapG_ext_def op_heapG_ext_def heapG_ext_abs Abs_heapG_ext_inverse)
next
fix a b c :: "'a heapG_ext"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" 
  by (auto simp: op_heapG_ext_def heapG_ext_abs Abs_heapG_ext_inverse camera_assoc split: prod.splits)
next
fix a b :: "'a heapG_ext"
show "a \<cdot> b = b \<cdot> a"
  by (auto simp: op_heapG_ext_def heapG_ext_abs Abs_heapG_ext_inverse camera_comm split: prod.splits)
next
fix a a' :: "'a heapG_ext"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a"
  by (auto simp: op_heapG_ext_def pcore_heapG_ext_def heapG_ext_abs Abs_heapG_ext_inverse 
    split: option.splits prod.splits) (metis Rep_heapG_ext_inverse camera_pcore_id)
next
fix a a' :: "'a heapG_ext"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a"
  by (auto simp: pcore_heapG_ext_def heapG_ext_abs Abs_heapG_ext_inverse camera_pcore_idem 
    split: option.splits prod.splits)
next
fix a a' b :: "'a heapG_ext"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  by (auto simp: op_heapG_ext_def pcore_heapG_ext_def heapG_ext_abs Abs_heapG_ext_inverse
    split: option.splits prod.splits)
  (metis option.distinct(1) Rep_heapG_ext_inverse heapG.ext_inject heapG_ext_abs option.inject 
    camera_pcore_mono)+
next
fix a b :: "'a heapG_ext" fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  by (auto simp: valid_raw_heapG_ext.rep_eq op_heapG_ext_def heapG_ext_abs Abs_heapG_ext_inverse 
    camera_valid_op split: prod.splits)
next
fix a b c :: "'a heapG_ext" fix n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b \<cdot> c) \<Longrightarrow> 
  \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c"
  apply (auto simp: valid_raw_heapG_ext.rep_eq op_heapG_ext_def heapG_ext_abs Abs_heapG_ext_inverse
    n_equiv_heapG_ext_def split: prod.splits)
  by (metis Rep_heapG_ext_inverse camera_extend heapG.ext_inject heapG_ext_abs)
qed
end

instance heapG_ext :: (dcamera) dcamera 
  apply (standard; auto simp: valid_def valid_raw_heapG_ext.rep_eq)
  using dcamera_valid_iff by blast+

instantiation heapG_ext :: (ucamera) ucamera begin
definition \<epsilon>_heapG_ext :: "'a heapG_ext" where [simp]: "\<epsilon>_heapG_ext \<equiv> heapG_ext \<epsilon> \<epsilon>"
instance proof standard
show "camera_class.valid (\<epsilon>::'a heapG_ext)" 
  by (auto simp: valid_def heapG_ext_abs valid_raw_heapG_ext.rep_eq Abs_heapG_ext_inverse \<epsilon>_n_valid)
next
fix a :: "'a heapG_ext" show "\<epsilon> \<cdot> a = a" 
  by (auto simp: heapG_ext_abs op_heapG_ext_def Abs_heapG_ext_inverse Rep_heapG_ext_inverse \<epsilon>_left_id 
    split: prod.splits)
next
show "pcore \<epsilon> = Some (\<epsilon>::'a heapG_ext)" 
  by (auto simp: heapG_ext_abs pcore_heapG_ext_def Abs_heapG_ext_inverse \<epsilon>_pcore split: option.splits)
qed
end

instance heapG_ext :: (ducamera) ducamera ..

abbreviation own_graph :: "graphUR auth \<Rightarrow> ('a::ucamera) graphG_scheme iprop" ("Own\<^sub>g _") where
  "own_graph \<equiv> \<lambda>g. Own\<lparr>graph=g,markings=\<epsilon>,\<dots>=\<epsilon>\<rparr>"
abbreviation own_marking :: "markingUR auth \<Rightarrow> ('a::ucamera) graphG_scheme iprop" ("Own\<^sub>m _") where
  "own_marking \<equiv> \<lambda>m. Own\<lparr>graph=\<epsilon>,markings=m,\<dots>=\<epsilon>\<rparr>"
abbreviation own_heap :: "heapGS \<Rightarrow> ('a::ucamera) heapG_scheme iprop" ("Own\<^sub>h _") where
  "own_heap \<equiv> \<lambda>h. Own\<lparr>graph=\<epsilon>,markings=\<epsilon>,heap=h,\<dots>=\<epsilon>\<rparr>"

definition points_to_graph :: "loc \<Rightarrow> dfrac \<Rightarrow> val \<Rightarrow> ('a::ucamera) heapG_scheme iprop" where
  "points_to_graph l dq v = Own\<^sub>h(Heap [l\<mapsto>(dq, to_ag (Some v))])"
abbreviation points_to_disc :: "loc \<Rightarrow> val \<Rightarrow> ('a::ucamera) heapG_scheme iprop" where 
  "points_to_disc \<equiv> \<lambda>l v. points_to_graph l DfracDiscarded v"
abbreviation points_to_own :: "loc \<Rightarrow> frac \<Rightarrow> val \<Rightarrow> ('a::ucamera) heapG_scheme iprop" where
  "points_to_own \<equiv> \<lambda>l p v. points_to_graph l (DfracOwn p) v"
abbreviation points_to_full :: "loc \<Rightarrow> val \<Rightarrow> ('a::ucamera) heapG_scheme iprop" where
  "points_to_full \<equiv> \<lambda>l v. points_to_own l 1 v"
  
end