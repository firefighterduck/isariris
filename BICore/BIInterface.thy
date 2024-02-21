theory BIInterface
imports "../IrisCore/COFEs"
begin

locale bunched_implications = preorder bi_entails "\<lambda>P Q. (bi_entails P Q \<and> \<not> (bi_entails Q P))"
  for bi_entails :: "'prop::cofe \<Rightarrow> 'prop \<Rightarrow> bool" 
  +
fixes bi_emp :: 'prop
  and bi_pure :: "bool \<Rightarrow> 'prop"
  and bi_and :: "'prop \<Rightarrow> 'prop \<Rightarrow> 'prop"
  and bi_or :: "'prop \<Rightarrow> 'prop \<Rightarrow> 'prop"
  and bi_impl :: "'prop \<Rightarrow> 'prop \<Rightarrow> 'prop"
  and bi_forall :: "('a \<Rightarrow> 'prop) \<Rightarrow> 'prop"
  and bi_exists :: "('a \<Rightarrow> 'prop) \<Rightarrow> 'prop"
  and bi_sep :: "'prop \<Rightarrow> 'prop \<Rightarrow> 'prop"
  and bi_wand :: "'prop \<Rightarrow> 'prop \<Rightarrow> 'prop"
assumes bi_equiv_entails: "ofe_eq P Q \<longleftrightarrow> (bi_entails P Q) \<and> (bi_entails Q P)"
  \<comment> \<open>Non-expansiveness\<close>
  and bi_pure_ne: "non_expansive bi_pure"
  and bi_and_ne: "non_expansive2 bi_and"
  and bi_or_ne: "non_expansive2 bi_or"
  and bi_impl_ne: "non_expansive2 bi_impl"
  and bi_forall_ne: "non_expansive bi_forall"
  and bi_exists_ne: "non_expansive bi_exists"
  and bi_sep_ne: "non_expansive2 bi_sep"
  and bi_wand_ne: "non_expansive2 bi_wand"
  \<comment> \<open>Higher-Order logic properties\<close>
  and bi_pure_intro: "b \<Longrightarrow> bi_entails P (bi_pure b)"
  and bi_pure_elim: "(b \<Longrightarrow> bi_entails (bi_pure True) P) \<Longrightarrow> bi_entails (bi_pure b) P"
  and bi_and_elimL: "bi_entails (bi_and P Q) P"
  and bi_and_elimR: "bi_entails (bi_and P Q) Q"
  and bi_and_intro: "\<lbrakk>bi_entails P Q; bi_entails P R\<rbrakk> \<Longrightarrow> bi_entails P (bi_and Q R)"
  and bi_or_introL: "bi_entails P (bi_or P Q)"
  and bi_or_introR: "bi_entails Q (bi_or P Q)"
  and bi_or_elim: "\<lbrakk>bi_entails P R; bi_entails Q R\<rbrakk> \<Longrightarrow> bi_entails (bi_or P Q) R"
  and bi_impl_introR: "bi_entails (bi_and P Q) R \<Longrightarrow> bi_entails P (bi_impl Q R)"
  and bi_impl_elimL: "bi_entails P (bi_impl Q R) \<Longrightarrow> bi_entails (bi_and P Q) R"
  and bi_forall_intro: "\<forall>x. bi_entails P (\<Phi> x) \<Longrightarrow> bi_entails P (bi_forall \<Phi>)"
  and bi_forall_elim: "bi_entails (bi_forall \<Phi>) (\<Phi> x)"
  and bi_exists_intro: "bi_entails (\<Phi> x) (bi_exists \<Phi>)"
  and bi_exists_elim: "\<forall>x. bi_entails (\<Phi> x) P \<Longrightarrow> bi_entails (bi_exists \<Phi>) P"
  \<comment> \<open>BI connectives\<close>
  and bi_sep_mono: "\<lbrakk>bi_entails P Q; bi_entails P' Q'\<rbrakk> \<Longrightarrow> bi_entails (bi_sep P P') (bi_sep Q Q')"
  and bi_emp_sep1: "bi_entails P (bi_sep bi_emp P)"
  and bi_emp_sep2: "bi_entails (bi_sep bi_emp P) P"
  and bi_sep_comm: "bi_entails (bi_sep P Q) (bi_sep Q P)"
  and bi_sep_assoc: "bi_entails (bi_sep (bi_sep P Q) R) (bi_sep P (bi_sep Q R))"
  and bi_wand_introR: "bi_entails (bi_sep P Q) R \<Longrightarrow> bi_entails P (bi_wand Q R)"
  and bi_wand_elimL: "bi_entails P (bi_wand Q R) \<Longrightarrow> bi_entails (bi_sep P Q) R"

\<comment> \<open>The persistency modality makes the BI logic intuitionistic (somehow).\<close>
locale bi_persistently = bunched_implications +
fixes bi_persistently :: "'a \<Rightarrow> 'a"
assumes bi_pers_ne: "non_expansive bi_persistently"
  and bi_pers_mono: "bi_entails P Q \<Longrightarrow> bi_entails (bi_persistently P) (bi_persistently Q)"
  and bi_per_idemp: "bi_entails (bi_persistently P) (bi_persistently (bi_persistently P))"
  and bi_pers_emp: "bi_entails bi_emp (bi_persistently bi_emp)"
  and bi_pers_and: "bi_entails (bi_and (bi_persistently P) (bi_persistently Q)) (bi_persistently (bi_and P Q))"
  and bi_pers_exists: "bi_entails (bi_persistently (bi_exists \<Phi>)) (bi_exists (\<lambda>x. bi_persistently (\<Phi> x)))"
  and bi_pers_absorbing: "bi_entails (bi_sep (bi_persistently P) Q) (bi_persistently P)"
  and bi_pers_and_sep_elim: "bi_entails (bi_and (bi_persistently P) Q) (bi_sep P Q)"

locale bi_later = bi_persistently +
fixes bi_later :: "'a \<Rightarrow> 'a"
assumes bi_later_ne: "non_expansive bi_later"
  and bi_later_mono: "bi_entails P Q \<Longrightarrow> bi_entails (bi_later P) (bi_later Q)"
  and bi_later_intro: "bi_entails P (bi_later P)"
  and bi_later_forall: "bi_entails (bi_forall (\<lambda>x. bi_later (\<Phi> x))) (bi_later (bi_forall \<Phi>))"
  and bi_later_exists_false: "bi_entails (bi_later (bi_exists \<Phi>)) (bi_or (bi_later (bi_pure False))
    (bi_exists (\<lambda>x. bi_later (\<Phi> x))))"
  and bi_later_sep1: "bi_entails (bi_later (bi_sep P Q)) (bi_sep (bi_later P) (bi_later Q))"
  and bi_later_sep2: "bi_entails (bi_sep (bi_later P) (bi_later Q)) (bi_later (bi_sep P Q))"
  and bi_later_pers1: "bi_entails (bi_later (bi_persistently P)) (bi_persistently (bi_later P))"
  and bi_later_pers2: "bi_entails (bi_persistently (bi_later P)) (bi_later (bi_persistently P))"
  and bi_later_false_em: "bi_entails (bi_later P) (bi_or (bi_later (bi_pure False)) 
    (bi_impl (bi_later (bi_pure False)) P))"

definition (in bunched_implications) bi_holds :: "'prop \<Rightarrow> bool" where
  "bi_holds P = bi_entails bi_emp P"
end