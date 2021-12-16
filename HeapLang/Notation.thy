theory Notation
imports HeapLang
begin

text \<open> Loosely based on https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/notation.v\<close>

abbreviation "LamE \<equiv> Rec None"
abbreviation "LamV \<equiv> RecV None"
abbreviation "LetE \<equiv> \<lambda>x e1 e2. App (LamE x e2) e1"
abbreviation "NoneE \<equiv> InjL (Val (LitV LitUnit))"
abbreviation "NoneV \<equiv> InjLV (LitV LitUnit)"
abbreviation "SomeE \<equiv> InjR"
abbreviation "SomeV \<equiv> InjRV"
abbreviation "CAS \<equiv> \<lambda>l e1 e2. Snd (CmpXchg l e1 e2)"
abbreviation "FalseV \<equiv> LitV (LitBool False)"
abbreviation "FalseE \<equiv> Val (LitV (LitBool False))"
abbreviation "TrueV \<equiv> LitV (LitBool True)"
abbreviation "TrueE \<equiv> Val (LitV (LitBool True))"
abbreviation "MatchE \<equiv> \<lambda>e0 x1 e1 x2 e2. Case e1 (LamE x1 e1) (LamE x2 e2)"
abbreviation "MatchOpt \<equiv> \<lambda>e0 e1 x2 e2. MatchE e1 None e1  x2 e2"
abbreviation "Seq \<equiv> \<lambda>e2 e1. App (LamE None e1) e2"
abbreviation "UnitE \<equiv> Val (LitV LitUnit)"
abbreviation "Alloc \<equiv> AllocN (Val (LitV (LitInt 1)))"

notation LamE ("E\<lambda>_: _")
notation LamV ("V\<lambda>_: _")
notation LetE ("let: _ := _ in _ tel" 40)
notation Load ("!_")
notation Store (infix "\<leftarrow>" 60)
notation MatchOpt ("match: _ with NoneCase \<Rightarrow> _ | SomeCase _ \<Rightarrow> _ hctam")
notation If ("if: _ then _ else _ fi")
notation Seq (infixl ";;" 40)
notation Var ("V_")
end