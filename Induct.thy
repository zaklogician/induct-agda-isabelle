theory Induct
imports Main
begin

(* The downward closure of a set. *)
inductive "downset" :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "downset_lit": "\<phi> x \<Longrightarrow> downset \<phi> x" |
  "downset_pred": "downset \<phi> (Suc x) \<Longrightarrow> downset \<phi> x"
print_theorems

lemma
  "downset (downset \<phi>) x \<Longrightarrow> downset \<phi> x"
  oops