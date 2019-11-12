theory Induct
imports Main
begin

(* The downward closure of a set. *)
inductive "downset" :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "downset_lit": "\<phi> x \<Longrightarrow> downset \<phi> x" |
  "downset_pred": "downset \<phi> (Suc x) \<Longrightarrow> downset \<phi> x"

lemma
  "downset (downset \<phi>) x \<Longrightarrow> downset \<phi> x"
  apply (induct "downset \<phi>" x rule: downset.induct)
  by (auto simp: downset_pred)
