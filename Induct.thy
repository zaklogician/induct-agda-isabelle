theory Induct
imports Main
begin

(* The downward closure of a set. *)
inductive "downset" :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "downset_lit": "\<phi> x \<Longrightarrow> downset \<phi> x" |
  "downset_pred": "downset \<phi> (Suc x) \<Longrightarrow> downset \<phi> x"

(* Example 1: The downset of a downset is itself. Simple induction. *)
lemma downset_downset:
  "downset (downset \<phi>) x \<Longrightarrow> downset \<phi> x"
  apply (induct "downset \<phi>" x rule: downset.induct)
  by (auto simp: downset_pred)

(* Example 2: Downsets are downward closed. Auto takes care of it. *)
lemma downset_downward_closed:
  "downset \<phi> x \<Longrightarrow> x \<le> y \<Longrightarrow> downset \<phi> x"
  by auto