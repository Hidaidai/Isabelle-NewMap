theory Ifte
imports Nchoice
begin

definition ifprog :: " 'a proc  \<Rightarrow> bool \<Rightarrow> 'a proc \<Rightarrow> 'a proc"  ("(_ \<triangleleft> _  \<triangleright>\<^sub>\<p>/ _)" [52,0,53] 52)
  where "x  \<triangleleft> P  \<triangleright>\<^sub>\<p> y \<equiv> (THE z::'a proc. (P = True \<longrightarrow> z = x) \<and> (P = False \<longrightarrow> z = y))"
(***I hope I can use abbreviation to define this If-then-else!
typedef ('t, '\<alpha>) uexpr = "UNIV :: ('\<alpha> \<Rightarrow> 't) set" ..
......
abbreviation cond ::
  "('a,'\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr \<Rightarrow> ('a,'\<alpha>) uexpr \<Rightarrow> ('a,'\<alpha>) uexpr"
  ("(3_ \<triangleleft> _ \<triangleright>/ _)" [52,0,53] 52)
  where "P \<triangleleft> b \<triangleright> Q \<equiv> trop uIf b P Q"
***)
theorem ifprog_idemp : "x \<triangleleft> a \<triangleright>\<^sub>\<p> x = x"
  by (simp add: ifprog_def)

theorem ifprog_compl : "y \<triangleleft> (\<not> a) \<triangleright>\<^sub>\<p> x = x \<triangleleft> a \<triangleright>\<^sub>\<p> y "
  by (metis (no_types) If_def ifprog_def)

theorem ifprog_true : "x \<triangleleft> True \<triangleright>\<^sub>\<p> y = x"
  by (simp add: ifprog_def)

theorem ifprog_false : "x \<triangleleft> False \<triangleright>\<^sub>\<p> y = y"
   by (simp add: ifprog_def)




definition ifbool :: "bool  \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"  ("(_ \<triangleleft> _ \<triangleright>\<^sub>\<b>/ _)" [52,0,53] 52)
  where "x \<triangleleft> P \<triangleright>\<^sub>\<b> y \<equiv> (THE z:: bool. (P = True \<longrightarrow> z = x) \<and> (P = False \<longrightarrow> z = y))"

theorem ifbool_idemp : "x \<triangleleft> (a \<triangleleft> b \<triangleright>\<^sub>\<b> a) \<triangleright>\<^sub>\<p> y = x \<triangleleft> a \<triangleright>\<^sub>\<p> y"
  by (simp add: ifbool_def)

theorem ifbool_true : "x \<triangleleft> (a \<triangleleft> True \<triangleright>\<^sub>\<b> c) \<triangleright>\<^sub>\<p> y = x \<triangleleft> a \<triangleright>\<^sub>\<p> y"
  by (simp add: ifbool_def)

theorem ifbool_false : "x \<triangleleft> (a \<triangleleft> False \<triangleright>\<^sub>\<b> c) \<triangleright>\<^sub>\<p> y = x \<triangleleft> c \<triangleright>\<^sub>\<p> y"
  by (simp add: ifbool_def)




definition iflist :: "'a list \<Rightarrow> bool \<Rightarrow> 'a list\<Rightarrow> 'a list"   ("(3_ \<triangleleft> _ \<triangleright>\<^sub>l/ _)" [52,0,53] 52)
  where "x \<triangleleft> P \<triangleright>\<^sub>l y \<equiv> (THE z:: 'a list. (P = True \<longrightarrow> z = x) \<and> (P = False \<longrightarrow> z = y))"

theorem iflist_idemp: "v:=(g \<triangleleft> a \<triangleright>\<^sub>l g) = v:=g"
  by (simp add: iflist_def)

theorem iflist_true: "v:=(g \<triangleleft> True \<triangleright>\<^sub>l h) = v:=g"
  by (simp add: iflist_def)

theorem iflist_false: "v:=(g \<triangleleft> False \<triangleright>\<^sub>l h) = v:=h"
  by (simp add: iflist_def)

theorem iflist_proc: "((v:=g) \<triangleleft> True \<triangleright>\<^sub>\<p> (v:= h)) = v:=(g \<triangleleft> True \<triangleright>\<^sub>l h)"
  by (simp add: iflist_true ifprog_true)




end