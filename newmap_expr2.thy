theory newmap_expr2
imports Main newmap_expr1
begin

subsection \<open> preparation \<close>

consts
  uifte    :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd"  ("(3_ \<triangleleft> _ \<triangleright>/ _)" [52,0,53] 52)

datatype 'a list = Empty | List 'a "'a list"
fun conc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixl "," 71)
where
  "conc Empty ys = ys"
| "conc (List x xs) ys = List x (conc xs ys)"

fun reverse :: "'a list \<Rightarrow> 'a list"
where
  "reverse Empty = Empty"
| "reverse (List x xs) = conc (reverse xs) (List x Empty)"

subsection \<open> conditional operaters \<close>

locale condi = comm_monoid_nchoice +
  fixes  next_two :: "bool \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ":*" 60)
  assumes LawA4_2_3: "(a :* (b :* x)) = ((a \<and> b) :* x)"
  and LawA4_1_0: "(a :* x)  \<sqinter>  (b :* y) = (a \<or> b) :* (x  \<sqinter> y)"
  and LawA4_2_1: "(a :* (x \<sqinter> y)) = ((a :* x) \<sqinter> (a :* y))"
  and condi_true: "(True :* x) = x"
  and condi_false: "(False :* x) = II"



lemma (in condi) LawA4_1_1: "(a :* x)  \<sqinter>  (b :* x) = (a \<or> b) :* x"
  by (simp add: LawA4_1_0 ncho.idemp)




subsection \<open> if-than-else operaters \<close>
locale ifprog = comm_monoid_nchoice + condi +
  fixes iftep :: "'a \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(3_ \<triangleleft> _ \<triangleright>\<^sub>\<p>/ _)" [52,0,53] 52)
  defines  "x \<triangleleft> a \<triangleright>\<^sub>\<p> y \<equiv> a \<triangleleft> x \<triangleright> y"
  assumes ifprog_def: "x \<triangleleft> a \<triangleright>\<^sub>\<p> y = (a :* x) \<sqinter> ((\<not> a) :* y)"
context ifprog 
begin
theorem ifprog_idemp : "x \<triangleleft> a \<triangleright>\<^sub>\<p> x = x"
  by (simp add: LawA4_1_1 condi_true local.ifprog_def)

theorem ifprog_compl : "y \<triangleleft> (\<not> a) \<triangleright>\<^sub>\<p> x = x \<triangleleft> a \<triangleright>\<^sub>\<p> y "
  by (simp add: local.ifprog_def ncho.commute)

(*
theorem ifprog_assoc : "(x \<triangleleft> a \<triangleright>\<^sub>\<p> y) \<triangleleft> b \<triangleright>\<^sub>\<p> z = x \<triangleleft> a \<and> b \<triangleright>\<^sub>\<p> (y \<triangleleft> b \<triangleright>\<^sub>\<p> z)"
proof -
  have f1: "(x \<triangleleft> a \<triangleright>\<^sub>\<p> y) \<triangleleft> b \<triangleright>\<^sub>\<p> z = ((b \<and> a) :* x) \<sqinter> ((b \<and>(\<not> a)) :* y)  \<sqinter> ((\<not> b) :* z)"
    by (metis LawA4_2_1 LawA4_2_3 ifprog.axioms(3) ifprog_axioms ifprog_axioms_def iftep_def)
  then have f2: "x \<triangleleft> a \<and> b \<triangleright>\<^sub>\<p> (y \<triangleleft> b \<triangleright>\<^sub>\<p> z) =((b \<and> a) :* x) \<sqinter> ((\<not>(b \<and> a)\<and>b) :* y) \<sqinter> ((\<not>(b \<and> a)\<and>(\<not>b)) :* z)"
theorem ifprog_distr : " x \<triangleleft> a \<triangleright>\<^sub>\<p> (y \<triangleleft> b \<triangleright>\<^sub>\<p> z) = (x \<triangleleft> a \<triangleright>\<^sub>\<p> y) \<triangleleft> b \<triangleright>\<^sub>\<p> (x \<triangleleft> a \<triangleright>\<^sub>\<p> z)"
  sledgehammer
*)

theorem ifprog_true : "x \<triangleleft> True \<triangleright>\<^sub>\<p> y = x"
  by (simp add: condi_false condi_true condi_axioms local.ifprog_def)

theorem ifprog_false : "x \<triangleleft> False \<triangleright>\<^sub>\<p> y = y"
  by (simp add: condi_false condi_true condi_axioms local.ifprog_def)
end


subsection \<open> if-than-else operaters \<close>
locale ifbool = ifprog + monoid_nchoice +
  fixes ifteb :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"  ("(3_ \<triangleleft> _ \<triangleright>\<^sub>\<b>/ _)" [51,0,52] 51)
  defines  "a \<triangleleft> b \<triangleright>\<^sub>\<b> c \<equiv> a \<triangleleft> b \<triangleright> c"
  assumes ifbool_def : "x \<triangleleft> (a \<triangleleft> b \<triangleright>\<^sub>\<b> c) \<triangleright>\<^sub>\<p> y = (((b\<and>a)\<or>(\<not>b\<and>c)) :* x) \<sqinter> (((\<not>b\<and>\<not>c)\<or>(b\<and>\<not>a)) :* y)"
context ifbool
begin
theorem ifbool_idemp :

shows "x \<triangleleft> (a \<triangleleft> b \<triangleright>\<^sub>\<b> a) \<triangleright>\<^sub>\<p> y = x \<triangleleft> a \<triangleright>\<^sub>\<p> y"
  by (smt ifbool_def local.ifprog_def)

theorem ifbool_true : "x \<triangleleft> (a \<triangleleft> True \<triangleright>\<^sub>\<b> c) \<triangleright>\<^sub>\<p> y = x \<triangleleft> a \<triangleright>\<^sub>\<p> y"
  using local.ifbool_def local.ifprog_def by auto

theorem ifbool_false : "x \<triangleleft> (a \<triangleleft> False \<triangleright>\<^sub>\<b> c) \<triangleright>\<^sub>\<p> y = x \<triangleleft> c \<triangleright>\<^sub>\<p> y"
  using local.ifbool_def local.ifprog_def by auto
end



subsection \<open> if-than-else operaters \<close>
locale assi = 
  fixes asss :: "'b list\<Rightarrow> 'b list\<Rightarrow> 'a"  (infixl ":=" 70)
  assumes assi_total: "v:=e = v,u:=e,u"
    and assi_idemp: "v,u:=e,u = u,v:=u,e"

(* u a list of variables disjoint with v,it needs definition*)



subsection \<open> if-than-else operaters \<close>
locale iflist = assi + ifprog +
  fixes iftel :: "'a list\<Rightarrow> bool \<Rightarrow> 'a list\<Rightarrow> 'a list"  ("(3_ \<triangleleft> _ \<triangleright>\<^sub>l/ _)" [52,0,53] 52)
  defines  "v \<triangleleft> a \<triangleright>\<^sub>l u \<equiv> v \<triangleleft> a \<triangleright> u"
  assumes  iflist_def: " v:=(g \<triangleleft> a \<triangleright>\<^sub>l h) = ((v:=g) \<triangleleft> a \<triangleright>\<^sub>\<p> (v:=h))"
context iflist
begin
theorem iflist_idemp: "v:=(g \<triangleleft> a \<triangleright>\<^sub>l g) = v:=g"
  using ifprog_idemp local.iflist_def by auto

theorem iflist_true: "v:=(g \<triangleleft> True \<triangleright>\<^sub>l h) = v:=g"
  by (simp add: ifprog_true local.iflist_def)
(*here has problem,when i changde g to h.sledgehammer still can find proof*)

theorem iflist_false: "v:=(g \<triangleleft> False \<triangleright>\<^sub>l h) = v:=h"
  by (simp add: ifprog_false local.iflist_def)
end



subsection \<open> all operaters \<close>

locale all_operater = serial + assi + ifprog + ifbool + iflist + comm_monoid_nchoice + condi +
  assumes all_1: "\<forall>x \<in> A. a :* \<Sqinter>(A)  =  \<Sqinter>{(a :* x)}"
      and all_2: "\<forall>x \<in> A. \<Sqinter>{(a :* x)}  \<sqinter> ((\<not>a) :* y) = \<Sqinter>{x \<triangleleft> a \<triangleright> y}"
      and all_3: "\<forall>y \<in> B. (a :* x) \<sqinter>  \<Sqinter>{((\<not>a):* y)} = \<Sqinter>{x \<triangleleft> a \<triangleright> y}"
      and serial_1: "\<forall>x \<in> A. \<Sqinter>(A) ; y = \<Sqinter>{(x ; y)}"
      and serial_2: "\<forall>y \<in> B. x ; \<Sqinter>(B) = \<Sqinter>{(x ; y)}"
      and fasdfa: "((v:=g) \<triangleleft> True \<triangleright>\<^sub>\<p> (v:= h)) = v:=(g \<triangleleft> True \<triangleright>\<^sub>l h)"






subsection \<open>LawA2\<close>

lemma (in all_operater) LawA2_1:
  shows "v:=e = v,u:=e,u"
  by(simp add:assi_total)
(*LawA2_1*)

lemma (in all_operater) LawA2_2:
  shows "v,u:=e,u = u,v:=u,e"
  by(simp add:assi_idemp)
(*LawA2_2*)

lemma (in all_operater) LawA2_3:
  shows "((v:=g) \<triangleleft> True \<triangleright>\<^sub>\<p> (v:= h)) = v:=(g \<triangleleft> True \<triangleright>\<^sub>l h)"
  by(simp add:fasdfa)
(*LawA2_3*)

lemma (in all_operater) LawA2_4:
  shows "v:=e =  \<bottom> \<triangleleft> False \<triangleright>\<^sub>\<p> v,u:=e,u"
  by (simp add: assi_total ifprog_false)
(*LawA2_4*)

lemma (in all_operater) LawA2_5:
    shows "\<bottom> \<triangleleft> True \<triangleright>\<^sub>\<p> y = \<bottom>"
  by (simp add: ifprog_true)
(*LawA2_5*)



subsection \<open>LawA3\<close>

lemma (in all_operater) LawA3_1_1:
  assumes "finite A" and "finite B"
  shows "\<Sqinter>(A \<union> B)  = \<Sqinter>(A-(A \<inter> B)) \<sqinter> \<Sqinter>(B-(A \<inter> B)) \<sqinter> \<Sqinter>(A \<inter> B)"
  by (simp add: Diff_Int Nchoice.union_diff2 assms)

lemma (in all_operater) LawA3_1_2:
  assumes "finite A" and "finite B"
  shows "\<Sqinter>(A \<union> B)  = \<Sqinter>(A-(A \<inter> B)) \<sqinter> \<Sqinter>(B-(A \<inter> B)) \<sqinter> \<Sqinter>(A \<inter> B)  \<sqinter> \<Sqinter>(A \<inter> B)"
  by (simp add: LawA3_1_1 ncho.assoc ncho.idemp assms)

lemma (in all_operater) LawA3_1:
  assumes "finite A" and "finite B"
  shows "\<Sqinter>(A \<union> B)  = \<Sqinter>(A) \<sqinter> \<Sqinter>(B)"
  by (metis LawA3_1_1 LawA3_1_2 Nchoice.union_inter assms)
(*LawA3_1*)

lemma (in all_operater) ifprog_3:
  assumes "finite A" and "finite B"
    shows "\<forall>x \<in> A.\<forall>y \<in> B. (\<Sqinter>(A) \<triangleleft> a \<triangleright>\<^sub>\<p> \<Sqinter>(B)) = \<Sqinter>{x \<triangleleft> a \<triangleright>\<^sub>\<p> y}"
  by (simp add: all_1 local.ifprog_def)
(*LawA3_2*)

lemma (in all_operater) serial_3:
  assumes "finite A" and "finite B"
    shows "\<forall>x \<in> A.\<forall>y \<in> B. (\<Sqinter>(A) ; \<Sqinter>(B)) = \<Sqinter>{(x ; y)}"
  by (simp add: serial_1 serial_2)
(*LawA3_3*)

lemma (in all_operater) ifprog_4:
  assumes "finite A" 
    shows "\<bottom> \<triangleleft> False \<triangleright>\<^sub>\<p> \<Sqinter>(A) = \<Sqinter>A"
  by (simp add: ifprog_false)
(*LawA3_4*)



print_locale! all_operater

subsection \<open>LawA4\<close>

lemma (in all_operater) LawA4_1:
  assumes "finite A" and "finite B"
  shows  "(\<bottom> \<triangleleft> b \<triangleright>\<^sub>\<p> \<Sqinter>A) \<sqinter> (\<bottom> \<triangleleft> c \<triangleright>\<^sub>\<p> \<Sqinter>B) = \<bottom> \<triangleleft> (b \<or> c) \<triangleright>\<^sub>\<p> (\<Sqinter>A \<sqinter> \<Sqinter>B)"
proof -
  have "(\<bottom> \<triangleleft> b \<triangleright>\<^sub>\<p> \<Sqinter>A) \<sqinter> (\<bottom> \<triangleleft> c \<triangleright>\<^sub>\<p> \<Sqinter>B) = (b :*\<bottom>) \<sqinter> ((\<not>b) :* (\<Sqinter>A)) \<sqinter> (c :*\<bottom>) \<sqinter> ((\<not>c) :* (\<Sqinter>B))"
    by (simp add: local.ifprog_def nchoice_assoc)
  then have "(\<bottom> \<triangleleft> b \<triangleright>\<^sub>\<p> \<Sqinter>A) \<sqinter> (\<bottom> \<triangleleft> c \<triangleright>\<^sub>\<p> \<Sqinter>B) = ((b \<or> c) :*\<bottom>) \<sqinter> (((\<not>b) \<or> (\<not>c)) :* ((\<Sqinter>B) \<sqinter> (\<Sqinter>A)))"
    by (simp add: LawA4_1_0)
  then show ?thesis
    using LawA4_1_0 local.ifprog_def by auto
qed
(*LawA4_1*)

lemma (in all_operater) LawA4_2: 
  assumes "finite A" and "finite B"
  shows "(\<bottom> \<triangleleft> b \<triangleright>\<^sub>\<p> \<Sqinter>A) \<triangleleft> d \<triangleright>\<^sub>\<p> (\<bottom> \<triangleleft> c \<triangleright>\<^sub>\<p> \<Sqinter>B) = \<bottom> \<triangleleft> (b \<triangleleft> d \<triangleright>\<^sub>\<b> c) \<triangleright>\<^sub>\<p> (\<Sqinter>A \<triangleleft> d \<triangleright>\<^sub>\<p> \<Sqinter>B)"
proof -
  have "(\<bottom> \<triangleleft> b \<triangleright>\<^sub>\<p> \<Sqinter>A) \<triangleleft> d \<triangleright>\<^sub>\<p> (\<bottom> \<triangleleft> c \<triangleright>\<^sub>\<p> \<Sqinter>B) = ((d:*(b:*\<bottom>)) \<sqinter> (d :*((\<not>b):*\<Sqinter>A))) \<sqinter> (((\<not>d):*(c:*\<bottom>)) \<sqinter> ((\<not>d):*((\<not>c):*\<Sqinter>B)))"
    by (simp add: LawA4_2_1 local.ifprog_def)
  then have "(\<bottom> \<triangleleft> b \<triangleright>\<^sub>\<p> \<Sqinter>A) \<triangleleft> d \<triangleright>\<^sub>\<p> (\<bottom> \<triangleleft> c \<triangleright>\<^sub>\<p> \<Sqinter>B) = (((d \<and> b)\<or>(\<not>d \<and> c)):* \<bottom>) \<sqinter> (d:*((\<not>b):*\<Sqinter>A))\<sqinter>((\<not>d):*((\<not>c):*\<Sqinter>B))"
    by (simp add: LawA4_1_0 ifprog_idemp local.ifprog_def)
  then have "(\<bottom> \<triangleleft> b \<triangleright>\<^sub>\<p> \<Sqinter>A) \<triangleleft> d \<triangleright>\<^sub>\<p> (\<bottom> \<triangleleft> c \<triangleright>\<^sub>\<p> \<Sqinter>B) = (((d \<and> b)\<or>(\<not>d \<and> c)):* \<bottom>) \<sqinter> (((d\<and>\<not>b):*(\<Sqinter>A)) \<sqinter> ((\<not>d\<and>\<not>c) :* \<Sqinter>B))"
    by (simp add: ncho.assoc  LawA4_2_3)
  then have "(\<bottom> \<triangleleft> b \<triangleright>\<^sub>\<p> \<Sqinter>A) \<triangleleft> d \<triangleright>\<^sub>\<p> (\<bottom> \<triangleleft> c \<triangleright>\<^sub>\<p> \<Sqinter>B) = (((d \<and> b)\<or>(\<not>d \<and> c)):* \<bottom>) \<sqinter> (((d\<and>\<not>b)\<or>(\<not>d\<and>\<not>c)) :* (\<Sqinter>A \<triangleleft> d \<triangleright>\<^sub>\<p> \<Sqinter>B))"
    by (simp add: condi.LawA4_1_0 condi_axioms)
  then show ?thesis
    by (smt local.ifbool_def)
qed
(*LawA4_2*)

(*LawA4_3*)
  
(*LawA4_4 , zhege da V you shengyou yong? *)

(*LawA4_5 zhege wenti he 4_2 yiyang P;c bu shi bool datatypes *)


end