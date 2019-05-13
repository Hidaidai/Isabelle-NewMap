theory nmap_assign   
imports
  nmap_expr
begin

type_synonym '\<alpha> proc        = " (bool, '\<alpha> \<times> '\<alpha>) uexpr"
type_synonym ('\<alpha>, '\<beta>) urel  = " (bool, '\<alpha> \<times> '\<beta>) uexpr"

subsection \<open>assignment statement\<close>

consts uassigns :: "'a usubst \<Rightarrow> 'b" ("\<langle>_\<rangle>\<^sub>a")
lift_definition assigns_r :: "'\<alpha> usubst \<Rightarrow> '\<alpha> proc "
  is "\<lambda> \<sigma> (b, b'). b' = \<sigma>(b)" .
adhoc_overloading
  uassigns assigns_r

consts uskip :: "'a" ("II")
definition skip_r :: " '\<alpha> proc " where "skip_r = assigns_r id"
print_theorems
adhoc_overloading
  uskip skip_r







syntax
  \<comment> \<open> Single and multiple assignement \<close>
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> proc"  ("'(_') := '(_')")  
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> proc"  (infixr ":=" 62)
  \<comment> \<open> Substitution constructor \<close>
  "_mk_usubst"      :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> usubst"

translations
  "_mk_usubst \<sigma> (_svid_unit x) v" \<rightleftharpoons> "\<sigma>(&x \<mapsto>\<^sub>s v)"
  "_mk_usubst \<sigma> (_svid_list x xs) (_uexprs v vs)" \<rightleftharpoons> "(_mk_usubst (\<sigma>(&x \<mapsto>\<^sub>s v)) xs vs)"
  "_assignment xs vs" => "CONST uassigns (_mk_usubst (CONST id) xs vs)"
  "_assignment x v" <= "CONST uassigns (CONST subst_upd (CONST id) x v)"
  "_assignment x v" <= "_assignment (_spvar x) v"
  "x,y := u,v" <= "CONST uassigns (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

lemma " \<langle>[y \<mapsto>\<^sub>s f]\<rangle>\<^sub>a =  y := f "
  by (simp add: pr_var_def)




(***    test begin    ***)
lemma assign_skip:
  assumes "vwb_lens x"
  shows "(x := &x) = II"
proof -
  have " [x \<mapsto>\<^sub>s var x] = id"
    by (simp add: assms usubst_upd_var_id)
  then show ?thesis
    by (simp add: assms skip_r_def usubst_upd_var_id)
qed

lemma assigns_simul2:
  assumes "vwb_lens x"
  shows "(x,x) := (u,v) = (x := v)"
  by (simp add: assms  usubst_upd_idem)

lemma assign_simul1:
  assumes "vwb_lens y" "x \<bowtie> y"
  shows "(x,y) := (1+1, &y) = (x := 2)"
  by (metis assms(1) assms(2) one_add_one pr_var_def usubst_upd_comm usubst_upd_pr_var_id)











(**

consts useq     :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 61)
lift_definition seqr::"('\<alpha>, '\<beta>) urel \<Rightarrow> ('\<beta>, '\<gamma>) urel \<Rightarrow>  (bool,'\<alpha> \<times> '\<gamma>) uexpr"
is "\<lambda> P Q b. b \<in> ({p. P p} O {q. Q q})" .
adhoc_overloading
  useq seqr


lemma assigns_comp: "(assigns_r f ;; assigns_r g) = assigns_r (g \<circ> f)" 





  


(***    test end    ***)




subsection \<open> nchoice statement  \<close>

class nchoice = 
  fixes nchoice :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)
  assumes nch_assoc   : "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
      and nch_commute : "x \<sqinter> y = y \<sqinter> x"
      and nch_idemp   : "(x \<sqinter> x) = x" 

      and nch_skip_left: " II \<sqinter> x = x"
      and nch_skip_right: "x \<sqinter>  II = x"
**)







(***
lemma (in nchoice) "(x:=3)  \<sqinter> (y:=4) =  (y:=4)  \<sqinter>  (x:=3)"
  by (simp add: nch_commute)


lemma " (a:=3)  \<sqinter> (b:=4) =  (b:=4)  \<sqinter>  (a:=3)  "
'a  = 'b state_scheme




subsection \<open> if-than-else statement  \<close>

definition ifprog :: " 'a  \<Rightarrow> bool \<Rightarrow> 'a  \<Rightarrow> 'a "  ("(_ \<triangleleft> _  \<triangleright>\<^sub>\<p>/ _)" [52,0,53] 52)
  where "x  \<triangleleft> P \<triangleright>\<^sub>\<p> y \<equiv> (THE z::'a . (P = True \<longrightarrow> z = x) \<and> (P = False \<longrightarrow> z = y))"

theorem ifprog_idemp : "x \<triangleleft> boole \<triangleright>\<^sub>\<p> x = x"
  by (simp add: ifprog_def)
***)







end