section \<open> Alphabetised Relations \<close>

theory nmap_assign
imports
  nmap_expr

begin

text \<open> An alphabetised relation is simply a predicate whose state-space is a product type. In this
  theory we construct the core operators of the relational calculus, and prove a libary of 
  associated theorems, based on Chapters 2 and 5 of the UTP book~\cite{Hoare&98}. \<close>
  
subsection \<open> Relational Alphabets \<close>
  
text \<open> We set up convenient syntax to refer to the input and output parts of the alphabet, as is
  common in UTP. Since we are in a product space, these are simply the lenses @{term "fst\<^sub>L"} and
  @{term "snd\<^sub>L"}. \<close>
  
definition in\<alpha> :: "('\<alpha> \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "in\<alpha> = fst\<^sub>L"

definition out\<alpha> :: "('\<beta> \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "out\<alpha> = snd\<^sub>L"

lemma in\<alpha>_uvar [simp]: "vwb_lens in\<alpha>"
  by (unfold_locales, auto simp add: in\<alpha>_def)

lemma out\<alpha>_uvar [simp]: "vwb_lens out\<alpha>"
  by (unfold_locales, auto simp add: out\<alpha>_def)

lemma var_in_alpha [simp]: "x ;\<^sub>L in\<alpha> = ivar x"
  by (simp add: fst_lens_def in\<alpha>_def in_var_def)

lemma var_out_alpha [simp]: "x ;\<^sub>L out\<alpha> = ovar x"
  by (simp add: out\<alpha>_def out_var_def snd_lens_def)

lemma out_alpha_in_indep [simp]:
  "out\<alpha> \<bowtie> in_var x" "in_var x \<bowtie> out\<alpha>"
  by (simp_all add: in_var_def out\<alpha>_def lens_indep_def fst_lens_def snd_lens_def lens_comp_def)

lemma in_alpha_out_indep [simp]:
  "in\<alpha> \<bowtie> out_var x" "out_var x \<bowtie> in\<alpha>"
  by (simp_all add: in_var_def in\<alpha>_def lens_indep_def fst_lens_def lens_comp_def)

text \<open> The following two functions lift a predicate substitution to a relational one. \<close>
 
abbreviation usubst_rel_lift :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<times> '\<beta>) usubst" ("\<lceil>_\<rceil>\<^sub>s") where
"\<lceil>\<sigma>\<rceil>\<^sub>s \<equiv> \<sigma> \<oplus>\<^sub>s in\<alpha>"

abbreviation usubst_rel_drop :: "('\<alpha> \<times> '\<alpha>) usubst \<Rightarrow> '\<alpha> usubst" ("\<lfloor>_\<rfloor>\<^sub>s") where
"\<lfloor>\<sigma>\<rfloor>\<^sub>s \<equiv> \<sigma> \<restriction>\<^sub>s in\<alpha>"

text \<open> The alphabet of a relation then consists wholly of the input and output portions. \<close>

lemma alpha_in_out:
  "\<Sigma> \<approx>\<^sub>L in\<alpha> +\<^sub>L out\<alpha>"
  by (simp add: fst_snd_id_lens in\<alpha>_def lens_equiv_refl out\<alpha>_def)

subsection \<open> Relational Types and Operators \<close>

text \<open> We create type synonyms for conditions (which are simply predicates) -- i.e. relations
  without dashed variables --, alphabetised relations where the input and output alphabet can
  be different, and finally homogeneous relations. \<close>
type_synonym '\<alpha> hrel        = " (bool, '\<alpha> \<times> '\<alpha>) uexpr"

text \<open> We set up some overloaded constants for sequential composition and the identity in case
  we want to overload their definitions later. \<close>
  
consts
  useq     :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 61)
  uassigns :: "'a usubst \<Rightarrow> 'b" ("\<langle>_\<rangle>\<^sub>a")
  uskip    :: "'a" ("II")
  


text \<open> Assignment is defined using substitutions, where latter defines what each variable should
  map to. The definition of the operator identifies the after state binding, $b'$, with the 
  substitution function applied to the before state binding $b$. \<close>
  
lift_definition assigns_r :: "'\<alpha> usubst \<Rightarrow> '\<alpha> hrel "
  is "\<lambda> \<sigma> (b, b'). b' = \<sigma>(b)" .

adhoc_overloading
  uassigns assigns_r
    
text \<open> Relational identity, or skip, is then simply an assignment with the identity substitution:
  it simply identifies all variables. \<close>
    
definition skip_r :: " '\<alpha> hrel " where"skip_r = assigns_r id"

adhoc_overloading
  uskip skip_r
 
text \<open> A singleton assignment simply applies a singleton substitution function, and similarly
  for a double assignment. \<close>

abbreviation assign_r :: "('t \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel "
where "assign_r x v \<equiv> \<langle>[x \<mapsto>\<^sub>s v]\<rangle>\<^sub>a"

abbreviation assign_2_r ::
  "('t1 \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t2 \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t1, '\<alpha>) uexpr \<Rightarrow> ('t2, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel "
where "assign_2_r x y u v \<equiv> assigns_r [x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v]"

text \<open> We also define the alphabetised skip operator that identifies all input and output variables
  in the given alphabet lens. All other variables are unrestricted. We also set up syntax for it. \<close>
  
definition skip_ra :: "('\<beta>, '\<alpha>) lens \<Rightarrow>  '\<alpha> hrel " where "skip_ra v = ($v\<acute> =\<^sub>u $v)"

text \<open> Similarly, we define the alphabetised assignment operator. \<close>

definition assigns_ra :: "'\<alpha> usubst \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> '\<alpha> hrel " ("\<langle>_\<rangle>\<^bsub>_\<^esub>") where
"\<langle>\<sigma>\<rangle>\<^bsub>a\<^esub> = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> skip_ra a)"









subsection \<open> Syntax Translations \<close>
    
syntax
  \<comment> \<open> Single and multiple assignement \<close>
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  ("'(_') := '(_')")  
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  (infixr ":=" 62)
  \<comment> \<open> Substitution constructor \<close>
  "_mk_usubst"      :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> usubst"


translations
  "_mk_usubst \<sigma> (_svid_unit x) v" \<rightleftharpoons> "\<sigma>(&x \<mapsto>\<^sub>s v)"
  "_mk_usubst \<sigma> (_svid_list x xs) (_uexprs v vs)" \<rightleftharpoons> "(_mk_usubst (\<sigma>(&x \<mapsto>\<^sub>s v)) xs vs)"
  "_assignment xs vs" => "CONST uassigns (_mk_usubst (CONST id) xs vs)"
  "_assignment x v" <= "CONST uassigns (CONST subst_upd (CONST id) x v)"
  "_assignment x v" <= "_assignment (_spvar x) v"
  "x,y := u,v" <= "CONST uassigns (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

(***    test begin    ***)
lemma assign_vacuous_skip:
  assumes "vwb_lens x"
  shows "(x := &x) = II"
  by (metis assms pr_var_def skip_r_def usubst_upd_pr_var_id)
  
lemma assign_simultaneous:
  assumes "vwb_lens y" "x \<bowtie> y"
  shows "(x,y) := (e, &y) = (x := e)"
  by (simp add: assms usubst_upd_comm usubst_upd_var_id)

lemma assigns_idem: "mwb_lens x \<Longrightarrow> (x,x) := (u,v) = (x := v)"
  by (simp add: usubst)

alphabet state =
  a :: int
  b :: int 
  c :: int

text \<open> Prove a simple relational equality \<close>
  
theorem "(a,b) := (2, &b) = (a := 2)"
  by (simp add:  usubst_upd_comm usubst_upd_var_id)

theorem "(a,b) := (2, &a+1) = (a,b) := (2,&a+1)"
  by simp

theorem "(a,b,c) := (2, &b, 4) = (a,c) := (2,4)"
  by (metis b_vwb_lens pr_var_def state_indeps(1) usubst_upd_comm usubst_upd_pr_var_id)

theorem "(b := 3) = (b,a) := (3 ,&a)"
  by (simp add:  usubst_upd_comm usubst_upd_var_id)

lemma "a \<bowtie> b"
  by simp

lemma assign_simueweltaus:
  assumes "vwb_lens a" "a \<bowtie> b"
  shows "(a,b) := (3, &b) = (a := 3)"
  by (simp add: assms usubst_upd_comm usubst_upd_var_id)
(***   test end   ***)


class nchoice = 
  fixes nchoice :: "'a hrel \<Rightarrow> 'a hrel \<Rightarrow> 'a hrel" (infixl "\<sqinter>" 70)
  assumes nch_assoc [algebra_simps, field_simps]: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
      and nch_commute [algebra_simps, field_simps]: "x \<sqinter> y = y \<sqinter> x"
      and nch_idemp [algebra_simps, field_simps]: "(x \<sqinter> x) = x" 
      and nch_skip_left: " II \<sqinter> x = x"
      and nch_skip_right: "x \<sqinter>  II = x"

lemma " (x:=3)  \<sqinter> (y:=4) =  (y:=4)  \<sqinter>  (x:=3)  "
  by (simp add: nch_commute)

(***
lemma " (a:=3)  \<sqinter> (b:=4) =  (b:=4)  \<sqinter>  (a:=3)  "
'a  = 'b state_scheme
***)


definition ifprog :: " 'a hrel  \<Rightarrow> bool \<Rightarrow> 'a hrel \<Rightarrow> 'a hrel"  ("(_ \<triangleleft> _  \<triangleright>\<^sub>\<p>/ _)" [52,0,53] 52)
  where "x  \<triangleleft> P  \<triangleright>\<^sub>\<p> y \<equiv> (THE z::'a hrel. (P = True \<longrightarrow> z = x) \<and> (P = False \<longrightarrow> z = y))"

theorem ifprog_idemp : "x \<triangleleft> boole \<triangleright>\<^sub>\<p> x = x"
  by (simp add: ifprog_def)

theorem  "(a:=5) \<triangleleft> True \<triangleright>\<^sub>\<p> (b:=6) = (a:=5)"
  by (simp add: ifprog_def)

end