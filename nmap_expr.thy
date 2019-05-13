theory nmap_expr
imports nmap_var
begin

section \<open> Expression type \<close>

typedef ('t, '\<alpha>) uexpr = "UNIV :: ('\<alpha> \<Rightarrow> 't) set" ..

notation Rep_uexpr ("\<lbrakk>_\<rbrakk>\<^sub>e")
lemma uexpr_eq_iff: "e = f \<longleftrightarrow> (\<forall> b. \<lbrakk>e\<rbrakk>\<^sub>e b = \<lbrakk>f\<rbrakk>\<^sub>e b)"
  using Rep_uexpr_inject[of e f, THEN sym] by (auto)

section \<open> Core expression constructs using lift_definition  \<close>

setup_lifting type_definition_uexpr
lift_definition var :: "('t \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t, '\<alpha>) uexpr" is lens_get .
print_theorems
lift_definition lit :: "'t \<Rightarrow> ('t, '\<alpha>) uexpr" ("\<guillemotleft>_\<guillemotright>") is "\<lambda> v b. v" .
lift_definition bop ::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr"
 is "\<lambda> f u v b. f (u b) (v b)" .

definition eq_upred :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infixl "=\<^sub>u" 50)
  where "eq_upred x y = bop HOL.eq x y"

subsection \<open> Type class instantiations\<close>
instantiation uexpr :: (zero, type) zero
begin
  definition zero_uexpr_def : "0 = lit 0"
instance ..
end

instantiation uexpr :: (one, type) one
begin
  definition one_uexpr_def : "1 = lit 1"
instance ..
end

instantiation uexpr :: (plus, type) plus
begin
  definition plus_uexpr_def : "u + v = bop (+) u v"
instance ..
end


instance uexpr :: (numeral, type) numeral
  by (intro_classes, simp add: plus_uexpr_def, transfer, simp add: add.assoc)


instantiation uexpr :: (ord, type) ord
begin
  lift_definition less_eq_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> bool"
  is "\<lambda> P Q. (\<forall> A. P A \<le> Q A)" .
  definition less_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> bool"
    where "less_uexpr P Q = (P \<le> Q \<and> \<not> Q \<le> P)"
instance ..
end

lemma lit_ueval : "\<lbrakk>\<guillemotleft>x\<guillemotright>\<rbrakk>\<^sub>eb = x"
  by (transfer, simp)

lemma var_ueval: "\<lbrakk>var x\<rbrakk>\<^sub>eb = get\<^bsub>x\<^esub> b"
  by (transfer, simp)

lemma bop_ueval : "\<lbrakk>bop f x y\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb)"
  by (transfer, simp)

lemma plus_ueval : "\<lbrakk>x + y\<rbrakk>\<^sub>eb = (\<lbrakk>x\<rbrakk>\<^sub>eb) + (\<lbrakk>y\<rbrakk>\<^sub>eb)"
  by (simp add: bop_ueval plus_uexpr_def)

subsection \<open>The fundamental lemma of computation\<close>
lemma lit_fun_simps  :
  "\<guillemotleft>g x y\<guillemotright> = bop g \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright>"
  by (transfer, simp)+

lemma numeral_uexpr_rep_eq: "\<lbrakk>numeral x\<rbrakk>\<^sub>e b = numeral x"
  apply (induct x)
    apply (simp add: lit.rep_eq one_uexpr_def)
   apply (simp add: bop.rep_eq numeral_Bit0 plus_uexpr_def)
  apply (simp add: bop.rep_eq lit.rep_eq numeral_code(3) one_uexpr_def plus_uexpr_def)
  done

lemma lit_zero [simp]: "\<guillemotleft>0\<guillemotright> = 0" by (simp add: zero_uexpr_def)
lemma lit_one [simp]: "\<guillemotleft>1\<guillemotright> = 1" by (simp add: one_uexpr_def)
lemma lit_plus [simp]: "\<guillemotleft>x + y\<guillemotright> = \<guillemotleft>x\<guillemotright> + \<guillemotleft>y\<guillemotright>" by (simp add: plus_uexpr_def, transfer, simp)
lemma lit_numeral [simp]: "\<guillemotleft>numeral n\<guillemotright> = numeral n" 
  by (simp add: uexpr_eq_iff numeral_uexpr_rep_eq lit.rep_eq)








section \<open> ???????????????? \<close>

syntax
  "_uuvar" :: "svar \<Rightarrow> logic" ("_")
translations
  "_uuvar x" == "CONST var x"






section \<open> Substitution definitions \<close>

consts usubst :: "'s \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "\<dagger>" 80)
type_synonym '\<alpha> usubst = "'\<alpha> \<Rightarrow> '\<alpha>"
lift_definition subst :: " '\<alpha> usubst \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" is
"\<lambda> \<sigma> e b. e (\<sigma> b)" .  
print_theorems
adhoc_overloading
  usubst subst
lemma show_usubst:
  shows "\<lbrakk> x \<dagger> P \<rbrakk>\<^sub>e = (\<lambda>b. \<lbrakk>P\<rbrakk>\<^sub>e (x b))"
  by (simp add: subst.rep_eq)


type_synonym ('\<alpha>,'\<beta>) psubst = "'\<alpha> \<Rightarrow> '\<beta>"
consts subst_upd :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> 'v \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<alpha>,'\<beta>) psubst"
definition subst_upd_uvar :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> ('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<alpha>,'\<beta>) psubst" where
"subst_upd_uvar \<sigma> x v = (\<lambda> b. put\<^bsub>x\<^esub> (\<sigma> b) (\<lbrakk>v\<rbrakk>\<^sub>e b))" 
adhoc_overloading
  subst_upd subst_upd_uvar
lemma show_subst_upd:
  shows " subst_upd_uvar \<sigma> x e  = (\<lambda>b. put\<^bsub>x\<^esub> (\<sigma> b) (\<lbrakk>e\<rbrakk>\<^sub>e b))     "
  by (simp add: subst_upd_uvar_def)


lift_definition usubst_lookup :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> ('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<langle>_\<rangle>\<^sub>s")
is "\<lambda> \<sigma> x b. get\<^bsub>x\<^esub> (\<sigma> b)" .
print_theorems
lemma show_usubst_lookup:
  shows "\<lbrakk> \<langle>\<sigma>\<rangle>\<^sub>s x \<rbrakk>\<^sub>e = (\<lambda>b. get\<^bsub>x\<^esub> (\<sigma> b))"
  by (simp add: usubst_lookup.rep_eq)






subsection \<open> Syntax translations about subsitution \<close>

nonterminal smaplet and smaplets and uexp and uexprs and salphas

syntax
  "_smaplet"  :: "[salpha, 'a] => smaplet"             ("_ /\<mapsto>\<^sub>s/ _")
  ""          :: "smaplet => smaplets"            ("_")
  "_SMaplets" :: "[smaplet, smaplets] => smaplets" ("_,/ _")
  "_SubstUpd" :: "['m usubst, smaplets] => 'm usubst" ("_/'(_')" [900,0] 900)
  "_Subst"    :: "smaplets => 'a \<rightharpoonup> 'b"            ("(1[_])")
  "_psubst"  :: "[logic, svars, uexprs] \<Rightarrow> logic"

  "_uexp_l"  :: "logic \<Rightarrow> uexp" ("_" [64] 64)
  "_uexprs"  :: "[uexp, uexprs] => uexprs" ("_,/ _")
  ""         :: "uexp => uexprs" ("_")
  "_salphas" :: "[salpha, salphas] => salphas" ("_,/ _")
  ""         :: "salpha => salphas" ("_")

translations
  "_SubstUpd m (_SMaplets xy ms)"     == "_SubstUpd (_SubstUpd m xy) ms"
  "_SubstUpd m (_smaplet x y)"        == "CONST subst_upd m x y"
  "_Subst ms"                         == "_SubstUpd (CONST id) ms"
  "_Subst (_SMaplets ms1 ms2)"        <= "_SubstUpd (_Subst ms1) ms2"
  "_SMaplets ms1 (_SMaplets ms2 ms3)" <= "_SMaplets (_SMaplets ms1 ms2) ms3"
  "_psubst m (_salphas x xs) (_uexprs v vs)" => "_psubst (_psubst m x v) xs vs"
  "_psubst m x v"  => "CONST subst_upd m x v"
  "_uexp_l e" => "e"

lemma hello_wodsrlddwe:
  assumes"vwb_lens x"
  shows " [x \<mapsto>\<^sub>s e]  = (\<lambda>b. put\<^bsub>x\<^esub> b (\<lbrakk>e\<rbrakk>\<^sub>e b))"
  by (simp add: subst_upd_uvar_def)






section \<open> Substitution Application Laws \<close>

subsection  \<open>id has no effect \<close>

lemma usubst_lookup_id : "\<langle>id\<rangle>\<^sub>s x = var x"
proof -
  have f1:"\<lbrakk>var x\<rbrakk>\<^sub>e = get\<^bsub>x\<^esub>"
    by (simp add: var.rep_eq)
  then have f2:"\<lbrakk>\<langle>id\<rangle>\<^sub>s x\<rbrakk>\<^sub>e = (\<lambda>b. get\<^bsub>x\<^esub> (id b))"
    by (simp add: usubst_lookup.rep_eq)
  then show ?thesis
    by (simp add: f1 uexpr_eq_iff)
qed

lemma usubst_lookup_upd :
  assumes "vwb_lens x"
  shows "\<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = v"   
proof -
  have "\<forall> b. get\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> (\<sigma> b) (\<lbrakk>v\<rbrakk>\<^sub>e b)) = \<lbrakk>v\<rbrakk>\<^sub>e b"
    by (simp add: assms)
  then have "\<forall>b. get\<^bsub>x\<^esub> ((\<sigma>(x \<mapsto>\<^sub>s v)) b) = \<lbrakk>v\<rbrakk>\<^sub>e b" 
    by (simp add: subst_upd_uvar_def)
  then have "\<forall>b. \<lbrakk>\<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x \<rbrakk>\<^sub>e b = \<lbrakk>v\<rbrakk>\<^sub>e b"
    by (simp add: usubst_lookup.rep_eq)
  then show ?thesis
    by (simp add: uexpr_eq_iff)
qed

lemma usubst_lookup_upd_pr_var :
  assumes "vwb_lens x"               
  shows "\<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>s (pr_var x) = v"      
  by (simp add: pr_var_def usubst_lookup_upd assms)
 
subsection \<open> Substitution update is idempotent. \<close>
lemma usubst_upd_idem :
  assumes "vwb_lens x"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, x \<mapsto>\<^sub>s v) = \<sigma>(x \<mapsto>\<^sub>s v)"
  by (simp add: assms subst_upd_uvar_def)

subsection \<open>just assignment \<close>
lemma usubst_upd_var_id :
  "vwb_lens x \<Longrightarrow> [x \<mapsto>\<^sub>s var x] = id"
  by (metis eq_id_iff subst_upd_uvar_def var.rep_eq vwb_lens.axioms(1) wb_lens.get_put)
  
lemma usubst_upd_pr_var_id :
  "vwb_lens x \<Longrightarrow> [x \<mapsto>\<^sub>s var (pr_var x)] = id"
  by (simp add: pr_var_def usubst_upd_var_id)

subsection \<open> Substitution updates commute when the lenses are independent. \<close> 
lemma usubst_upd_comm:
  assumes "x \<bowtie> y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v) = \<sigma>(y \<mapsto>\<^sub>s v, x \<mapsto>\<^sub>s u)"
  using assms
  by (rule_tac ext, auto simp add: subst_upd_uvar_def assms comp_def lens_indep_comm)

lemma usubst_upd_comm2:
  assumes "z \<bowtie> y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v, z \<mapsto>\<^sub>s s) = \<sigma>(x \<mapsto>\<^sub>s u, z \<mapsto>\<^sub>s s, y \<mapsto>\<^sub>s v)"
  using assms
  by (rule_tac ext, auto simp add: subst_upd_uvar_def assms comp_def lens_indep_comm)



subsection \<open> others \<close>
lemma subst_upd_lens_plus : 
  "subst_upd \<sigma> (x +\<^sub>L y) \<guillemotleft>(u,v)\<guillemotright> = \<sigma>(y \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>, x \<mapsto>\<^sub>s \<guillemotleft>u\<guillemotright>)"
  by (simp add: lens_defs zero_uexpr_def subst_upd_uvar_def, transfer, auto)

lemma usubst_lookup_upd_indep :
  assumes "mwb_lens x" "x \<bowtie> y"
  shows "\<langle>\<sigma>(y \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, simp)



























consts
  usedBy :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

syntax
  "_usedBy" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<natural>" 20)
translations
  "_usedBy x p" == "CONST usedBy x p"                                           
  "_usedBy (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_usedBy (x +\<^sub>L y) P"

lift_definition usedBy_uexpr :: "('b \<Longrightarrow> '\<alpha>) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> bool" 
is "\<lambda> x e. (\<forall> b b'. e (b' \<oplus>\<^sub>L b on x) = e b)" .
adhoc_overloading usedBy usedBy_uexpr



end