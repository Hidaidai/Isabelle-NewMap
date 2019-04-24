theory nmap_expr
imports nmap_var
begin

subsection \<open> Expression type \<close>

no_notation BNF_Def.convol ("\<langle>(_,/ _)\<rangle>")

text \<open>the following make a new type called uexpr.then using lifting makes uexpr support var lit uop and bot\<close>

typedef ('t, '\<alpha>) uexpr = "UNIV :: ('\<alpha> \<Rightarrow> 't) set" ..

notation Rep_uexpr ("\<lbrakk>_\<rbrakk>\<^sub>e")

lemma uexpr_eq_iff: "e = f \<longleftrightarrow> (\<forall> b. \<lbrakk>e\<rbrakk>\<^sub>e b = \<lbrakk>f\<rbrakk>\<^sub>e b)"
  using Rep_uexpr_inject[of e f, THEN sym] by (auto)

setup_lifting type_definition_uexpr
named_theorems uexpr_defs and ueval and lit_simps and lit_norm

subsection \<open> Core expression constructs using lift_definition  \<close>

lift_definition var :: "('t \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t, '\<alpha>) uexpr" is lens_get .
                                                             
lift_definition lit :: "'t \<Rightarrow> ('t, '\<alpha>) uexpr" ("\<guillemotleft>_\<guillemotright>") is "\<lambda> v b. v" .

lift_definition uop :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr"
  is "\<lambda> f e b. f (e b)" .

lift_definition bop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr"
  is "\<lambda> f u v b. f (u b) (v b)" .







text \<open>???????????????\<close>

syntax
  "_uuvar" :: "svar \<Rightarrow> logic" ("_")

translations
  "_uuvar x" == "CONST var x"








subsection \<open> Type class instantiations \<close>
text \<open> Type class instantiations\<close>
  
instantiation uexpr :: (zero, type) zero
begin
  definition zero_uexpr_def [uexpr_defs]: "0 = lit 0"
instance ..
end

instantiation uexpr :: (one, type) one
begin
  definition one_uexpr_def [uexpr_defs]: "1 = lit 1"
instance ..
end

instantiation uexpr :: (uminus, type) uminus
begin
  definition uminus_uexpr_def [uexpr_defs]: "- u = uop uminus u"
instance ..
end

instantiation uexpr :: (plus, type) plus
begin
  definition plus_uexpr_def [uexpr_defs]: "u + v = bop (+) u v"
instance ..
end

instance uexpr :: (numeral, type) numeral
  by (intro_classes, simp add: plus_uexpr_def, transfer, simp add: add.assoc)

lemma lit_fun_simps [lit_simps]:
  "\<guillemotleft>f x\<guillemotright> = uop f \<guillemotleft>x\<guillemotright>"
  "\<guillemotleft>g x y\<guillemotright> = bop g \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright>"
  by (transfer, simp)+

lemma numeral_uexpr_rep_eq: "\<lbrakk>numeral x\<rbrakk>\<^sub>e b = numeral x"
  apply (induct x)
    apply (simp add: lit.rep_eq one_uexpr_def)
   apply (simp add: bop.rep_eq numeral_Bit0 plus_uexpr_def)
  apply (simp add: bop.rep_eq lit.rep_eq numeral_code(3) one_uexpr_def plus_uexpr_def)
  done

lemma numeral_uexpr_simp: "numeral x = \<guillemotleft>numeral x\<guillemotright>"
  by (simp add: uexpr_eq_iff numeral_uexpr_rep_eq lit.rep_eq)

lemma lit_zero [lit_simps]: "\<guillemotleft>0\<guillemotright> = 0" by (simp add:uexpr_defs)
lemma lit_one [lit_simps]: "\<guillemotleft>1\<guillemotright> = 1" by (simp add: uexpr_defs)
lemma lit_plus [lit_simps]: "\<guillemotleft>x + y\<guillemotright> = \<guillemotleft>x\<guillemotright> + \<guillemotleft>y\<guillemotright>" by (simp add: uexpr_defs, transfer, simp)
lemma lit_numeral [lit_simps]: "\<guillemotleft>numeral n\<guillemotright> = numeral n" by (simp add: numeral_uexpr_simp)








subsection \<open> Evaluation laws for expressions \<close>

lemma lit_ueval [ueval]: "\<lbrakk>\<guillemotleft>x\<guillemotright>\<rbrakk>\<^sub>eb = x"
  by (transfer, simp)
lemma var_ueval [ueval]: "\<lbrakk>var x\<rbrakk>\<^sub>eb = get\<^bsub>x\<^esub> b"
  by (transfer, simp)
lemma uop_ueval [ueval]: "\<lbrakk>uop f x\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb)"
  by (transfer, simp)
lemma bop_ueval [ueval]: "\<lbrakk>bop f x y\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb)"
  by (transfer, simp)
lemma uop_const [simp]: "uop id u = u"
  by (transfer, simp)
lemma bop_const_1 [simp]: "bop (\<lambda>x y. y) u v = v"
  by (transfer, simp)
lemma bop_const_2 [simp]: "bop (\<lambda>x y. x) u v = u"
  by (transfer, simp)

lemma lit_numeral_1: "uop numeral x = Abs_uexpr (\<lambda>b. numeral (\<lbrakk>x\<rbrakk>\<^sub>e b))"
  by (simp add: uop_def)

lemma lit_numeral_2: "Abs_uexpr (\<lambda> b. numeral v) = numeral v"
  by (metis lit.abs_eq lit_numeral)
  
method literalise = (unfold lit_simps[THEN sym])
method unliteralise = (unfold lit_simps uexpr_defs[THEN sym];
                     (unfold lit_numeral_1 ; (unfold uexpr_defs ueval); (unfold lit_numeral_2))?)+

method uexpr_simp uses simps = ((literalise)?, simp add: lit_norm simps, (unliteralise)?)

(* Example *)
lemma "((1::(int, '\<alpha>) uexpr) + \<guillemotleft>2\<guillemotright> = 4) = (\<guillemotleft>3\<guillemotright> = 4)"
  apply (literalise)
  apply (uexpr_simp) oops









subsection \<open> Substitution definitions \<close>

consts usubst :: "'s \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "\<dagger>" 80)

named_theorems usubst

type_synonym ('\<alpha>,'\<beta>) psubst = "'\<alpha> \<Rightarrow> '\<beta>"
type_synonym '\<alpha> usubst = "'\<alpha> \<Rightarrow> '\<alpha>"
  
lift_definition subst :: " '\<alpha> usubst \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" is
"\<lambda> \<sigma> e b. e (\<sigma> b)" .
                    
adhoc_overloading
  usubst subst

consts subst_upd :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> 'v \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<alpha>,'\<beta>) psubst"
  
definition subst_upd_uvar :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> ('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<alpha>,'\<beta>) psubst" where
"subst_upd_uvar \<sigma> x v = (\<lambda> b. put\<^bsub>x\<^esub> (\<sigma> b) (\<lbrakk>v\<rbrakk>\<^sub>eb))"

adhoc_overloading
  subst_upd subst_upd_uvar

lift_definition usubst_lookup :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> ('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<langle>_\<rangle>\<^sub>s")
is "\<lambda> \<sigma> x b. get\<^bsub>x\<^esub> (\<sigma> b)" .
  
definition unrest_usubst :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> usubst \<Rightarrow> bool"
where "unrest_usubst x \<sigma> = (\<forall> \<rho> v. \<sigma> (put\<^bsub>x\<^esub> \<rho> v) = put\<^bsub>x\<^esub> (\<sigma> \<rho>) v)"

adhoc_overloading
   unrest_usubst
  
definition par_subst :: "'\<alpha> usubst \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('b \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> usubst" where
"par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2 = (\<lambda> s. (s \<oplus>\<^sub>L (\<sigma>\<^sub>1 s) on A) \<oplus>\<^sub>L (\<sigma>\<^sub>2 s) on B)"

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

text \<open> Thus we can write things like @{term "\<sigma>(x \<mapsto>\<^sub>s v)"} to update a variable $x$ in $\sigma$ with
  expression $v$, @{term "[x \<mapsto>\<^sub>s e, y \<mapsto>\<^sub>s f]"} to construct a substitution with two variables,
  We can now express deletion of a substitution maplet. \<close>

definition subst_del :: "'\<alpha> usubst \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> usubst" (infix "-\<^sub>s" 85) where
"subst_del \<sigma> x = \<sigma>(x \<mapsto>\<^sub>s &x)"

subsection \<open> Substitution Application Laws \<close>

text \<open> We set up a simple substitution tactic that applies substitution and unrestriction laws \<close>

method subst_tac = (simp add: usubst )?

text \<open> Evaluation of a substitution expression involves application of the substitution to different
  variables. Thus we first prove laws for these cases. \<close>
  
lemma usubst_lookup_id [usubst]: "\<langle>id\<rangle>\<^sub>s x = var x"
  by (transfer, simp)

lemma subst_upd_id_lam [usubst]: "subst_upd (\<lambda> x. x) x v = subst_upd id x v"
  by (simp add: id_def)
    
text \<open> A substitution update naturally yields the given expression. \<close>
    
lemma usubst_lookup_upd [usubst]:
  assumes "weak_lens x"
  shows "\<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = v"
  using assms
  by (simp add: subst_upd_uvar_def, transfer) (simp)

lemma usubst_lookup_upd_pr_var [usubst]:
  assumes "weak_lens x"
  shows "\<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>s (pr_var x) = v"
  using assms
  by (simp add: subst_upd_uvar_def pr_var_def, transfer) (simp)
    
text \<open> Substitution update is idempotent. \<close>
    
lemma usubst_upd_idem [usubst]:
  assumes "mwb_lens x"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, x \<mapsto>\<^sub>s v) = \<sigma>(x \<mapsto>\<^sub>s v)"
  by (simp add: subst_upd_uvar_def assms comp_def)

text \<open> Substitution updates commute when the lenses are independent. \<close>
    
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

lemma subst_upd_pr_var: "s(&x \<mapsto>\<^sub>s v) = s(x \<mapsto>\<^sub>s v)"
  by (simp add: pr_var_def) 

text \<open> A substitution which swaps two independent variables is an injective function. \<close>
    
lemma swap_usubst_inj:
  fixes x y :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "vwb_lens x" "vwb_lens y" "x \<bowtie> y"
  shows "inj [x \<mapsto>\<^sub>s &y, y \<mapsto>\<^sub>s &x]"
proof (rule injI)
  fix b\<^sub>1 :: '\<alpha> and b\<^sub>2 :: '\<alpha>
  assume "[x \<mapsto>\<^sub>s &y, y \<mapsto>\<^sub>s &x] b\<^sub>1 = [x \<mapsto>\<^sub>s &y, y \<mapsto>\<^sub>s &x] b\<^sub>2"
  hence a: "put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> b\<^sub>1 (\<lbrakk>&y\<rbrakk>\<^sub>e b\<^sub>1)) (\<lbrakk>&x\<rbrakk>\<^sub>e b\<^sub>1) = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> b\<^sub>2 (\<lbrakk>&y\<rbrakk>\<^sub>e b\<^sub>2)) (\<lbrakk>&x\<rbrakk>\<^sub>e b\<^sub>2)"
    by (auto simp add: subst_upd_uvar_def)
  then have "(\<forall>a b c. put\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> a b) c = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> a c) b) \<and> 
             (\<forall>a b. get\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> a b) = get\<^bsub>x\<^esub> a) \<and> (\<forall>a b. get\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> a b) = get\<^bsub>y\<^esub> a)"
    by (simp add: assms(3) lens_indep.lens_put_irr2 lens_indep_comm)
  then show "b\<^sub>1 = b\<^sub>2"
    by (metis a assms(1) assms(2) pr_var_def var.rep_eq vwb_lens.source_determination vwb_lens_def wb_lens_def weak_lens.put_get)   
qed

lemma usubst_upd_var_id [usubst]:
  "vwb_lens x \<Longrightarrow> [x \<mapsto>\<^sub>s var x] = id"
  apply (simp add: subst_upd_uvar_def)
  apply (transfer)
  apply (rule ext)
  apply (auto)
  done

lemma usubst_upd_pr_var_id [usubst]:
  "vwb_lens x \<Longrightarrow> [x \<mapsto>\<^sub>s var (pr_var x)] = id"
  apply (simp add: subst_upd_uvar_def pr_var_def)
  apply (transfer)
  apply (rule ext)
  apply (auto)
  done
  


lemma subst_upd_lens_plus [usubst]: 
  "subst_upd \<sigma> (x +\<^sub>L y) \<guillemotleft>(u,v)\<guillemotright> = \<sigma>(y \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>, x \<mapsto>\<^sub>s \<guillemotleft>u\<guillemotright>)"
  by (simp add: lens_defs uexpr_defs subst_upd_uvar_def, transfer, auto)


    
lemma usubst_lookup_upd_indep [usubst]:
  assumes "mwb_lens x" "x \<bowtie> y"
  shows "\<langle>\<sigma>(y \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, simp)
   
text \<open> There follows various laws about deleting variables from a substitution. \<close>
    
lemma subst_del_id [usubst]:
  "vwb_lens x \<Longrightarrow> id -\<^sub>s x = id"
  by (simp add: subst_del_def subst_upd_uvar_def pr_var_def, transfer, auto)

lemma subst_del_upd_same [usubst]:
  "mwb_lens x \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) -\<^sub>s x = \<sigma> -\<^sub>s x"
  by (simp add: subst_del_def subst_upd_uvar_def)

lemma subst_del_upd_diff [usubst]:
  "x \<bowtie> y \<Longrightarrow> \<sigma>(y \<mapsto>\<^sub>s v) -\<^sub>s x = (\<sigma> -\<^sub>s x)(y \<mapsto>\<^sub>s v)"
  by (simp add: subst_del_def subst_upd_uvar_def lens_indep_comm)
































end