theory nmap_seq
imports
  nmap_assign
begin


consts
  unrest :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

syntax
  "_unrest" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<sharp>" 20)
  
translations
  "_unrest x p" == "CONST unrest x p"                                           
  "_unrest (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_unrest (x +\<^sub>L y) P"

text \<open> Our syntax translations support both variables and variable sets such that we can write down 
  predicates like @{term "&x \<sharp> P"} and also @{term "{&x,&y,&z} \<sharp> P"}. 

  We set up a simple tactic for discharging unrestriction conjectures using a simplification set. \<close>
  
named_theorems unrest
method unrest_tac = (simp add: unrest)?
  
lift_definition unrest_uexpr :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> bool"
is "\<lambda> x e. \<forall> b v. e (put\<^bsub>x\<^esub> b v) = e b" .

adhoc_overloading
  unrest unrest_uexpr

lemma unrest_expr_alt_def:
  "weak_lens x \<Longrightarrow> (x \<sharp> P) = (\<forall> b b'. \<lbrakk>P\<rbrakk>\<^sub>e (b \<oplus>\<^sub>L b' on x) = \<lbrakk>P\<rbrakk>\<^sub>e b)"
  by (transfer, metis lens_override_def weak_lens.put_get)
  
subsection \<open> Unrestriction laws \<close>
  

  
lemma unrest_var_comp [unrest]:
  "\<lbrakk> x \<sharp> P; y \<sharp> P \<rbrakk> \<Longrightarrow> x;y \<sharp> P"
  by (transfer, simp add: lens_defs)

lemma unrest_svar [unrest]: "(&x \<sharp> P) \<longleftrightarrow> (x \<sharp> P)"
  by (transfer, simp add: lens_defs)

text \<open> No lens is restricted by a literal, since it returns the same value for any state binding. \<close>
    
lemma unrest_lit [unrest]: "x \<sharp> \<guillemotleft>v\<guillemotright>"
  by (transfer, simp)

text \<open> If one lens is smaller than another, then any unrestriction on the larger lens implies
  unrestriction on the smaller. \<close>
    
lemma unrest_sublens:
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "y \<subseteq>\<^sub>L x"
  shows "y \<sharp> P" 
  using assms
  by (transfer, metis (no_types, lifting) lens.select_convs(2) lens_comp_def sublens_def)
    
text \<open> If two lenses are equivalent, and thus they characterise the same state-space regions,
  then clearly unrestrictions over them are equivalent. \<close>
    
lemma unrest_equiv:
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "mwb_lens y" "x \<approx>\<^sub>L y" "x \<sharp> P"
  shows "y \<sharp> P"
  by (metis assms lens_equiv_def sublens_pres_mwb sublens_put_put unrest_uexpr.rep_eq)

text \<open> If we can show that an expression is unrestricted on a bijective lens, then is unrestricted
  on the entire state-space. \<close>

lemma bij_lens_unrest_all:
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "bij_lens X" "X \<sharp> P"
  shows "\<Sigma> \<sharp> P"
  using assms bij_lens_equiv_id lens_equiv_def unrest_sublens by blast

lemma bij_lens_unrest_all_eq:
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "bij_lens X"
  shows "(\<Sigma> \<sharp> P) \<longleftrightarrow> (X \<sharp> P)"
  by (meson assms bij_lens_equiv_id lens_equiv_def unrest_sublens)

text \<open> If an expression is unrestricted by all variables, then it is unrestricted by any variable \<close>

lemma unrest_all_var:
  fixes e :: "('a, '\<alpha>) uexpr"
  assumes "\<Sigma> \<sharp> e"
  shows "x \<sharp> e"
  by (metis assms id_lens_def lens.simps(2) unrest_uexpr.rep_eq)

text \<open> We can split an unrestriction composed by lens plus \<close>

lemma unrest_plus_split:
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<bowtie> y" "vwb_lens x" "vwb_lens y"
  shows "unrest (x +\<^sub>L y) P \<longleftrightarrow> (x \<sharp> P) \<and> (y \<sharp> P)"
  using assms
  by (meson lens_plus_right_sublens lens_plus_ub sublens_refl unrest_sublens unrest_var_comp vwb_lens_wb)

lemma unrest_var [unrest]: "\<lbrakk> mwb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> y \<sharp> var x"
  by (transfer, auto)
    
text \<open> Unrestriction distributes through the various function lifting expression constructs;
  this allows us to prove unrestrictions for the majority of the expression language. \<close>
    
lemma unrest_uop [unrest]: "x \<sharp> e \<Longrightarrow> x \<sharp> uop f e"
  by (transfer, simp)

lemma unrest_bop [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> bop f u v"
  by (transfer, simp)



text \<open> For convenience, we also prove unrestriction rules for the bespoke operators on equality,
  numbers, arithmetic etc. \<close>

lemma unrest_zero [unrest]: "x \<sharp> 0"
  by (metis unrest_lit zero_uexpr_def)

lemma unrest_one [unrest]: "x \<sharp> 1"
  by (metis  one_uexpr_def unrest_lit)

lemma unrest_plus [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u + v"
  by (simp add: plus_uexpr_def unrest)

lemma unrest_case_prod [unrest]: "\<lbrakk> \<And> i j. x \<sharp> P i j \<rbrakk> \<Longrightarrow> x \<sharp> case_prod P v"
  by (simp add: prod.split_sel_asm)






text \<open> If a variable is unrestricted in an expression, then any substitution of that variable
  has no effect on the expression .\<close>
    
lemma subst_unrest : "x \<sharp> P \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) \<dagger> P = \<sigma> \<dagger> P"
  by (simp add: subst_upd_uvar_def, transfer, auto)

lemma subst_unrest_2 : 
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<bowtie> y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u,y \<mapsto>\<^sub>s v) \<dagger> P = \<sigma>(y \<mapsto>\<^sub>s v) \<dagger> P"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, auto, metis lens_indep.lens_put_comm)


































text \<open> The following two functions lift a predicate substitution to a relational one. \<close>

definition in\<alpha> :: "('\<alpha> \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "in\<alpha> = fst\<^sub>L"

definition out\<alpha> :: "('\<beta> \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "out\<alpha> = snd\<^sub>L"



lift_definition aext :: "('a, '\<beta>) uexpr \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> ('a, '\<alpha>) uexpr" (infixr "\<oplus>\<^sub>p" 95)
is "\<lambda> P x b. P (get\<^bsub>x\<^esub> b)" .



definition subst_ext :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> '\<beta> usubst" (infix "\<oplus>\<^sub>s" 65) where
 "\<sigma> \<oplus>\<^sub>s x = (\<lambda> s. put\<^bsub>x\<^esub> s (\<sigma> (get\<^bsub>x\<^esub> s)))"

lemma id_subst_ext :
  "wb_lens x \<Longrightarrow> id \<oplus>\<^sub>s x = id"
  by (simp add: id_def subst_ext_def)


lemma upd_subst_ext :
  "vwb_lens x \<Longrightarrow> \<sigma>(y \<mapsto>\<^sub>s v) \<oplus>\<^sub>s x = (\<sigma> \<oplus>\<^sub>s x)(&x:y \<mapsto>\<^sub>s v \<oplus>\<^sub>p x)"


lemma apply_subst_ext :
  "vwb_lens x \<Longrightarrow> (\<sigma> \<dagger> e) \<oplus>\<^sub>p x = (\<sigma> \<oplus>\<^sub>s x) \<dagger> (e \<oplus>\<^sub>p x)"
  by (pred_auto)

lemma aext_upred_eq :
  "((e =\<^sub>u f) \<oplus>\<^sub>p a) = ((e \<oplus>\<^sub>p a) =\<^sub>u (f \<oplus>\<^sub>p a))"
  by (pred_auto)

lemma subst_aext_comp :
  "vwb_lens a \<Longrightarrow> (\<sigma> \<oplus>\<^sub>s a) \<circ> (\<rho> \<oplus>\<^sub>s a) = (\<sigma> \<circ> \<rho>) \<oplus>\<^sub>s a"
  by pred_auto
    
subsection \<open> Substitution Alphabet Restriction \<close>

text \<open> This allows us to reduce the alphabet of a substitution, in a similar way to expressions. \<close>
  
definition subst_res :: "'\<alpha> usubst \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<beta> usubst" (infix "\<restriction>\<^sub>s" 65) where
[upred_defs]: "\<sigma> \<restriction>\<^sub>s x = (\<lambda> s. get\<^bsub>x\<^esub> (\<sigma> (create\<^bsub>x\<^esub> s)))"

lemma id_subst_res [usubst]:
  "mwb_lens x \<Longrightarrow> id \<restriction>\<^sub>s x = id"
  by pred_auto

lemma upd_subst_res [alpha]:
  "mwb_lens x \<Longrightarrow> \<sigma>(&x:y \<mapsto>\<^sub>s v) \<restriction>\<^sub>s x = (\<sigma> \<restriction>\<^sub>s x)(&y \<mapsto>\<^sub>s v \<restriction>\<^sub>e x)"
  by (pred_auto)

lemma subst_ext_res [usubst]:
  "mwb_lens x \<Longrightarrow> (\<sigma> \<oplus>\<^sub>s x) \<restriction>\<^sub>s x = \<sigma>"
  by (pred_auto)

lemma unrest_subst_alpha_ext [unrest]:
  "x \<bowtie> y \<Longrightarrow> x \<sharp> (P \<oplus>\<^sub>s y)"
  by (pred_simp robust, metis lens_indep_def)



abbreviation usubst_rel_lift :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<times> '\<beta>) usubst" ("\<lceil>_\<rceil>\<^sub>s") where
"\<lceil>\<sigma>\<rceil>\<^sub>s \<equiv> \<sigma> \<oplus>\<^sub>s in\<alpha>"



lemma assigns_subst :
  "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a"
 

lemma assigns_r_comp: "(\<langle>\<sigma>\<rangle>\<^sub>a ;; P) = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P)"
  by (rel_auto)
















subsection \<open> serial statement  \<close>

consts useq     :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 61)
lift_definition seqr::"('\<alpha>, '\<beta>) urel \<Rightarrow> ('\<beta>, '\<gamma>) urel \<Rightarrow>  (bool,'\<alpha> \<times> '\<gamma>) uexpr"
is "\<lambda> P Q b. b \<in> ({p. P p} O {q. Q q})" .
adhoc_overloading
  useq seqr


(***
locale serial = 
  fixes serial :: "'\<alpha> proc \<Rightarrow> '\<alpha> proc \<Rightarrow> '\<alpha> proc" (infixl ";;" 60)
  assumes serial_assoc : "(X ;; Y) ;; Z = X ;; (Y ;; Z)"
      and serial_skip_left : "II ;; X = X"
      and serial_skip_right : "X ;; II = X"

lemma  (in serial) assign_test1:
  assumes "vwb_lens x"
  shows "(x:=1  ;; II) = x := 1"
  using serial_skip_right by auto

***)






end