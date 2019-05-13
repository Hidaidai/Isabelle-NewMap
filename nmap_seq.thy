theory nmap_seq
imports
  nmap_assign
begin

consts
  unrest :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
lift_definition unrest_uexpr :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> bool"
is "\<lambda> x e. \<forall> b v. e (put\<^bsub>x\<^esub> b v) = e b" .
adhoc_overloading
  unrest unrest_uexpr
syntax
  "_unrest" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<sharp>" 20)
translations
  "_unrest x p" == "CONST unrest x p"                                           
  "_unrest (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_unrest (x +\<^sub>L y) P"

lemma unrest_var_comp:
  "\<lbrakk> x \<sharp> P; y \<sharp> P \<rbrakk> \<Longrightarrow> x;y \<sharp> P"
  by (transfer, simp add: lens_defs)

lemma unrest_svar: "(&x \<sharp> P) \<longleftrightarrow> (x \<sharp> P)"
  by (simp add: pr_var_def)

text \<open> No lens is restricted by a literal, since it returns the same value for any state binding. \<close>
lemma unrest_lit: "x \<sharp> \<guillemotleft>v\<guillemotright>"
  by (transfer, simp)

lemma unrest_var: "\<lbrakk> mwb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> y \<sharp> var x"
  by (transfer, auto)
  
lemma unrest_bop: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> bop f u v"
  by (transfer, simp)






definition unrest_usubst :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> usubst \<Rightarrow> bool"
where "unrest_usubst x \<sigma> = (\<forall> \<rho> v. \<sigma> (put\<^bsub>x\<^esub> \<rho> v) = put\<^bsub>x\<^esub> (\<sigma> \<rho>) v)"
adhoc_overloading
  unrest unrest_usubst

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

lemma subst_unrest_3 : 
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<bowtie> y" "x \<bowtie> z"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v, z \<mapsto>\<^sub>s w) \<dagger> P = \<sigma>(y \<mapsto>\<^sub>s v, z \<mapsto>\<^sub>s w) \<dagger> P"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, auto, metis (no_types, hide_lams) lens_indep_comm)

lemma subst_unrest_4 : 
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<bowtie> y" "x \<bowtie> z" "x \<bowtie> u"
  shows "\<sigma>(x \<mapsto>\<^sub>s e, y \<mapsto>\<^sub>s f, z \<mapsto>\<^sub>s g, u \<mapsto>\<^sub>s h) \<dagger> P = \<sigma>(y \<mapsto>\<^sub>s f, z \<mapsto>\<^sub>s g, u \<mapsto>\<^sub>s h) \<dagger> P"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, auto, metis (no_types, hide_lams) lens_indep_comm)

lemma subst_unrest_5 : 
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<bowtie> y" "x \<bowtie> z" "x \<bowtie> u" "x \<bowtie> v"
  shows "\<sigma>(x \<mapsto>\<^sub>s e, y \<mapsto>\<^sub>s f, z \<mapsto>\<^sub>s g, u \<mapsto>\<^sub>s h, v \<mapsto>\<^sub>s i) \<dagger> P = \<sigma>(y \<mapsto>\<^sub>s f, z \<mapsto>\<^sub>s g, u \<mapsto>\<^sub>s h, v \<mapsto>\<^sub>s i) \<dagger> P"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, auto, metis (no_types, hide_lams) lens_indep_comm)

lemma subst_compose_upd : "x \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<circ> \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> \<circ> \<rho>)(x \<mapsto>\<^sub>s v)"
  by (simp add: subst_upd_uvar_def, transfer, auto simp add: unrest_usubst_def)

lemma subst_subst : "\<sigma> \<dagger> \<rho> \<dagger> e = (\<rho> \<circ> \<sigma>) \<dagger> e"
  by (transfer, simp)

lemma subst_upd_comp : "\<rho>(x \<mapsto>\<^sub>s v) \<circ> \<sigma> = (\<rho> \<circ> \<sigma>)(x \<mapsto>\<^sub>s (\<sigma> \<dagger> v))"
  by (rule ext, simp add: subst_upd_uvar_def, transfer, simp)
















subsection \<open> serial statement  \<close>

definition skip_ra :: "('\<beta>, '\<alpha>) lens \<Rightarrow>'\<alpha> proc" where
"skip_ra v = ($v\<acute> =\<^sub>u $v)"

syntax
  \<comment> \<open> Alphabetised skip \<close>
  "_skip_ra"        :: "salpha \<Rightarrow> logic" ("II\<^bsub>_\<^esub>")
translations
  "_skip_ra v" \<rightleftharpoons> "CONST skip_ra v"





consts useq     :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 61)
lift_definition seqr::"(bool,'\<alpha> \<times> '\<beta>) uexpr  \<Rightarrow>  (bool,'\<beta> \<times> '\<gamma>) uexpr \<Rightarrow>  (bool,'\<alpha> \<times> '\<gamma>) uexpr"
is "\<lambda> P Q b. b \<in> ({p. P p} O {q. Q q})" .
adhoc_overloading
  useq seqr

lemma assigns_comp: "\<langle>f\<rangle>\<^sub>a ;; \<langle>g\<rangle>\<^sub>a = \<langle>g \<circ> f\<rangle>\<^sub>a" 
  by (transfer, simp add: relcomp_unfold)

lemma assigns_cobbmp: "P ;; (Q ;; R) = (P ;; Q) ;; R" 
  by (transfer,simp add: O_assoc)

lemma assigns_left: 
  assumes "P = \<langle>f\<rangle>\<^sub>a"
  shows "P ;;  II =  P"
  by (simp add: assigns_comp skip_r_def assms)

lemma assigns_right: 
  assumes "P = \<langle>f\<rangle>\<^sub>a"
  shows "II ;; P =  P"
  by (simp add: assigns_comp skip_r_def assms)

lemma assign_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x := e ;; y := f) = (y := f ;; x := e)"
  using assms
proof -
  have f1: "[y \<mapsto>\<^sub>s f] \<circ> [x \<mapsto>\<^sub>s e] = [x \<mapsto>\<^sub>s e, y \<mapsto>\<^sub>s [x \<mapsto>\<^sub>s e] \<dagger> f]"
    by (simp add:  subst_upd_comp)
  have f2: "[x \<mapsto>\<^sub>s e] = (id \<circ> id)(x \<mapsto>\<^sub>s id \<dagger> e)"
    by (metis comp_id subst_upd_comp)
  have f3: "([y \<mapsto>\<^sub>s f] \<circ> id) \<dagger> e = (id \<dagger> e)"
    by (simp add: assms(3)  subst_unrest)
  have "[y \<mapsto>\<^sub>s ([x \<mapsto>\<^sub>s e] \<circ> id) \<dagger> f] = [y \<mapsto>\<^sub>s f]"
    by (metis assms(2) comp_id  subst_unrest subst_upd_comp)
  then have "[y \<mapsto>\<^sub>s f] \<circ> [x \<mapsto>\<^sub>s e] = [x \<mapsto>\<^sub>s e] \<circ> [y \<mapsto>\<^sub>s f]"
    using f1 f2 f3 by (metis assms(1) assms(2) fun.map_id subst_unrest subst_upd_comp usubst_upd_comm)
  then show ?thesis
    by (simp add: assigns_comp pr_var_def)
qed




lemma fsdfas:
 assumes"vwb_lens x"
 shows " (\<lambda>b. \<lbrakk>&x + 2\<rbrakk>\<^sub>e ( put\<^bsub>x\<^esub> b (\<lbrakk>1\<rbrakk>\<^sub>e b)) ) =  (\<lambda>b. \<lbrakk>&x\<rbrakk>\<^sub>e  ( put\<^bsub>x\<^esub> b (\<lbrakk>1\<rbrakk>\<^sub>e b)) +  \<lbrakk>2\<rbrakk>\<^sub>e ( put\<^bsub>x\<^esub> b (\<lbrakk>1\<rbrakk>\<^sub>e b)) ) "
  by (simp add: plus_ueval )

lemma plus_ueval : "\<lbrakk>x + y\<rbrakk>\<^sub>eb = (\<lbrakk>x\<rbrakk>\<^sub>eb) + (\<lbrakk>y\<rbrakk>\<^sub>eb)"
  by (simp add: bop_ueval plus_uexpr_def)







lemma hello_test1:
  assumes"vwb_lens x"
  shows " [x \<mapsto>\<^sub>s 1] \<dagger> (&x + 2) = 3"
proof -
  have f1: " \<lbrakk> [x \<mapsto>\<^sub>s 1] \<dagger> (&x + 2)\<rbrakk>\<^sub>e =  (\<lambda>b. \<lbrakk>&x + 2\<rbrakk>\<^sub>e ( [x \<mapsto>\<^sub>s 1] b)) "
    by (simp add: subst.rep_eq)
  then have " (\<lambda>b. \<lbrakk>&x + 2\<rbrakk>\<^sub>e ( [x \<mapsto>\<^sub>s 1] b)) =  (\<lambda>b. \<lbrakk>&x + 2\<rbrakk>\<^sub>e ( put\<^bsub>x\<^esub> b (\<lbrakk>1\<rbrakk>\<^sub>e b)) )"
    by (simp add: subst_upd_uvar_def)
  then have " (\<lambda>b. \<lbrakk>&x + 2\<rbrakk>\<^sub>e ( [x \<mapsto>\<^sub>s 1] b)) =  (\<lambda>b. \<lbrakk>var x\<rbrakk>\<^sub>e  ( put\<^bsub>x\<^esub> b (\<lbrakk>1\<rbrakk>\<^sub>e b)) +  \<lbrakk>2\<rbrakk>\<^sub>e ( put\<^bsub>x\<^esub> b (\<lbrakk>1\<rbrakk>\<^sub>e b)) ) "
    by (simp add: plus_ueval pr_var_def)
  then have " (\<lambda>b. \<lbrakk>&x + 2\<rbrakk>\<^sub>e ( [x \<mapsto>\<^sub>s 1] b)) =  (\<lambda>b. get\<^bsub>x\<^esub> ( put\<^bsub>x\<^esub> b (\<lbrakk>1\<rbrakk>\<^sub>e b)) +  \<lbrakk>2\<rbrakk>\<^sub>e ( put\<^bsub>x\<^esub> b (\<lbrakk>1\<rbrakk>\<^sub>e b)) ) "
    by (simp add: var.rep_eq)
  then have " (\<lambda>b. \<lbrakk>&x + 2\<rbrakk>\<^sub>e ( [x \<mapsto>\<^sub>s 1] b)) =  (\<lambda>b. \<lbrakk>1\<rbrakk>\<^sub>e b +  \<lbrakk>2\<rbrakk>\<^sub>e b ) "
    by (simp add: assms numeral_uexpr_rep_eq)
  then have " \<lbrakk> [x \<mapsto>\<^sub>s 1] \<dagger> (&x + 2)\<rbrakk>\<^sub>e =  \<lbrakk>3\<rbrakk>\<^sub>e  "
    by (metis (no_types, hide_lams) f1 numeral_One numeral_uexpr_rep_eq one_plus_numeral semiring_norm(3) uexpr_eq_iff)
  then show ?thesis
    by (simp add: Rep_uexpr_inject)
qed

theorem hello_test: 
  assumes"vwb_lens x"
  shows "(x := 1 ;; x := &x + 2) = (x := 3 )"
proof -
  have f1: "[x \<mapsto>\<^sub>s &x + 2] \<circ> [x \<mapsto>\<^sub>s 1] = [x \<mapsto>\<^sub>s 1, x \<mapsto>\<^sub>s [x \<mapsto>\<^sub>s 1] \<dagger> (&x + 2)]"
    by (simp add: subst_upd_comp)
  have f2: " [x \<mapsto>\<^sub>s 1] \<dagger> (&x + 2) = 3"
    by (simp add: assms hello_test1)
  have "(x := 1 ;; x := &x + 2) = \<langle> [x \<mapsto>\<^sub>s &x + 2] \<circ> [x \<mapsto>\<^sub>s 1] \<rangle>\<^sub>a"
    by (simp add: assigns_comp pr_var_def)
  then have "(x := 1 ;; x := &x + 2) =  \<langle> [x \<mapsto>\<^sub>s 3] \<rangle>\<^sub>a"
    using f1 f2    by (simp add: assms usubst_upd_idem)
  then show ?thesis
    by (simp add: pr_var_def)
qed











lemma hello_thdhest1:
  assumes"vwb_lens x"
  shows " [x \<mapsto>\<^sub>s numeral a] \<dagger> (&x + numeral c) = numeral a + numeral c"
proof -
  have f1: " \<lbrakk> [x \<mapsto>\<^sub>s numeral a] \<dagger> (&x + numeral c)\<rbrakk>\<^sub>e =   (\<lambda>b. \<lbrakk>&x + numeral c\<rbrakk>\<^sub>e ( put\<^bsub>x\<^esub> b (\<lbrakk>numeral a\<rbrakk>\<^sub>e b))) "
    by (simp add: subst.rep_eq subst_upd_uvar_def)
  then have "(\<lambda>b. \<lbrakk>&x + numeral c\<rbrakk>\<^sub>e ( put\<^bsub>x\<^esub> b (\<lbrakk>numeral a\<rbrakk>\<^sub>e b))) =  (\<lambda>b. \<lbrakk>numeral a\<rbrakk>\<^sub>e b +  \<lbrakk>numeral c\<rbrakk>\<^sub>e b ) "
    by (simp add: assms numeral_uexpr_rep_eq var.rep_eq plus_ueval pr_var_def)
  then have " \<lbrakk> [x \<mapsto>\<^sub>s numeral a] \<dagger> (&x + numeral c)\<rbrakk>\<^sub>e =  \<lbrakk>numeral a + numeral c\<rbrakk>\<^sub>e  "
    by (metis (no_types, hide_lams) f1 numeral_plus_numeral numeral_uexpr_rep_eq uexpr_eq_iff)
  then show ?thesis
    by (simp add: Rep_uexpr_inject)
qed

theorem hellerqweqweo_test: 
  assumes"vwb_lens x"
  shows "(x := numeral a ;; x := &x +  numeral c) = (x :=  numeral a + numeral c )"
proof -
  have f1: "[x \<mapsto>\<^sub>s &x +  numeral c] \<circ> [x \<mapsto>\<^sub>s numeral a] = [x \<mapsto>\<^sub>s numeral a, x \<mapsto>\<^sub>s [x \<mapsto>\<^sub>s numeral a] \<dagger> (&x +  numeral c)]"
    by (simp add: subst_upd_comp)
  have f2: "[x \<mapsto>\<^sub>s numeral a] \<dagger> (&x + numeral c) = numeral a + numeral c"
    by (simp add: assms hello_thdhest1)
  have "(x := numeral a ;; x := &x +  numeral c) = \<langle> [x \<mapsto>\<^sub>s &x +  numeral c] \<circ> [x \<mapsto>\<^sub>s numeral a] \<rangle>\<^sub>a"
    by (simp add: assigns_comp pr_var_def)
  then have "(x := numeral a ;; x := &x +  numeral c) =  \<langle> [x \<mapsto>\<^sub>s  numeral a + numeral c] \<rangle>\<^sub>a"
    using f1 f2    by (simp add: assms usubst_upd_idem)
  then show ?thesis
    by (simp add: pr_var_def)
qed





(**
lemma assign_commute:
  assumes "x \<bowtie> y"  "y \<sharp> e"
  shows "(x := e ;; y := &x) = (x := e ;; f := e)"
 





lemma assign_test: "mwb_lens x \<Longrightarrow> (x := \<guillemotleft>u\<guillemotright> ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright>)"


lemma assign_twice: "\<lbrakk> mwb_lens x; x \<sharp> f \<rbrakk> \<Longrightarrow> (x := e ;; x := f) = (x := f)"



















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