theory nmap_var 
imports "./Optics/Lenses"   "HOL-Library.Adhoc_Overloading"
begin

definition var :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('a \<Longrightarrow> '\<alpha>)" where
[lens_defs]: "var x = x"    

definition univ_alpha :: "('\<alpha> \<Longrightarrow> '\<alpha>)" ("\<Sigma>") where
"univ_alpha \<equiv> 1\<^sub>L"

definition pr_var :: "('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('a \<Longrightarrow> '\<beta>)" where
[lens_defs]: "pr_var x = x"

(*** some proofs about lemmas have put in the last of this theory  ***)

nonterminal svid and svids and svar and svars and salpha

syntax \<comment> \<open> Identifiers \<close>
  "_svid"        :: "id \<Rightarrow> svid" ("_" [999] 999)
  "_svid_unit"   :: "svid \<Rightarrow> svids" ("_")
  "_svid_list"   :: "svid \<Rightarrow> svids \<Rightarrow> svids" ("_,/ _")
  "_svid_alpha"  :: "svid" ("\<^bold>v")
  "_svid_dot"    :: "svid \<Rightarrow> svid \<Rightarrow> svid" ("_:_" [998,999] 998)

consts
  svar :: "'v \<Rightarrow> 'e"
  ivar :: "'v \<Rightarrow> 'e"
  ovar :: "'v \<Rightarrow> 'e"

syntax 
\<comment> \<open> Decorations \<close>
  "_spvar"       :: "svid \<Rightarrow> svar" ("&_" [990] 990)
 \<comment> \<open> Variable sets \<close>
  "_salphaid"    :: "svid \<Rightarrow> salpha" ("_" [990] 990)
  "_salphavar"   :: "svar \<Rightarrow> salpha" ("_" [990] 990)
  "_salphaparen" :: "salpha \<Rightarrow> salpha" ("'(_')")
  "_salphacomp"  :: "salpha \<Rightarrow> salpha \<Rightarrow> salpha" (infixr ";" 75)
  "_salphaprod"  :: "salpha \<Rightarrow> salpha \<Rightarrow> salpha" (infixr "\<times>" 85)
  "_salpha_all"  :: "salpha" ("\<Sigma>")
  "_salpha_none" :: "salpha" ("\<emptyset>")
  "_svar_nil"    :: "svar \<Rightarrow> svars" ("_")
  "_svar_cons"   :: "svar \<Rightarrow> svars \<Rightarrow> svars" ("_,/ _")
  "_salphaset"   :: "svars \<Rightarrow> salpha" ("{_}")
  "_salphamk"    :: "logic \<Rightarrow> salpha"
 \<comment> \<open> Quotations \<close>
  "_ualpha_set"  :: "svars \<Rightarrow> logic" ("{_}\<^sub>\<alpha>")  
  "_svar"        :: "svar \<Rightarrow> logic" ("'(_')\<^sub>v")

translations
\<comment> \<open> Identifiers \<close>
  "_svid x" \<rightharpoonup> "x"
  "_svid_alpha" \<rightleftharpoons> "\<Sigma>"
  "_svid_dot x y" \<rightharpoonup> "y ;\<^sub>L x"
\<comment> \<open> Decorations \<close>
  "_spvar \<Sigma>"  \<leftharpoondown>  "CONST svar CONST id_lens"
  "_spvar (_svid_dot x y)" \<leftharpoondown> "CONST svar (CONST lens_comp y x)"
  "_svid_dot (_svid_dot x y) z" \<leftharpoondown> "_svid_dot (CONST lens_comp y x) z"
  "_spvar x" \<rightleftharpoons> "CONST svar x"
\<comment> \<open> Alphabets \<close>
  "_salphaparen a" \<rightharpoonup> "a"
  "_salphaid x" \<rightharpoonup> "x"
  "_salphacomp x y" \<rightharpoonup> "x +\<^sub>L y"
  "_salphaprod a b" \<rightleftharpoons> "a \<times>\<^sub>L b"
  "_salphavar x" \<rightharpoonup> "x"
  "_svar_nil x" \<rightharpoonup> "x"
  "_svar_cons x xs" \<rightharpoonup> "x +\<^sub>L xs"
  "_salphaset A" \<rightharpoonup> "A"  
  "(_svar_cons x (_salphamk y))" \<leftharpoondown> "_salphamk (x +\<^sub>L y)" 
  "x" \<leftharpoondown> "_salphamk x"
  "_salpha_all" \<rightleftharpoons> "1\<^sub>L"
  "_salpha_none" \<rightleftharpoons> "0\<^sub>L"
\<comment> \<open> Quotations \<close>
  "_ualpha_set A" \<rightharpoonup> "A"
  "_svar x" \<rightharpoonup> "x"

adhoc_overloading
  svar pr_var and ivar in_var and ovar out_var











declare fst_vwb_lens [simp]
declare snd_vwb_lens [simp]
declare comp_vwb_lens [simp]
declare lens_indep_left_ext [simp]
declare lens_indep_right_ext [simp]

text \<open> We can now easily show that our UTP variable construction are various classes of  well-behaved lens .\<close>

lemma var_uvar [simp]:
  "vwb_lens x \<Longrightarrow> vwb_lens (var x)"
  by (simp add: var_def)

lemma pr_var_vwb_lens [simp]: 
  "vwb_lens x \<Longrightarrow> vwb_lens (pr_var x)"
  by (simp add: pr_var_def)
    
lemma in_var_indep [simp]:
  "x \<bowtie> y \<Longrightarrow> var x \<bowtie> var y"
  by (simp add: var_def)

lemma pr_var_indeps [simp]: 
  "x \<bowtie> y \<Longrightarrow> pr_var x \<bowtie> y"
  "x \<bowtie> y \<Longrightarrow> x \<bowtie> pr_var y"
  by (simp_all add: pr_var_def)
    
lemma in_var_pr_var [simp]:
  "in_var (pr_var x) = in_var x"
  by (simp add: pr_var_def)

lemma out_var_pr_var [simp]:
  "out_var (pr_var x) = out_var x"
  by (simp add: pr_var_def)

lemma pr_var_idem [simp]: 
  "pr_var (pr_var x) = pr_var x"
  by (simp add: pr_var_def)
    
lemma pr_var_lens_plus [simp]: 
  "pr_var (x +\<^sub>L y) = (x +\<^sub>L y)"
  by (simp add: pr_var_def)
    
lemma pr_var_lens_comp_1 [simp]: 
  "pr_var x ;\<^sub>L y = pr_var (x ;\<^sub>L y)"
  by (simp add: pr_var_def)
    
lemma var_plus [simp]: "var (x +\<^sub>L y) = var x +\<^sub>L var y"
  by (simp add: var_def plus_lens_distr)







end