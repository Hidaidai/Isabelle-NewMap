theory nmap_var
imports "./Optics/Lenses"   "HOL-Library.Adhoc_Overloading"
begin

definition in_var :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('a \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "in_var x = x ;\<^sub>L fst\<^sub>L"

definition out_var :: "('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('a \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "out_var x = x ;\<^sub>L snd\<^sub>L"

abbreviation (input) univ_alpha :: "('\<alpha> \<Longrightarrow> '\<alpha>)" ("\<Sigma>") where
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
  "_sinvar"      :: "svid \<Rightarrow> svar" ("$_" [990] 990)
  "_soutvar"     :: "svid \<Rightarrow> svar" ("$_\<acute>" [990] 990)
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
  "_sinvar \<Sigma>"  \<leftharpoondown> "CONST ivar 1\<^sub>L"
  "_soutvar \<Sigma>" \<leftharpoondown> "CONST ovar 1\<^sub>L"
  "_spvar (_svid_dot x y)" \<leftharpoondown> "CONST svar (CONST lens_comp y x)"
  "_sinvar (_svid_dot x y)" \<leftharpoondown> "CONST ivar (CONST lens_comp y x)"
  "_soutvar (_svid_dot x y)" \<leftharpoondown> "CONST ovar (CONST lens_comp y x)"
  "_svid_dot (_svid_dot x y) z" \<leftharpoondown> "_svid_dot (CONST lens_comp y x) z"
  "_spvar x" \<rightleftharpoons> "CONST svar x"
  "_sinvar x" \<rightleftharpoons> "CONST ivar x"
  "_soutvar x" \<rightleftharpoons> "CONST ovar x"
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

syntax
  "_uvar_ty"  :: "type \<Rightarrow> type \<Rightarrow> type"









declare fst_vwb_lens [simp]
declare snd_vwb_lens [simp]
declare comp_vwb_lens [simp]
declare lens_indep_left_ext [simp]
declare lens_indep_right_ext [simp]

text \<open> We can now easily show that our UTP variable construction are various classes of 
  well-behaved lens .\<close>

lemma in_var_weak_lens [simp]:
  "weak_lens x \<Longrightarrow> weak_lens (in_var x)"
  by (simp add: comp_weak_lens in_var_def)

lemma in_var_semi_uvar [simp]:
  "mwb_lens x \<Longrightarrow> mwb_lens (in_var x)"
  by (simp add: comp_mwb_lens in_var_def)

lemma pr_var_weak_lens [simp]:
  "weak_lens x \<Longrightarrow> weak_lens (pr_var x)"
  by (simp add: pr_var_def)

lemma pr_var_mwb_lens [simp]:
  "mwb_lens x \<Longrightarrow> mwb_lens (pr_var x)"
  by (simp add: pr_var_def)
    
lemma pr_var_vwb_lens [simp]: 
  "vwb_lens x \<Longrightarrow> vwb_lens (pr_var x)"
  by (simp add: pr_var_def)
    
lemma in_var_uvar [simp]:
  "vwb_lens x \<Longrightarrow> vwb_lens (in_var x)"
  by (simp add: in_var_def)

lemma out_var_weak_lens [simp]:
  "weak_lens x \<Longrightarrow> weak_lens (out_var x)"
  by (simp add: comp_weak_lens out_var_def)

lemma out_var_semi_uvar [simp]:
  "mwb_lens x \<Longrightarrow> mwb_lens (out_var x)"
  by (simp add: comp_mwb_lens out_var_def)

lemma out_var_uvar [simp]:
  "vwb_lens x \<Longrightarrow> vwb_lens (out_var x)"
  by (simp add: out_var_def)
    
text \<open> Moreover, we can show that input and output variables are independent, since they refer
  to different sections of the alphabet. \<close>
    
lemma in_out_indep [simp]:
  "in_var x \<bowtie> out_var y"
  by (simp add: lens_indep_def in_var_def out_var_def fst_lens_def snd_lens_def lens_comp_def)

lemma out_in_indep [simp]:
  "out_var x \<bowtie> in_var y"
  by (simp add: lens_indep_def in_var_def out_var_def fst_lens_def snd_lens_def lens_comp_def)

lemma in_var_indep [simp]:
  "x \<bowtie> y \<Longrightarrow> in_var x \<bowtie> in_var y"
  by (simp add: in_var_def out_var_def)

lemma out_var_indep [simp]:
  "x \<bowtie> y \<Longrightarrow> out_var x \<bowtie> out_var y"
  by (simp add: out_var_def)

lemma pr_var_indeps [simp]: 
  "x \<bowtie> y \<Longrightarrow> pr_var x \<bowtie> y"
  "x \<bowtie> y \<Longrightarrow> x \<bowtie> pr_var y"
  by (simp_all add: pr_var_def)
    
lemma prod_lens_indep_in_var [simp]:
  "a \<bowtie> x \<Longrightarrow> a \<times>\<^sub>L b \<bowtie> in_var x"
  by (metis in_var_def in_var_indep out_in_indep out_var_def plus_pres_lens_indep prod_as_plus)

lemma prod_lens_indep_out_var [simp]:
  "b \<bowtie> x \<Longrightarrow> a \<times>\<^sub>L b \<bowtie> out_var x"
  by (metis in_out_indep in_var_def out_var_def out_var_indep plus_pres_lens_indep prod_as_plus)

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
    
lemma in_var_plus [simp]: "in_var (x +\<^sub>L y) = in_var x +\<^sub>L in_var y"
  by (simp add: in_var_def plus_lens_distr)

lemma out_var_plus [simp]: "out_var (x +\<^sub>L y) = out_var x +\<^sub>L out_var y"
  by (simp add: out_var_def plus_lens_distr)
  
text \<open> Similar properties follow for sublens \<close>
  
lemma in_var_sublens [simp]:
  "y \<subseteq>\<^sub>L x \<Longrightarrow> in_var y \<subseteq>\<^sub>L in_var x"
  by (metis (no_types, hide_lams) in_var_def lens_comp_assoc sublens_def)
     
lemma out_var_sublens [simp]:
  "y \<subseteq>\<^sub>L x \<Longrightarrow> out_var y \<subseteq>\<^sub>L out_var x"
  by (metis (no_types, hide_lams) out_var_def lens_comp_assoc sublens_def)

lemma pr_var_sublens [simp]:
  "y \<subseteq>\<^sub>L x \<Longrightarrow> pr_var y \<subseteq>\<^sub>L pr_var x"
  by (simp add: pr_var_def)

subsection \<open> Lens simplifications \<close>
    
text \<open> We also define some lookup abstraction simplifications. \<close>

lemma var_lookup_in [simp]: "lens_get (in_var x) (A, A') = lens_get x A"
  by (simp add: in_var_def fst_lens_def lens_comp_def)

lemma var_lookup_out [simp]: "lens_get (out_var x) (A, A') = lens_get x A'"
  by (simp add: out_var_def snd_lens_def lens_comp_def)

lemma var_update_in [simp]: "lens_put (in_var x) (A, A') v = (lens_put x A v, A')"
  by (simp add: in_var_def fst_lens_def lens_comp_def)

lemma var_update_out [simp]: "lens_put (out_var x) (A, A') v = (A, lens_put x A' v)"
  by (simp add: out_var_def snd_lens_def lens_comp_def)



end