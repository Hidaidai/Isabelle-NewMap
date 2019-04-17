theory nmap_expr
imports nmap_var
begin

subsection \<open> Expression type \<close>

no_notation BNF_Def.convol ("\<langle>(_,/ _)\<rangle>")

typedef ('t, '\<alpha>) uexpr = "UNIV :: ('\<alpha> \<Rightarrow> 't) set" ..


notation Rep_uexpr ("\<lbrakk>_\<rbrakk>\<^sub>e")

lemma uexpr_eq_iff:
  "e = f \<longleftrightarrow> (\<forall> b. \<lbrakk>e\<rbrakk>\<^sub>e b = \<lbrakk>f\<rbrakk>\<^sub>e b)"
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

lift_definition trop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr \<Rightarrow> ('d, '\<alpha>) uexpr"
  is "\<lambda> f u v w b. f (u b) (v b) (w b)" .

lift_definition ulambda :: "('a \<Rightarrow> ('b, '\<alpha>) uexpr) \<Rightarrow> ('a \<Rightarrow> 'b, '\<alpha>) uexpr"
is "\<lambda> f A x. f x A" .



definition uIf :: "bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
[uexpr_defs]: "uIf = If"

abbreviation cond ::
  "('a,'\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr \<Rightarrow> ('a,'\<alpha>) uexpr \<Rightarrow> ('a,'\<alpha>) uexpr"
  ("(3_ \<triangleleft> _ \<triangleright>/ _)" [52,0,53] 52)
  where "P \<triangleleft> b \<triangleright> Q \<equiv> trop uIf b P Q"

definition eq_upred :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infixl "=\<^sub>u" 50)
where [uexpr_defs]: "eq_upred x y = bop HOL.eq x y"

syntax
  "_uuvar" :: "svar \<Rightarrow> logic" ("_")

translations
  "_uuvar x" == "CONST var x"








subsection \<open> Type class instantiations \<close>

  
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

instantiation uexpr :: (minus, type) minus
begin
  definition minus_uexpr_def [uexpr_defs]: "u - v = bop (-) u v"
instance ..
end

instantiation uexpr :: (times, type) times
begin
  definition times_uexpr_def [uexpr_defs]: "u * v = bop times u v"
instance ..
end

instantiation uexpr :: (divide, type) divide
begin
  definition divide_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr" where
  [uexpr_defs]: "divide_uexpr u v = bop divide u v"
instance ..
end

instantiation uexpr :: (inverse, type) inverse
begin
  definition inverse_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr"
  where [uexpr_defs]: "inverse_uexpr u = uop inverse u"
instance ..
end

instantiation uexpr :: (modulo, type) modulo
begin
  definition mod_uexpr_def [uexpr_defs]: "u mod v = bop (mod) u v"
instance ..
end






instance uexpr :: (Rings.dvd, type) Rings.dvd ..

instance uexpr :: (semigroup_add, type) semigroup_add
  by (intro_classes) (simp add: plus_uexpr_def zero_uexpr_def, transfer, simp add: add.assoc)+

instance uexpr :: (numeral, type) numeral
  by (intro_classes, simp add: plus_uexpr_def, transfer, simp add: add.assoc)

instance uexpr :: (semigroup_mult, type) semigroup_mult
  by (intro_classes) (simp add: times_uexpr_def one_uexpr_def, transfer, simp add: mult.assoc)+

instance uexpr :: (monoid_mult, type) monoid_mult
  by (intro_classes) (simp add: times_uexpr_def one_uexpr_def, transfer, simp)+

instance uexpr :: (monoid_add, type) monoid_add
  by (intro_classes) (simp add: plus_uexpr_def zero_uexpr_def, transfer, simp)+

instance uexpr :: (ab_semigroup_add, type) ab_semigroup_add
  by (intro_classes) (simp add: plus_uexpr_def, transfer, simp add: add.commute)+

instance uexpr :: (cancel_semigroup_add, type) cancel_semigroup_add
  by (intro_classes) (simp add: plus_uexpr_def, transfer, simp add: fun_eq_iff)+

instance uexpr :: (cancel_ab_semigroup_add, type) cancel_ab_semigroup_add
  by (intro_classes, (simp add: plus_uexpr_def minus_uexpr_def, transfer, simp add: fun_eq_iff add.commute cancel_ab_semigroup_add_class.diff_diff_add)+)

instance uexpr :: (group_add, type) group_add
  by (intro_classes)
     (simp add: plus_uexpr_def uminus_uexpr_def minus_uexpr_def zero_uexpr_def, transfer, simp)+

instance uexpr :: (ab_group_add, type) ab_group_add
  by (intro_classes)
     (simp add: plus_uexpr_def uminus_uexpr_def minus_uexpr_def zero_uexpr_def, transfer, simp)+

instance uexpr :: (semiring, type) semiring
  by (intro_classes) (simp add: plus_uexpr_def times_uexpr_def, transfer, simp add: fun_eq_iff add.commute semiring_class.distrib_right semiring_class.distrib_left)+

instance uexpr :: (ring_1, type) ring_1
  by (intro_classes) (simp add: plus_uexpr_def uminus_uexpr_def minus_uexpr_def times_uexpr_def zero_uexpr_def one_uexpr_def, transfer, simp add: fun_eq_iff)+






lemma power_rep_eq: "\<lbrakk>P ^ n\<rbrakk>\<^sub>e = (\<lambda> b. \<lbrakk>P\<rbrakk>\<^sub>e b ^ n)"
  by (induct n, simp_all add: lit.rep_eq one_uexpr_def bop.rep_eq times_uexpr_def)

lemma lit_uminus [lit_simps]: "\<guillemotleft>- x\<guillemotright> = - \<guillemotleft>x\<guillemotright>" by (simp add: uexpr_defs, transfer, simp)
lemma lit_minus [lit_simps]: "\<guillemotleft>x - y\<guillemotright> = \<guillemotleft>x\<guillemotright> - \<guillemotleft>y\<guillemotright>" by (simp add: uexpr_defs, transfer, simp)
lemma lit_times [lit_simps]: "\<guillemotleft>x * y\<guillemotright> = \<guillemotleft>x\<guillemotright> * \<guillemotleft>y\<guillemotright>" by (simp add: uexpr_defs, transfer, simp)
lemma lit_divide [lit_simps]: "\<guillemotleft>x / y\<guillemotright> = \<guillemotleft>x\<guillemotright> / \<guillemotleft>y\<guillemotright>" by (simp add: uexpr_defs, transfer, simp)
lemma lit_div [lit_simps]: "\<guillemotleft>x div y\<guillemotright> = \<guillemotleft>x\<guillemotright> div \<guillemotleft>y\<guillemotright>" by (simp add: uexpr_defs, transfer, simp)
lemma lit_power [lit_simps]: "\<guillemotleft>x ^ n\<guillemotright> = \<guillemotleft>x\<guillemotright> ^ n" by (simp add: lit.rep_eq power_rep_eq uexpr_eq_iff)


                                                              

subsection \<open> Syntax translations \<close>


abbreviation (input) "ulens_override x f g \<equiv> lens_override f g x"

definition set_of :: "'a itself \<Rightarrow> 'a set" where
[uexpr_defs]: "set_of t = UNIV"

nonterminal utuple_args and umaplet and umaplets

syntax \<comment> \<open> Core expression constructs \<close>
  "_ucoerce"    :: "logic \<Rightarrow> type \<Rightarrow> logic" (infix ":\<^sub>u" 50)
  "_ulambda"    :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<lambda> _ \<bullet> _" [0, 10] 10)
  "_ulens_ovrd" :: "logic \<Rightarrow> logic \<Rightarrow> salpha \<Rightarrow> logic" ("_ \<oplus> _ on _" [85, 0, 86] 86)
  "_ulens_get"  :: "logic \<Rightarrow> svar \<Rightarrow> logic" ("_:_" [900,901] 901)
  "_umem"       :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<in>\<^sub>u" 50)

translations
  "\<lambda> x \<bullet> p" == "CONST ulambda (\<lambda> x. p)"
  "x :\<^sub>u 'a" == "x :: ('a, _) uexpr"
  "_ulens_ovrd f g a" => "CONST bop (CONST ulens_override a) f g"
  "_ulens_ovrd f g a" <= "CONST bop (\<lambda>x y. CONST lens_override x1 y1 a) f g"
  "_ulens_get x y" == "CONST uop (CONST lens_get y) x"
  "x \<in>\<^sub>u A" == "CONST bop (\<in>) x A"

syntax \<comment> \<open> Tuples \<close>
  "_utuple"     :: "('a, '\<alpha>) uexpr \<Rightarrow> utuple_args \<Rightarrow> ('a * 'b, '\<alpha>) uexpr" ("(1'(_,/ _')\<^sub>u)")
  "_utuple_arg"  :: "('a, '\<alpha>) uexpr \<Rightarrow> utuple_args" ("_")
  "_utuple_args" :: "('a, '\<alpha>) uexpr => utuple_args \<Rightarrow> utuple_args"     ("_,/ _")
  "_uunit"      :: "('a, '\<alpha>) uexpr" ("'(')\<^sub>u")
  "_ufst"       :: "('a \<times> 'b, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<pi>\<^sub>1'(_')")
  "_usnd"       :: "('a \<times> 'b, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr" ("\<pi>\<^sub>2'(_')")

translations
  "()\<^sub>u"      == "\<guillemotleft>()\<guillemotright>"
  "(x, y)\<^sub>u"  == "CONST bop (CONST Pair) x y"
  "_utuple x (_utuple_args y z)" == "_utuple x (_utuple_arg (_utuple y z))"
  "\<pi>\<^sub>1(x)"    == "CONST uop CONST fst x"
  "\<pi>\<^sub>2(x)"    == "CONST uop CONST snd x"







subsection \<open> Evaluation laws for expressions \<close>




lemma lit_ueval [ueval]: "\<lbrakk>\<guillemotleft>x\<guillemotright>\<rbrakk>\<^sub>eb = x"
  by (transfer, simp)
lemma var_ueval [ueval]: "\<lbrakk>var x\<rbrakk>\<^sub>eb = get\<^bsub>x\<^esub> b"
  by (transfer, simp)
lemma uop_ueval [ueval]: "\<lbrakk>uop f x\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb)"
  by (transfer, simp)
lemma bop_ueval [ueval]: "\<lbrakk>bop f x y\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb)"
  by (transfer, simp)
lemma trop_ueval [ueval]: "\<lbrakk>trop f x y z\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) (\<lbrakk>z\<rbrakk>\<^sub>eb)"
  by (transfer, simp)

lemma uop_const [simp]: "uop id u = u"
  by (transfer, simp)
lemma bop_const_1 [simp]: "bop (\<lambda>x y. y) u v = v"
  by (transfer, simp)
lemma bop_const_2 [simp]: "bop (\<lambda>x y. x) u v = u"
  by (transfer, simp)






lemma lit_fun_simps [lit_simps]:
  "\<guillemotleft>h x y z\<guillemotright> = trop h \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright> \<guillemotleft>z\<guillemotright>"
  "\<guillemotleft>g x y\<guillemotright> = bop g \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright>"
  "\<guillemotleft>f x\<guillemotright> = uop f \<guillemotleft>x\<guillemotright>"
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















subsection \<open> Syntax translations about functions \<close>

(***  utp-expr-funcs.thy    ***)



syntax \<comment> \<open> Polymorphic constructs \<close>
  "_uceil"      :: "logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>u")
  "_ufloor"     :: "logic \<Rightarrow> logic" ("\<lfloor>_\<rfloor>\<^sub>u")
  "_umin"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("min\<^sub>u'(_, _')")
  "_umax"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("max\<^sub>u'(_, _')")
  "_ugcd"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("gcd\<^sub>u'(_, _')")

translations
  \<comment> \<open> Type-class polymorphic constructs \<close>
  "min\<^sub>u(x, y)"  == "CONST bop (CONST min) x y"
  "max\<^sub>u(x, y)"  == "CONST bop (CONST max) x y"
  "gcd\<^sub>u(x, y)"  == "CONST bop (CONST gcd) x y"
  "\<lceil>x\<rceil>\<^sub>u" == "CONST uop CONST ceiling x"
  "\<lfloor>x\<rfloor>\<^sub>u" == "CONST uop CONST floor x"

syntax \<comment> \<open> Lists / Sequences \<close>
  "_ucons"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr "#\<^sub>u" 65)
  "_unil"       :: "('a list, '\<alpha>) uexpr" ("\<langle>\<rangle>")
  "_ulist"      :: "args => ('a list, '\<alpha>) uexpr"    ("\<langle>(_)\<rangle>")
  "_uappend"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixr "^\<^sub>u" 80)
  "_udconcat"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr "\<^sup>\<frown>\<^sub>u" 90)
  "_ulast"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("last\<^sub>u'(_')")
  "_ufront"     :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" ("front\<^sub>u'(_')")
  "_uhead"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("head\<^sub>u'(_')")
  "_utail"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" ("tail\<^sub>u'(_')")
  "_utake"      :: "(nat, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" ("take\<^sub>u'(_,/ _')")
  "_udrop"      :: "(nat, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" ("drop\<^sub>u'(_,/ _')")
  "_ufilter"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixl "\<restriction>\<^sub>u" 75)
  "_uextract"   :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixl "\<upharpoonleft>\<^sub>u" 75)
  "_uelems"     :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" ("elems\<^sub>u'(_')")
  "_usorted"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" ("sorted\<^sub>u'(_')")
  "_udistinct"  :: "('a list, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" ("distinct\<^sub>u'(_')")
  "_uupto"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_.._\<rangle>")
  "_uupt"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_..<_\<rangle>")
  "_umap"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("map\<^sub>u")
  "_uzip"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("zip\<^sub>u")

subsection \<open> Distributed Concatenation \<close>

definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow>  'c) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c)" where
[simp]: "uncurry f = (\<lambda>(x, y). f x y)"

definition dist_concat ::
  "'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list set" (infixr "\<^sup>\<frown>" 100) where
"dist_concat ls1 ls2 = (uncurry (@) ` (ls1 \<times> ls2))"

subsection \<open> Filtering a list according to a set \<close>

definition seq_filter :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a list" (infix "\<restriction>\<^sub>l" 80) where
"seq_filter xs A = filter (\<lambda> x. x \<in> A) xs"

subsection \<open> Extracting List Elements \<close>

definition seq_extract :: "nat set \<Rightarrow> 'a list \<Rightarrow> 'a list" (infix "\<upharpoonleft>\<^sub>l" 80) where
"seq_extract A xs = nths xs A"

translations
  "x #\<^sub>u ys" == "CONST bop (#) x ys"
  "\<langle>\<rangle>"       == "\<guillemotleft>[]\<guillemotright>"
  "\<langle>x, xs\<rangle>"  == "x #\<^sub>u \<langle>xs\<rangle>"
  "\<langle>x\<rangle>"      == "x #\<^sub>u \<guillemotleft>[]\<guillemotright>"
  "x ^\<^sub>u y"   == "CONST bop (@) x y"
  "A \<^sup>\<frown>\<^sub>u B" == "CONST bop (\<^sup>\<frown>) A B"
  "last\<^sub>u(xs)" == "CONST uop CONST last xs"
  "front\<^sub>u(xs)" == "CONST uop CONST butlast xs"
  "head\<^sub>u(xs)" == "CONST uop CONST hd xs"
  "tail\<^sub>u(xs)" == "CONST uop CONST tl xs"
  "drop\<^sub>u(n,xs)" == "CONST bop CONST drop n xs"
  "take\<^sub>u(n,xs)" == "CONST bop CONST take n xs"
  "elems\<^sub>u(xs)" == "CONST uop CONST set xs"
  "sorted\<^sub>u(xs)" == "CONST uop CONST sorted xs"
  "distinct\<^sub>u(xs)" == "CONST uop CONST distinct xs"
  "xs \<restriction>\<^sub>u A"   == "CONST bop CONST seq_filter xs A"
  "A \<upharpoonleft>\<^sub>u xs"   == "CONST bop (\<upharpoonleft>\<^sub>l) A xs"
  "\<langle>n..k\<rangle>" == "CONST bop CONST upto n k"
  "\<langle>n..<k\<rangle>" == "CONST bop CONST upt n k"
  "map\<^sub>u f xs" == "CONST bop CONST map f xs"
  "zip\<^sub>u xs ys" == "CONST bop CONST zip xs ys"

syntax \<comment> \<open> Sets \<close>
  "_ufinite"    :: "logic \<Rightarrow> logic" ("finite\<^sub>u'(_')")
  "_uempset"    :: "('a set, '\<alpha>) uexpr" ("{}\<^sub>u")
  "_uset"       :: "args => ('a set, '\<alpha>) uexpr" ("{(_)}\<^sub>u")
  "_uunion"     :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (infixl "\<union>\<^sub>u" 65)
  "_uinter"     :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (infixl "\<inter>\<^sub>u" 70)
  "_uinsert"    :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("insert\<^sub>u")
  "_uimage"     :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<lparr>_\<rparr>\<^sub>u" [10,0] 10)
  "_usubset"    :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<subset>\<^sub>u" 50)
  "_usubseteq"  :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<subseteq>\<^sub>u" 50)
  "_uconverse"  :: "logic \<Rightarrow> logic" ("(_\<^sup>~)" [1000] 999)
  "_ucarrier"   :: "type \<Rightarrow> logic" ("[_]\<^sub>T")
  "_uid"        :: "type \<Rightarrow> logic" ("id[_]")
  "_uproduct"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr "\<times>\<^sub>u" 80)
  "_urelcomp"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr ";\<^sub>u" 75)

translations
  "finite\<^sub>u(x)" == "CONST uop (CONST finite) x"
  "{}\<^sub>u"      == "\<guillemotleft>{}\<guillemotright>"
  "insert\<^sub>u x xs" == "CONST bop CONST insert x xs"
  "{x, xs}\<^sub>u" == "insert\<^sub>u x {xs}\<^sub>u"
  "{x}\<^sub>u"     == "insert\<^sub>u x \<guillemotleft>{}\<guillemotright>"
  "A \<union>\<^sub>u B"   == "CONST bop (\<union>) A B"
  "A \<inter>\<^sub>u B"   == "CONST bop (\<inter>) A B"
  "f\<lparr>A\<rparr>\<^sub>u"     == "CONST bop CONST image f A"
  "A \<subset>\<^sub>u B"   == "CONST bop (\<subset>) A B"


  "A \<subseteq>\<^sub>u B"   == "CONST bop (\<subseteq>) A B"


  "P\<^sup>~"        == "CONST uop CONST converse P"
  "['a]\<^sub>T"     == "\<guillemotleft>CONST set_of TYPE('a)\<guillemotright>"
  "id['a]"    == "\<guillemotleft>CONST Id_on (CONST set_of TYPE('a))\<guillemotright>"
  "A \<times>\<^sub>u B"    == "CONST bop CONST Product_Type.Times A B"
  "A ;\<^sub>u B"    == "CONST bop CONST relcomp A B"

syntax \<comment> \<open> Partial functions \<close>
  "_umap_plus"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<oplus>\<^sub>u" 85)
  "_umap_minus" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<ominus>\<^sub>u" 85)

typedef ('a, 'b) pfun = "UNIV :: ('a \<rightharpoonup> 'b) set" ..

translations
  "f \<oplus>\<^sub>u g"   => "(f :: ((_, _) pfun, _) uexpr) + g"
  "f \<ominus>\<^sub>u g"   => "(f :: ((_, _) pfun, _) uexpr) - g"
  
syntax \<comment> \<open> Sum types \<close>
  "_uinl"       :: "logic \<Rightarrow> logic" ("inl\<^sub>u'(_')")
  "_uinr"       :: "logic \<Rightarrow> logic" ("inr\<^sub>u'(_')")
  
translations
  "inl\<^sub>u(x)" == "CONST uop CONST Inl x"
  "inr\<^sub>u(x)" == "CONST uop CONST Inr x"





(***   utp_unrest.thy   unrestriction   ***)



subsection \<open> Unrestriction Definitions and Core Syntax \<close>
  
text \<open> Unrestriction is an encoding of semantic freshness that allows us to reason about the
  presence of variables in predicates without being concerned with abstract syntax trees.
  An expression $p$ is unrestricted by lens $x$, written $x \mathop{\sharp} p$, if
  altering the value of $x$ has no effect on the valuation of $p$. This is a sufficient
  notion to prove many laws that would ordinarily rely on an \emph{fv} function. 

  Unrestriction was first defined in the work of Marcel Oliveira~\cite{Oliveira2005-PHD,Oliveira07} in his
  UTP mechanisation in \emph{ProofPowerZ}. Our definition modifies his in that our variables
  are semantically characterised as lenses, and supported by the lens laws, rather than named 
  syntactic entities. We effectively fuse the ideas from both Feliachi~\cite{Feliachi2010} and 
  Oliveira's~\cite{Oliveira07} mechanisations of the UTP, the former being also purely semantic
  in nature.

  We first set up overloaded syntax for unrestriction, as several concepts will have this
  defined. \<close>

consts
  unrest :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
syntax
  "_unrest" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<sharp>" 20)
translations
  "_unrest x p" == "CONST unrest x p"                                           
  "_unrest (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_unrest (x +\<^sub>L y) P"

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

text \<open> The following laws demonstrate the primary motivation for lens independence: a variable
  expression is unrestricted by another variable only when the two variables are independent. 
  Lens independence thus effectively allows us to semantically characterise when two variables,
  or sets of variables, are different. \<close>

lemma unrest_var [unrest]: "\<lbrakk> mwb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> y \<sharp> var x"
  by (transfer, auto)
    
lemma unrest_iuvar [unrest]: "\<lbrakk> mwb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> $y \<sharp> $x"
  by (simp add: unrest_var)

lemma unrest_ouvar [unrest]: "\<lbrakk> mwb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> $y\<acute> \<sharp> $x\<acute>"
  by (simp add: unrest_var)

text \<open> The following laws follow automatically from independence of input and output variables. \<close>
    
lemma unrest_iuvar_ouvar [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "mwb_lens y"
  shows "$x \<sharp> $y\<acute>"
  by (metis prod.collapse unrest_uexpr.rep_eq var.rep_eq var_lookup_out var_update_in)

lemma unrest_ouvar_iuvar [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "mwb_lens y"
  shows "$x\<acute> \<sharp> $y"
  by (metis prod.collapse unrest_uexpr.rep_eq var.rep_eq var_lookup_in var_update_out)

text \<open> Unrestriction distributes through the various function lifting expression constructs;
  this allows us to prove unrestrictions for the majority of the expression language. \<close>
    
lemma unrest_uop [unrest]: "x \<sharp> e \<Longrightarrow> x \<sharp> uop f e"
  by (transfer, simp)

lemma unrest_bop [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> bop f u v"
  by (transfer, simp)

lemma unrest_trop [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v; x \<sharp> w \<rbrakk> \<Longrightarrow> x \<sharp> trop f u v w"
  by (transfer, simp)

text \<open> For convenience, we also prove unrestriction rules for the bespoke operators on equality,
  numbers, arithmetic etc. \<close>
    
lemma unrest_eq [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u =\<^sub>u v"
  by (simp add: eq_upred_def, transfer, simp)

lemma unrest_zero [unrest]: "x \<sharp> 0"
  by (simp add: unrest_lit zero_uexpr_def)

lemma unrest_one [unrest]: "x \<sharp> 1"
  by (simp add: one_uexpr_def unrest_lit)

lemma unrest_numeral [unrest]: "x \<sharp> (numeral n)"
  by (simp add: numeral_uexpr_simp unrest_lit)

lemma unrest_plus [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u + v"
  by (simp add: plus_uexpr_def unrest)

lemma unrest_uminus [unrest]: "x \<sharp> u \<Longrightarrow> x \<sharp> - u"
  by (simp add: uminus_uexpr_def unrest)

lemma unrest_minus [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u - v"
  by (simp add: minus_uexpr_def unrest)

lemma unrest_times [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u * v"
  by (simp add: times_uexpr_def unrest)

lemma unrest_divide [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u / v"
  by (simp add: divide_uexpr_def unrest)

lemma unrest_case_prod [unrest]: "\<lbrakk> \<And> i j. x \<sharp> P i j \<rbrakk> \<Longrightarrow> x \<sharp> case_prod P v"
  by (simp add: prod.split_sel_asm)

text \<open> For a $\lambda$-term we need to show that the characteristic function expression does
  not restrict $v$ for any input value $x$. \<close>
    
lemma unrest_ulambda [unrest]:
  "\<lbrakk> \<And> x. v \<sharp> F x \<rbrakk> \<Longrightarrow> v \<sharp> (\<lambda> x \<bullet> F x)"
  by (transfer, simp)








subsection \<open> Substitution definitions \<close>

consts usubst :: "'s \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "\<dagger>" 80)

named_theorems usubst

type_synonym ('\<alpha>,'\<beta>) psubst = "'\<alpha> \<Rightarrow> '\<beta>"
type_synonym '\<alpha> usubst = "'\<alpha> \<Rightarrow> '\<alpha>"
  
lift_definition subst :: "('\<alpha>, '\<beta>) psubst \<Rightarrow> ('a, '\<beta>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" is
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
  unrest unrest_usubst
  
definition cond_subst :: "'\<alpha> usubst \<Rightarrow> (bool, '\<alpha>) uexpr \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> usubst" ("(3_ \<triangleleft> _ \<triangleright>\<^sub>s/ _)" [52,0,53] 52) where
"cond_subst \<sigma> b \<rho> = (\<lambda> s. if \<lbrakk>b\<rbrakk>\<^sub>e s then \<sigma>(s) else \<rho>(s))"
  
definition par_subst :: "'\<alpha> usubst \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('b \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> usubst" where
"par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2 = (\<lambda> s. (s \<oplus>\<^sub>L (\<sigma>\<^sub>1 s) on A) \<oplus>\<^sub>L (\<sigma>\<^sub>2 s) on B)"



subsection \<open> Syntax translations about subsitution \<close>

text \<open> We support two kinds of syntax for substitutions, one where we construct a substitution
  using a maplet-style syntax, with variables mapping to expressions. Such a constructed substitution
  can be applied to an expression. Alternatively, we support the more traditional notation, 
  $P \llbracket v / x \rrbracket$, which also support multiple simultaneous substitutions. We 
  have to use double square brackets as the single ones are already well used. 

  We set up non-terminals to represent a single substitution maplet, a sequence of maplets, a
  list of expressions, and a list of alphabets. The parser effectively uses @{term subst_upd}
  to construct substitutions from multiple variables. 
\<close>
  
nonterminal smaplet and smaplets and uexp and uexprs and salphas

syntax
  "_smaplet"  :: "[salpha, 'a] => smaplet"             ("_ /\<mapsto>\<^sub>s/ _")
  ""          :: "smaplet => smaplets"            ("_")
  "_SMaplets" :: "[smaplet, smaplets] => smaplets" ("_,/ _")
  "_SubstUpd" :: "['m usubst, smaplets] => 'm usubst" ("_/'(_')" [900,0] 900)
  "_Subst"    :: "smaplets => 'a \<rightharpoonup> 'b"            ("(1[_])")
  "_psubst"  :: "[logic, svars, uexprs] \<Rightarrow> logic"
  "_subst"   :: "logic \<Rightarrow> uexprs \<Rightarrow> salphas \<Rightarrow> logic" ("(_\<lbrakk>_'/_\<rbrakk>)" [990,0,0] 991)
  "_uexp_l"  :: "logic \<Rightarrow> uexp" ("_" [64] 64)
  "_uexprs"  :: "[uexp, uexprs] => uexprs" ("_,/ _")
  ""         :: "uexp => uexprs" ("_")
  "_salphas" :: "[salpha, salphas] => salphas" ("_,/ _")
  ""         :: "salpha => salphas" ("_")
  "_par_subst" :: "logic \<Rightarrow> salpha \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ [_|_]\<^sub>s _" [100,0,0,101] 101)
    
translations
  "_SubstUpd m (_SMaplets xy ms)"     == "_SubstUpd (_SubstUpd m xy) ms"
  "_SubstUpd m (_smaplet x y)"        == "CONST subst_upd m x y"
  "_Subst ms"                         == "_SubstUpd (CONST id) ms"
  "_Subst (_SMaplets ms1 ms2)"        <= "_SubstUpd (_Subst ms1) ms2"
  "_SMaplets ms1 (_SMaplets ms2 ms3)" <= "_SMaplets (_SMaplets ms1 ms2) ms3"
  "_subst P es vs" => "CONST subst (_psubst (CONST id) vs es) P"
  "_psubst m (_salphas x xs) (_uexprs v vs)" => "_psubst (_psubst m x v) xs vs"
  "_psubst m x v"  => "CONST subst_upd m x v"
  "_subst P v x" <= "CONST usubst (CONST subst_upd (CONST id) x v) P"
  "_subst P v x" <= "_subst P (_spvar x) v"
  "_par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2" == "CONST par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2"
  "_uexp_l e" => "e"

text \<open> Thus we can write things like @{term "\<sigma>(x \<mapsto>\<^sub>s v)"} to update a variable $x$ in $\sigma$ with
  expression $v$, @{term "[x \<mapsto>\<^sub>s e, y \<mapsto>\<^sub>s f]"} to construct a substitution with two variables,
  and finally @{term "P\<lbrakk>v/x\<rbrakk>"}, the traditional syntax.

  We can now express deletion of a substitution maplet. \<close>

definition subst_del :: "'\<alpha> usubst \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> usubst" (infix "-\<^sub>s" 85) where
"subst_del \<sigma> x = \<sigma>(x \<mapsto>\<^sub>s &x)"

subsection \<open> Substitution Application Laws \<close>

text \<open> We set up a simple substitution tactic that applies substitution and unrestriction laws \<close>

method subst_tac = (simp add: usubst unrest)?

text \<open> Evaluation of a substitution expression involves application of the substitution to different
  variables. Thus we first prove laws for these cases. The simplest substitution, $id$, when applied
  to any variable $x$ simply returns the variable expression, since $id$ has no effect. \<close>
  
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
  
lemma usubst_upd_comm_dash [usubst]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "\<sigma>($x\<acute> \<mapsto>\<^sub>s v, $x \<mapsto>\<^sub>s u) = \<sigma>($x \<mapsto>\<^sub>s u, $x\<acute> \<mapsto>\<^sub>s v)"
  using out_in_indep usubst_upd_comm by blast

lemma subst_upd_lens_plus [usubst]: 
  "subst_upd \<sigma> (x +\<^sub>L y) \<guillemotleft>(u,v)\<guillemotright> = \<sigma>(y \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>, x \<mapsto>\<^sub>s \<guillemotleft>u\<guillemotright>)"
  by (simp add: lens_defs uexpr_defs subst_upd_uvar_def, transfer, auto)

lemma subst_upd_in_lens_plus [usubst]: 
  "subst_upd \<sigma> (ivar (x +\<^sub>L y)) \<guillemotleft>(u,v)\<guillemotright> = \<sigma>($y \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>, $x \<mapsto>\<^sub>s \<guillemotleft>u\<guillemotright>)"
  by (simp add: lens_defs uexpr_defs subst_upd_uvar_def, transfer, auto simp add: prod.case_eq_if)

lemma subst_upd_out_lens_plus [usubst]: 
  "subst_upd \<sigma> (ovar (x +\<^sub>L y)) \<guillemotleft>(u,v)\<guillemotright> = \<sigma>($y\<acute> \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>, $x\<acute> \<mapsto>\<^sub>s \<guillemotleft>u\<guillemotright>)"
  by (simp add: lens_defs uexpr_defs subst_upd_uvar_def, transfer, auto simp add: prod.case_eq_if)
    
lemma usubst_lookup_upd_indep [usubst]:
  assumes "mwb_lens x" "x \<bowtie> y"
  shows "\<langle>\<sigma>(y \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, simp)
    
text \<open> If a variable is unrestricted in a substitution then it's application has no effect. \<close>

lemma usubst_apply_unrest [usubst]:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>s x = var x"
  by (simp add: unrest_usubst_def, transfer, auto simp add: fun_eq_iff, metis vwb_lens_wb wb_lens.get_put wb_lens_weak weak_lens.put_get)

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

text \<open> If a variable is unrestricted in an expression, then any substitution of that variable
  has no effect on the expression .\<close>
    
lemma subst_unrest [usubst]: "x \<sharp> P \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) \<dagger> P = \<sigma> \<dagger> P"
  by (simp add: subst_upd_uvar_def, transfer, auto)

lemma subst_unrest_2 [usubst]: 
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<bowtie> y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u,y \<mapsto>\<^sub>s v) \<dagger> P = \<sigma>(y \<mapsto>\<^sub>s v) \<dagger> P"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, auto, metis lens_indep.lens_put_comm)

lemma subst_unrest_3 [usubst]: 
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<bowtie> y" "x \<bowtie> z"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v, z \<mapsto>\<^sub>s w) \<dagger> P = \<sigma>(y \<mapsto>\<^sub>s v, z \<mapsto>\<^sub>s w) \<dagger> P"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, auto, metis (no_types, hide_lams) lens_indep_comm)

lemma subst_unrest_4 [usubst]: 
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<bowtie> y" "x \<bowtie> z" "x \<bowtie> u"
  shows "\<sigma>(x \<mapsto>\<^sub>s e, y \<mapsto>\<^sub>s f, z \<mapsto>\<^sub>s g, u \<mapsto>\<^sub>s h) \<dagger> P = \<sigma>(y \<mapsto>\<^sub>s f, z \<mapsto>\<^sub>s g, u \<mapsto>\<^sub>s h) \<dagger> P"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, auto, metis (no_types, hide_lams) lens_indep_comm)

lemma subst_unrest_5 [usubst]: 
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<bowtie> y" "x \<bowtie> z" "x \<bowtie> u" "x \<bowtie> v"
  shows "\<sigma>(x \<mapsto>\<^sub>s e, y \<mapsto>\<^sub>s f, z \<mapsto>\<^sub>s g, u \<mapsto>\<^sub>s h, v \<mapsto>\<^sub>s i) \<dagger> P = \<sigma>(y \<mapsto>\<^sub>s f, z \<mapsto>\<^sub>s g, u \<mapsto>\<^sub>s h, v \<mapsto>\<^sub>s i) \<dagger> P"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, auto, metis (no_types, hide_lams) lens_indep_comm)

lemma subst_compose_upd [usubst]: "x \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<circ> \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> \<circ> \<rho>)(x \<mapsto>\<^sub>s v) "
  by (simp add: subst_upd_uvar_def, transfer, auto simp add: unrest_usubst_def)


subsection \<open> Substitution laws \<close>
  
text \<open> We now prove the key laws that show how a substitution should be performed for every 
  expression operator, including the core function operators, literals, variables, and the 
  arithmetic operators. They are all added to the \emph{usubst} theorem attribute so that
  we can apply them using the substitution tactic. \<close>
    
lemma id_subst [usubst]: "id \<dagger> v = v"
  by (transfer, simp)

lemma subst_lit [usubst]: "\<sigma> \<dagger> \<guillemotleft>v\<guillemotright> = \<guillemotleft>v\<guillemotright>"
  by (transfer, simp)

lemma subst_var [usubst]: "\<sigma> \<dagger> var x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  by (transfer, simp)

lemma usubst_ulambda [usubst]: "\<sigma> \<dagger> (\<lambda> x \<bullet> P(x)) = (\<lambda> x \<bullet> \<sigma> \<dagger> P(x))"
  by (transfer, simp)

lemma unrest_usubst_del [unrest]: "\<lbrakk> vwb_lens x; x \<sharp> (\<langle>\<sigma>\<rangle>\<^sub>s x); x \<sharp> \<sigma> -\<^sub>s x \<rbrakk> \<Longrightarrow>  x \<sharp> (\<sigma> \<dagger> P)"
  by (simp add: subst_del_def subst_upd_uvar_def unrest_uexpr_def unrest_usubst_def subst.rep_eq usubst_lookup.rep_eq)
     (metis vwb_lens.put_eq)

text \<open> We add the symmetric definition of input and output variables to substitution laws
        so that the variables are correctly normalised after substitution. \<close>

lemma subst_uop [usubst]: "\<sigma> \<dagger> uop f v = uop f (\<sigma> \<dagger> v)"
  by (transfer, simp)

lemma subst_bop [usubst]: "\<sigma> \<dagger> bop f u v = bop f (\<sigma> \<dagger> u) (\<sigma> \<dagger> v)"
  by (transfer, simp)

lemma subst_trop [usubst]: "\<sigma> \<dagger> trop f u v w = trop f (\<sigma> \<dagger> u) (\<sigma> \<dagger> v) (\<sigma> \<dagger> w)"
  by (transfer, simp)

lemma subst_case_prod [usubst]:
  fixes P :: "'i \<Rightarrow> 'j \<Rightarrow> ('a, '\<alpha>) uexpr"  
  shows "\<sigma> \<dagger> case_prod (\<lambda> x y. P x y) v = case_prod (\<lambda> x y. \<sigma> \<dagger> P x y) v"
  by (simp add: case_prod_beta')

lemma subst_plus [usubst]: "\<sigma> \<dagger> (x + y) = \<sigma> \<dagger> x + \<sigma> \<dagger> y"
  by (simp add: plus_uexpr_def subst_bop)

lemma subst_times [usubst]: "\<sigma> \<dagger> (x * y) = \<sigma> \<dagger> x * \<sigma> \<dagger> y"
  by (simp add: times_uexpr_def subst_bop)

lemma subst_mod [usubst]: "\<sigma> \<dagger> (x mod y) = \<sigma> \<dagger> x mod \<sigma> \<dagger> y"
  by (simp add: mod_uexpr_def usubst)

lemma subst_div [usubst]: "\<sigma> \<dagger> (x div y) = \<sigma> \<dagger> x div \<sigma> \<dagger> y"
  by (simp add: divide_uexpr_def usubst)

lemma subst_minus [usubst]: "\<sigma> \<dagger> (x - y) = \<sigma> \<dagger> x - \<sigma> \<dagger> y"
  by (simp add: minus_uexpr_def subst_bop)

lemma subst_uminus [usubst]: "\<sigma> \<dagger> (- x) = - (\<sigma> \<dagger> x)"
  by (simp add: uminus_uexpr_def subst_uop)

lemma subst_zero [usubst]: "\<sigma> \<dagger> 0 = 0"
  by (simp add: zero_uexpr_def subst_lit)

lemma subst_one [usubst]: "\<sigma> \<dagger> 1 = 1"
  by (simp add: one_uexpr_def subst_lit)

lemma subst_eq_upred [usubst]: "\<sigma> \<dagger> (x =\<^sub>u y) = (\<sigma> \<dagger> x =\<^sub>u \<sigma> \<dagger> y)"
  by (simp add: eq_upred_def usubst)

text \<open> This laws shows the effect of applying one substitution after another -- we simply
  use function composition to compose them. \<close>
    
lemma subst_subst [usubst]: "\<sigma> \<dagger> \<rho> \<dagger> e = (\<rho> \<circ> \<sigma>) \<dagger> e"
  by (transfer, simp)

text \<open> The next law is similar, but shows how such a substitution is to be applied to every
  updated variable additionally. \<close>
    
lemma subst_upd_comp [usubst]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "\<rho>(x \<mapsto>\<^sub>s v) \<circ> \<sigma> = (\<rho> \<circ> \<sigma>)(x \<mapsto>\<^sub>s \<sigma> \<dagger> v)"
  by (rule ext, simp add:uexpr_defs subst_upd_uvar_def, transfer, simp)

lemma subst_singleton:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "x \<sharp> \<sigma>"
  shows "\<sigma>(x \<mapsto>\<^sub>s v) \<dagger> P = (\<sigma> \<dagger> P)\<lbrakk>v/x\<rbrakk>"
  using assms
  by (simp add: usubst)

lemmas subst_to_singleton = subst_singleton id_subst

subsection \<open> Ordering substitutions \<close>

text \<open> A simplification procedure to reorder substitutions maplets lexicographically by variable syntax \<close>

simproc_setup subst_order ("subst_upd_uvar (subst_upd_uvar \<sigma> x u) y v") =
  {* (fn _ => fn ctx => fn ct => 
        case (Thm.term_of ct) of
          Const ("utp_subst.subst_upd_uvar", _) $ (Const ("utp_subst.subst_upd_uvar", _) $ s $ x $ u) $ y $ v
            => if (YXML.content_of (Syntax.string_of_term ctx x) > YXML.content_of(Syntax.string_of_term ctx y))
               then SOME (mk_meta_eq @{thm usubst_upd_comm})
               else NONE  |
          _ => NONE) 
  *}

subsection \<open> Unrestriction laws \<close>

text \<open> These are the key unrestriction theorems for substitutions and expressions involving substitutions. \<close>
  
lemma unrest_usubst_single [unrest]:
  "\<lbrakk> mwb_lens x; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> P\<lbrakk>v/x\<rbrakk>"
  by (transfer, auto simp add: subst_upd_uvar_def unrest_uexpr_def)

lemma unrest_usubst_id [unrest]:
  "mwb_lens x \<Longrightarrow> x \<sharp> id"
  by (simp add: unrest_usubst_def)

lemma unrest_usubst_upd [unrest]:
  "\<lbrakk> x \<bowtie> y; x \<sharp> \<sigma>; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> \<sigma>(y \<mapsto>\<^sub>s v)"
  by (simp add: subst_upd_uvar_def unrest_usubst_def unrest_uexpr.rep_eq lens_indep_comm)

lemma unrest_subst [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> x \<sharp> (\<sigma> \<dagger> P)"
  by (transfer, simp add: unrest_usubst_def)
    
subsection \<open> Conditional Substitution Laws \<close>
  
lemma usubst_cond_upd_1 [usubst]:
  "\<sigma>(x \<mapsto>\<^sub>s u) \<triangleleft> b \<triangleright>\<^sub>s \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>)(x \<mapsto>\<^sub>s u \<triangleleft> b \<triangleright> v)"
  by (simp add: cond_subst_def subst_upd_uvar_def uexpr_defs, transfer, auto)

lemma usubst_cond_upd_2 [usubst]:
  "\<lbrakk> vwb_lens x; x \<sharp> \<rho> \<rbrakk> \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s u) \<triangleleft> b \<triangleright>\<^sub>s \<rho> = (\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>)(x \<mapsto>\<^sub>s u \<triangleleft> b \<triangleright> &x)"
  by (simp add: cond_subst_def subst_upd_uvar_def unrest_usubst_def uexpr_defs, transfer)
     (metis (full_types, hide_lams) id_apply pr_var_def subst_upd_uvar_def usubst_upd_pr_var_id var.rep_eq)
 
lemma usubst_cond_upd_3 [usubst]:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>)(x \<mapsto>\<^sub>s &x \<triangleleft> b \<triangleright> v)"
  by (simp add: cond_subst_def subst_upd_uvar_def unrest_usubst_def uexpr_defs, transfer)
     (metis (full_types, hide_lams) id_apply pr_var_def subst_upd_uvar_def usubst_upd_pr_var_id var.rep_eq)
    
lemma usubst_cond_id [usubst]:
  "id \<triangleleft> b \<triangleright>\<^sub>s id = id"
  by (auto simp add: cond_subst_def)
    
subsection \<open> Parallel Substitution Laws \<close>
    
lemma par_subst_id [usubst]:
  "\<lbrakk> vwb_lens A; vwb_lens B \<rbrakk> \<Longrightarrow> id [A|B]\<^sub>s id = id"
  by (simp add: par_subst_def id_def)

lemma par_subst_left_empty [usubst]:
  "\<lbrakk> vwb_lens A \<rbrakk> \<Longrightarrow> \<sigma> [\<emptyset>|A]\<^sub>s \<rho> = id [\<emptyset>|A]\<^sub>s \<rho>"
  by (simp add: par_subst_def pr_var_def)

lemma par_subst_right_empty [usubst]:
  "\<lbrakk> vwb_lens A \<rbrakk> \<Longrightarrow> \<sigma> [A|\<emptyset>]\<^sub>s \<rho> = \<sigma> [A|\<emptyset>]\<^sub>s id"
  by (simp add: par_subst_def pr_var_def)
    
lemma par_subst_comm:
  "\<lbrakk> A \<bowtie> B \<rbrakk> \<Longrightarrow> \<sigma> [A|B]\<^sub>s \<rho> = \<rho> [B|A]\<^sub>s \<sigma>"
  by (simp add: par_subst_def lens_override_def lens_indep_comm)
      
lemma par_subst_upd_left_in [usubst]:
  "\<lbrakk> vwb_lens A; A \<bowtie> B; x \<subseteq>\<^sub>L A \<rbrakk> \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) [A|B]\<^sub>s \<rho> = (\<sigma> [A|B]\<^sub>s \<rho>)(x \<mapsto>\<^sub>s v)"
  by (simp add: par_subst_def subst_upd_uvar_def lens_override_put_right_in)
     (simp add: lens_indep_comm lens_override_def sublens_pres_indep)

lemma par_subst_upd_left_out [usubst]:
  "\<lbrakk> vwb_lens A; x \<bowtie> A \<rbrakk> \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) [A|B]\<^sub>s \<rho> = (\<sigma> [A|B]\<^sub>s \<rho>)"
  by (simp add: par_subst_def subst_upd_uvar_def lens_override_put_right_out)
     
lemma par_subst_upd_right_in [usubst]:
  "\<lbrakk> vwb_lens B; A \<bowtie> B; x \<subseteq>\<^sub>L B \<rbrakk> \<Longrightarrow> \<sigma> [A|B]\<^sub>s \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> [A|B]\<^sub>s \<rho>)(x \<mapsto>\<^sub>s v)"
  using lens_indep_sym par_subst_comm par_subst_upd_left_in by fastforce

lemma par_subst_upd_right_out [usubst]:
  "\<lbrakk> vwb_lens B; A \<bowtie> B; x \<bowtie> B \<rbrakk> \<Longrightarrow> \<sigma> [A|B]\<^sub>s \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> [A|B]\<^sub>s \<rho>)"
  by (simp add: par_subst_comm par_subst_upd_left_out)
    











named_theorems alpha

method alpha_tac = (simp add: alpha unrest)?

lift_definition aext :: "('a, '\<beta>) uexpr \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> ('a, '\<alpha>) uexpr" (infixr "\<oplus>\<^sub>p" 95)
is "\<lambda> P x b. P (get\<^bsub>x\<^esub> b)" .

subsection \<open> Substitution Alphabet Extension \<close>

text \<open> This allows us to extend the alphabet of a substitution, in a similar way to expressions. \<close>
  
definition subst_ext :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> '\<beta> usubst" (infix "\<oplus>\<^sub>s" 65) where "\<sigma> \<oplus>\<^sub>s x = (\<lambda> s. put\<^bsub>x\<^esub> s (\<sigma> (get\<^bsub>x\<^esub> s)))"

lemma id_subst_ext [usubst]:
  "wb_lens x \<Longrightarrow> id \<oplus>\<^sub>s x = id"
  by (metis eq_id_iff id_apply iso_tuple_surjective_proof_assist_def subst_ext_def wb_lens.source_stability wb_lens_def weak_lens.put_get weak_lens.update_def)


    
subsection \<open> Substitution Alphabet Restriction \<close>

text \<open> This allows us to reduce the alphabet of a substitution, in a similar way to expressions. \<close>
  
definition subst_res :: "'\<alpha> usubst \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<beta> usubst" (infix "\<restriction>\<^sub>s" 65) where
 "\<sigma> \<restriction>\<^sub>s x = (\<lambda> s. get\<^bsub>x\<^esub> (\<sigma> (create\<^bsub>x\<^esub> s)))"

lemma id_subst_res [usubst]:
  "mwb_lens x \<Longrightarrow> id \<restriction>\<^sub>s x = id"
  by (metis eq_id_iff mwb_lens_weak subst_res_def weak_lens.create_get)









end