theory newmap_expr1 
imports Main
begin

typedecl proc
consts
  uskip    :: "'a"  ("II")
  uzero    :: "'a"  ("\<bottom>")


subsection \<open>Generic operations\<close>
(*Generic operations without axiomas*)

locale abel_abel_semigroup = abel_semigroup +
  assumes idemp [ac_simps]: "a \<^bold>* a = a" 

locale nchoice=
  fixes nchoice :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)
  assumes nchoice_zero_left[simp] : "\<bottom> \<sqinter> a = \<bottom>"
    and nchoice_zero_right[simp] : "a \<sqinter> \<bottom> = \<bottom>"

subsection \<open>Semigroups and Monoids\<close>
(*In order to define the set operation notation,Semigroups and Monoids *)

locale semigroup_nchoice = nchoice +
  assumes nchoice_assoc [algebra_simps, field_simps]: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
begin
sublocale ncho: semigroup nchoice
  by standard (fact nchoice_assoc)
end

locale ab_semigroup_nchoice = semigroup_nchoice +
  assumes nchoice_commute [algebra_simps, field_simps]: "x \<sqinter> y = y \<sqinter> x"
begin
sublocale ncho: abel_semigroup nchoice
  by standard (fact nchoice_commute)

declare ncho.left_commute [algebra_simps, field_simps]
end

locale ab_ab_semigroup_nchoice = ab_semigroup_nchoice +
  assumes nchoice_idemp [algebra_simps, field_simps]: "(x \<sqinter> x) = x" 
begin
sublocale ncho: abel_abel_semigroup nchoice
  by standard (fact nchoice_idemp)

lemmas ncho_ac = ncho.assoc ncho.commute ncho.left_commute  ncho.idemp
end

locale monoid_nchoice =  semigroup_nchoice +
  assumes nchoice_skip_left: " II \<sqinter> a = a"
    and nchoice_skip_right: "a \<sqinter>  II = a"
begin
sublocale add: monoid nchoice  II
  by standard (fact nchoice_skip_left nchoice_skip_right)+

lemma zero_reorient: "a =  II  \<longleftrightarrow>  II = a"
  by (fact eq_commute)
end
(*LawA1_1,LawA1_2*)
locale comm_monoid_nchoice = ab_ab_semigroup_nchoice +
  assumes nchoice_skip : " II \<sqinter> a = a"
begin
sublocale monoid_nchoice
  using monoid_nchoice.intro monoid_nchoice_axioms_def ncho.commute nchoice_skip semigroup_nchoice_axioms by fastforce

sublocale add: comm_monoid nchoice II
  by (meson comm_monoid.intro comm_monoid_axioms.intro local.add.right_neutral ncho.abel_semigroup_axioms)
end










print_locale! comm_monoid_nchoice

subsection \<open>Generalized operations over a set\<close>

context comm_monoid_nchoice
begin
sublocale Nchoice: comm_monoid_set nchoice II
  defines Nchoice = Nchoice.F ..

abbreviation NChoice ("\<Sqinter>_" [1000] 999)
  where "\<Sqinter>A \<equiv> Nchoice (\<lambda>a. a) A"


end

print_locale! comm_monoid_nchoice













subsection \<open> seq operaters \<close>

consts
  useq     :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

locale serial =   
  fixes nep :: "'a \<Rightarrow>'a \<Rightarrow>'a" (infixl ";" 60)
  defines  "x ; y \<equiv> useq x y"
  assumes serial_assoc : "(x ; y) ; z = x ; (y ; z)"
    and serial_skip_left : "skip ; x = x"
    and serial_skip_right : "x ; skip = x" 
    and serial_zero_left : "\<bottom> ; x = \<bottom>"
    and serial_zero_right : "x ; \<bottom> = \<bottom>"




end