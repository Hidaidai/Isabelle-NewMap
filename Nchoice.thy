theory Nchoice
imports Assign
begin

subsection \<open>Generic operations\<close>
(*Generic operations without axiomas*)

locale abel_abel_semigroup = abel_semigroup +
  assumes idemp [ac_simps]: "a \<^bold>* a = a" 

locale abel_abe_semigroup = abel_semigroup +
  assumes idem [ac_simps]: "a \<^bold>* a = a" 

class nchoice = uzero + uskip +
  fixes nchoice :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)
  assumes nch_assoc [algebra_simps, field_simps]: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
      and nch_commute [algebra_simps, field_simps]: "x \<sqinter> y = y \<sqinter> x"
      and nch_idemp [algebra_simps, field_simps]: "(x \<sqinter> x) = x" 
      and nch_zero_left[simp] : "\<bottom> \<sqinter> a = \<bottom>"
      and nch_zero_right[simp] : "a \<sqinter> \<bottom> = \<bottom>"
      and nch_skip_left: " II \<sqinter> a = a"
      and nch_skip_right: "a \<sqinter>  II = a"
begin
sublocale ncho: semigroup nchoice
  by standard (fact nch_assoc)

sublocale ncho: abel_semigroup nchoice
  by standard (fact nch_commute)

declare ncho.left_commute [algebra_simps, field_simps]

sublocale ncho: abel_abel_semigroup nchoice
  by standard (fact nch_idemp)

lemmas ncho_ac = ncho.assoc ncho.commute ncho.left_commute  ncho.idemp

sublocale add: monoid nchoice  II
  by standard (fact nch_skip_left nch_skip_right)+

lemma zero_reorient: "a =  II  \<longleftrightarrow>  II = a"
  by (fact eq_commute)
end

(*LawA1_1,LawA1_2*)
class comm_monoid_nchoice = nchoice + 
  assumes nchoice_II : " II \<sqinter> a = a"
begin
subclass nchoice ..

sublocale add: comm_monoid nchoice II
   by standard (simp add: ac_simps)
end

print_locale! comm_monoid_nchoice

subsection \<open>Generalized operations over a set\<close>

context comm_monoid_nchoice
begin
sublocale Nchoice: comm_monoid_set nchoice II
  defines Nchoice = Nchoice.F ..

abbreviation NChoice ("\<Sqinter>_" [1000] 999)
  where "\<Sqinter>A \<equiv> Nchoice (\<lambda>a. a) A"

print_locale! comm_monoid_nchoice

end


(***test***)
lemma nch_left_comm : "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  by (simp add: ncho.commute ncho.left_commute)

lemma nch_left_idem : "x \<sqinter> (x \<sqinter> y) = x \<sqinter> y"
  by (metis nch_assoc nch_idemp)

lemma "((x \<sqinter> (x \<sqinter> y)) ;; Y:=B) ;; Z :=C = (x \<sqinter> y) ;; (Y:=B ;; Z :=C)"
  by (simp add: nch_left_idem serial_assoc)

lemma  "\<Sqinter>{x,y} =  \<Sqinter>{x,y,y}"
  by auto

lemma "(\<Sqinter>A \<sqinter> \<Sqinter>A) \<sqinter> \<Sqinter>C = \<Sqinter>A  \<sqinter> \<Sqinter>C"
  by (simp add: nch_idemp)


lemma LawA3_1_1:
  assumes "finite A" and "finite B"
  shows "\<Sqinter>(A \<union> B)  = \<Sqinter>(A-(A \<inter> B)) \<sqinter> \<Sqinter>(B-(A \<inter> B)) \<sqinter> \<Sqinter>(A \<inter> B)"
  by (metis Diff_Int2 Int_commute Nchoice.union_diff2 assms inf.idem)

lemma LawA3_1_2:
  assumes "finite A" and "finite B"
  shows "\<Sqinter>(A \<union> B)  = \<Sqinter>(A-(A \<inter> B)) \<sqinter> \<Sqinter>(B-(A \<inter> B)) \<sqinter> \<Sqinter>(A \<inter> B)  \<sqinter> \<Sqinter>(A \<inter> B)"
  by (simp add: LawA3_1_1 assms nch_left_idem ncho.commute)

lemma LawA3_1:
  assumes "finite A" and "finite B"
  shows "\<Sqinter>(A \<union> B)  = \<Sqinter>(A) \<sqinter> \<Sqinter>(B)"
  by (metis LawA3_1_1 LawA3_1_2 Nchoice.union_inter assms)

lemma "A = {x,y} \<Longrightarrow> \<Sqinter>(A) = x \<sqinter> y"
  by (simp add: Nchoice.insert_if ncho_ac(4))

end







