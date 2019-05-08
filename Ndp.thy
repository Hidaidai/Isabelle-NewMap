theory Ndp
imports Main Complex_Main
begin

no_notation Set.member ("(_/ : _)" [51, 51] 50)


section \<open>Nondeterministic Probabilistics\<close>
subsection \<open>Nondeterministic operater and Probabilistics operater\<close>

locale Prep =
  fixes  nodt :: " 'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<sqinter>" 70)
    and nep:: "'b \<Rightarrow>'b \<Rightarrow>'b" (infixl ";" 60)
  assumes  commutative [simp]: "(x \<sqinter> y) = (y \<sqinter> x)"
    and associative [simp]: "((x \<sqinter> y) \<sqinter> z) = (x \<sqinter> (y \<sqinter> z))"
    and idempotent [simp]: "(x \<sqinter> x) = x"
    and next_one [simp]: "(x ; y) ; z = x ; (y ; z)"
    and nodtnep_r [simp]: "(x \<sqinter> y) ; z = (x ; z) \<sqinter> (y ; z)"
    and nodtnep_l [simp]: "z ; (x \<sqinter> y) = (z ; x) \<sqinter> (z ; y)"

locale Prob = 
  fixes probo :: " 'a \<Rightarrow> 'b \<Rightarrow> 'b" (infixl ":" 80)

(*make + & - by myself,so i set (a+(1-a)) = 1 whitout proof *)

locale Probjia = Prob + Prep +
  fixes probjiao :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<oplus>" 90)
  assumes  probjia_a [simp]: "(a : (x \<sqinter> y)) \<oplus> G = ((a : x) \<oplus> G) \<sqinter> ((a : y) \<oplus> G)"
and probjia_f [simp]: "(a : x) \<oplus> (b : x) = (a + b) : x"                     
and probjia_i [simp]: "(1 : x)  = x"   
and probjia_h [simp]: " H \<oplus> G = G \<oplus> H"

begin
print_locale! Probjia

lemma firstexamp [simp]: "(P \<sqinter> Q) = (P \<sqinter> Q) \<sqinter> ((b : P) \<oplus> ((1 - b) : Q))"            
proof -
  have "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) = (b+(1-b)):(P\<sqinter>Q) \<sqinter> ((b:P) \<oplus> ((1-b):Q))"
    by (simp only: probjia_i)
  then have "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) = (b:(P\<sqinter>Q))\<oplus>((1-b):(P\<sqinter>Q))\<sqinter>((b:P)\<oplus>((1-b):Q))"
    by (simp only: probjia_f)
  then have "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) = (b:P)\<oplus>((1-b):(P\<sqinter>Q)) \<sqinter>  (b:Q)\<oplus>((1-b):(P\<sqinter>Q)) \<sqinter> ((b:P)\<oplus>((1-b):Q))"
    by (simp only: probjia_a)
  then have "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) = ((1-b):(P\<sqinter>Q))\<oplus>(b:P) \<sqinter>  ((1-b):(P\<sqinter>Q))\<oplus>(b:Q) \<sqinter> ((b:P)\<oplus>((1-b):Q))"
    by (simp only: probjia_h)
  then have "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) = (((1-b):P)\<oplus>(b:P) \<sqinter> ((1-b):Q)\<oplus>(b:P)) \<sqinter> (((1-b):P)\<oplus>(b:Q) \<sqinter>((1-b):Q)\<oplus>(b:Q)) \<sqinter> ((b:P)\<oplus>((1-b):Q))"
    by (simp only: probjia_a)
  then have "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) =  ((1-b):P)\<oplus>(b:Q) \<sqinter> ((1-b):Q)\<oplus>(b:Q) \<sqinter> (((1-b):P)\<oplus>(b:P) \<sqinter> ((1-b):Q)\<oplus>(b:P)) \<sqinter> ((1-b):Q)\<oplus>(b:P)  "
    by (simp only: probjia_h commutative) 
  then have "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) = ((1-b):P)\<oplus>(b:Q) \<sqinter>((1-b):Q)\<oplus>(b:Q) \<sqinter> ((1-b):P)\<oplus>(b:P) \<sqinter> ((1-b):Q)\<oplus>(b:P) \<sqinter> ((1-b):Q)\<oplus>(b:P)  "
    by (simp only: associative ) 
  then have "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) = ((1-b):P)\<oplus>(b:Q) \<sqinter> ((1-b):Q)\<oplus>(b:Q) \<sqinter> ((1-b):P)\<oplus>(b:P) \<sqinter> ((1-b):Q)\<oplus>(b:P) "
    by (simp only: associative idempotent) 
  then have "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) = ((1-b):(P\<sqinter>Q))\<oplus>(b:Q) \<sqinter> ((1-b):P)\<oplus>(b:P) \<sqinter> ((1-b):Q)\<oplus>(b:P) "
    by (simp only: probjia_a ) 
  then have "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) = ((1-b):(P\<sqinter>Q))\<oplus>(b:Q) \<sqinter> ((1-b):(P\<sqinter>Q))\<oplus>(b:P) "
    by (simp only: associative probjia_a) 
  then have   "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) = (b:Q)\<oplus>((1-b):(P\<sqinter>Q)) \<sqinter> (b:P)\<oplus>((1-b):(P\<sqinter>Q))"
    by (simp only: probjia_h)
  then have "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) = (b:(P\<sqinter>Q))\<oplus>((1-b):(P\<sqinter>Q))"
    by (simp only: commutative probjia_a)
  then have "(P\<sqinter>Q)\<sqinter>((b:P)\<oplus>((1-b):Q)) = (b+(1-b)):(P\<sqinter>Q)"
    by (simp only: probjia_f)
  then show ?thesis
    by (simp only: probjia_i)
qed
end                                   

end