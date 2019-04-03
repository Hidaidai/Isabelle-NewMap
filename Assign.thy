theory Assign
  imports Main
begin


subsection \<open> preparation \<close>

consts order :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infixr "\<sqsubseteq>" 60)

type_synonym 'a proc = "('a \<times> 'a) list"
consts uskip :: "'a proc" ("II")
consts uzero :: "'a proc" ("\<bottom>")

lemma "[x,y,z]@[u] = [x,y,z,u]"  by simp
lemma "set [a,b,c,a] = {a,b,c,a}"  by simp
lemma "zip [a,b,c] [x,y,z] = [(a,x),(b,y),(c,z)]"  by simp
lemma "map f [a,b] = [f a,f b]"  by simp
lemma "fst (a,b) = a" by simp

subsection \<open>assignment operater \<close>

class assi =  
  fixes assi :: "'a list\<Rightarrow> 'a list\<Rightarrow> 'a proc"  (infixl ":=" 65)
  assumes assi_equal: "set (zip X A) = set(zip Y B) \<Longrightarrow> X := A = Y:=B"
      and assi_orde1: "set (zip X A) \<subseteq> set(zip Y B) \<Longrightarrow> X := A \<sqsubseteq> Y:=B"
      and assi_orde2: "X := A \<sqsubseteq> Y:=B \<Longrightarrow> set (zip X A) \<subseteq> set(zip Y B)"
      and assi_uskip: "set (zip u u) = {}"
  assumes assi_setadd: "Z = X @ Y \<Longrightarrow> c= A @ B \<Longrightarrow>set (zip Z C) = set (zip X A) \<union> set(zip Y B) "

lemma l1:"[x,y,z,u] := [a,b,c,u] = [x,y,z] := [a,b,c]"
  by (metis append.right_neutral assi_equal assi_setadd assi_uskip)

lemma l2:  "[x,y,z,w] := [a,b,c,d] = [x,y,w,z] := [a,b,d,c]"
proof -
  have f1: "set (zip [x,y,w,z] [a,b,d,c]) = set (zip [x,y,z,w] [a,b,c,d])"
    by (simp add: insert_commute)
  show ?thesis
    using assi_equal f1 by blast
qed

lemma l4: "[x,y,z] := [a,b,c] \<sqsubseteq> [x,y,z,w] := [a,b,c,d]"
  by (simp add: assi_orde1)

class serial =  assi +
  fixes nep :: "'a proc \<Rightarrow>'a proc \<Rightarrow>'a proc" (infixl ";;" 60)
  assumes serial_assoc : "(x ;; y) ;; z = x ;; (y ;; z)"
      and serial_skip_left : "II ;; x = x"
      and serial_skip_right : "x ;; II = x" 
  assumes assi_serial_map : "X:=A ;; X:=map f X = X:=map f A"

lemma l3: "[x,y]:=[a,b] ;; [x,y]:= [f x,f y] = [x,y]:=[f a,f b]" 
  by (metis (mono_tags, hide_lams) assi_serial_map insert_Nil list.simps(8) list.simps(9))



























end