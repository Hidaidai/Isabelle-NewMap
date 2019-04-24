
theory nmap_test
imports
  nmap_assign
begin


alphabet state =
  a :: int
  b :: int 
  c :: int

theorem "(a,b) := (2+3, &b) = (a := 5)"
  by (simp add:  usubst_upd_comm usubst_upd_var_id)

theorem "(a,b,c) := (2, &b, 4) = (a,c) := (2,4)"
  by (metis b_vwb_lens pr_var_def state_indeps(1) usubst_upd_comm usubst_upd_pr_var_id)

theorem  "(a:=5) \<triangleleft> True \<triangleright>\<^sub>\<p> (b:=6) = (a:=5)"
  by (simp add: ifprog_def)

theorem (in nchoice) "(a:=3)  \<sqinter> (b:=4) =  (a:=4)  \<sqinter>  (b:=3)" 
  by (simp add: nch_commute)


end