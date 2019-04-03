theory Prog
imports Ifte
begin

datatype 'a prog =
Const "'a proc" |
if_then_else "'a prog" bool "'a prog" |
sequential "'a prog" "'a prog" |
nondeterm_choice "'a prog" "'a prog"

primrec prog_op where
"prog_op  (Const P) = P" |
"prog_op (if_then_else P b Q) = prog_op P \<triangleleft> b \<triangleright>\<^sub>\<p> prog_op Q " |
"prog_op (sequential P Q) = prog_op P ;; prog_op Q " |
"prog_op (nondeterm_choice P Q) = prog_op P \<sqinter> prog_op Q"

(****next I hope to prove that all kinds of programs have a uniform form***)




end