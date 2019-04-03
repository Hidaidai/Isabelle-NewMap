theory newmap_expr3
imports Main newmap_expr2
begin

typedecl proc

datatype  prog_expr =
Const_expr proc |
if_then_else_expr proc bool proc |
sequential_expr proc proc |
nondeterm_choice_expr proc proc

primrec val_prog_expr :: "proc \<Rightarrow> ('a \<Rightarrow> proc) \<Rightarrow> proc" where
"val_prog_expr (Const_expr P) s = s P" |
"val_prog_expr (if_then_else_expr P b Q) s = (val_prog_expr P s \<triangleleft> b \<triangleright>\<^sub>P val_prog_expr Q s)" 







end