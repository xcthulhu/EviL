header{* Intuitions in Intuitionistic Logic *}

theory Intuitions
imports Main

no_notation
  bot ("\<bottom>") and
  
(*  imp (infixr "\<rightarrow>" 25)  and
  vdash ("\<turnstile> _" [20] 20) and
  lift_vdash (infix ":\<turnstile>" 10) and 
  Not  ("\<not> _" [40] 40) and
  neg ("\<not> _" [40] 40) and
  pneg ("\<sim> _" [40] 40) *)

datatype 'a int_form = 
    CL_P "'a"                       ("P#")
  | CL_Bot                          ("\<bottom>")
  | CL_Imp "'a cl_form" "'a cl_form"  (infixr "\<rightarrow>" 25)