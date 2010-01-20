header {* A Theory for Manipulating Finite and Infinite Sets, Lists *}

theory Set_to_List
imports Main Infinite_Set
begin

text
{* This file sets forward two main results.  The first is an elementary theory 
   regarding the translation between sets and finite lists.  The second is the
   embedding, via (relatively) injective functions, from finite lists to
   infinite lists.

   We shall begin by giving our theory for converting finite sets to
   lists via a choice function. *}

lemma finite_set_list_ex:
  assumes fin: "finite (A::'a set)"
    shows "\<exists>ls. set ls = A"
  using fin
proof (induct, simp)
   -- "We only have to show for one case"
   case (insert a A)
    then have "\<exists> ls . insert a A = set (a # ls)" by fastsimp
    thus ?case by blast
qed

lemma set_of_list_is_finite:
  "finite (set \<Gamma>)"
by (induct \<Gamma>, simp, clarify)

text
{* We now give the definition of the our function which converts
   sets into lists.  We should note that since it is a choice function,
   it is only meaningful in cases in which a list exists. In fact, we 
   will see that our function is meaningful in exactly those cases where 
   our original set is finite. We end with noting that, despite being
   based on a choice function, it has a definite value for the empty
   set. *}

definition list :: "'a set \<Rightarrow> 'a list" where
"list A = (SOME ls. set ls = A)"

lemma set_list: "finite A \<longleftrightarrow> (set (list A) = A)"
proof
    assume "finite A"
    with finite_set_list_ex [where A="A"]
         some_eq_ex [where P="% ls. set ls = A"]        
    show "set (list A) = A"
      by (induct, simp add: list_def)
  next
    assume "set (list A) = A"
    with set_of_list_is_finite [where \<Gamma>="list A"]
    show  "finite A" by simp
qed

lemma empty_set_list[simp]: "list {} = []"
proof -
  { fix ls
    have "~(ls = []) \<longrightarrow> ~(set ls = {})" 
      by (induct ls, fastsimp, auto) }
  hence "\<exists>! ls. set ls = {}" by fastsimp+
  with some1_equality [where a="[]"
                         and P="% ls. set ls = {}"]
  show ?thesis by (simp add: list_def)
qed

text
{* We now turn to showing that if @{term [show_types] "A::'a set"} is finite
   and @{term [show_types] "B::'b set"} is infinite, then there exists 
   a function @{term [show_types] "f::'a \<Rightarrow> 'b"} which is injective on 
   @{term "A::'a set"} and has its range in @{term "B::'b set"} 

   Rather than prove this from scratch, we will use some library theorems
   to assist us, namely @{thm [source] "finite_imp_nat_seg_image_inj_on"}
   and @{thm [source] "infinite_countable_subset"}.
   
   However, we evidently need to prove an elementary lemma regarding
   the relative inverses of functions that are injective on some range. *}

lemma inj_on_inj_off:
   assumes one_one: "inj_on f A"
     shows "\<exists>g. inj_on g (f ` A) 
                \<and> (\<forall> x \<in> A. x = (g o f) x)
                \<and> (\<forall> y \<in> (f ` A). (f o g) y = y)"
using one_one
proof -
  { fix b; from one_one have "b \<in> (f ` A) = (EX! x. x \<in> A \<and> b = f x)"
      by (unfold inj_on_def, unfold image_def, blast) }
  note \<heartsuit> = this
  -- "We now turn to crafting our choice function"
  let ?g = "% b. SOME x. x \<in> A \<and> b = f x"
  -- "We'll prove that it's one-one now"
  { fix b c; 
    assume I:  "b \<in> (f ` A)" 
       and II: "c \<in> (f ` A)"
    have "(b = c) = (?g b = ?g c)"
    proof (auto)
      --"We shall only show right to left"
      assume "?g b = ?g c"
      moreover from \<heartsuit> I someI_ex [where P="% x. x \<in> A \<and> b = f x"]
         have A: "b = f (?g b)" by blast
      moreover from \<heartsuit> II someI_ex [where P="% x. x \<in> A \<and> c = f x"]
         have B: "c = f (?g c)" by blast
      ultimately show "b = c" by fastsimp
    qed }
  with inj_on_def have "inj_on ?g (f ` A)" by blast
  moreover 
  --{*Evidently @{term "?g"} is a left-inverse of @{term "f"}*} 
  --{*relative to @{term "A"}*} 
  { fix x; assume "x \<in> A" 
    with \<heartsuit> one_one 
         someI_ex [where P="% y. y \<in> A \<and> f x = f y"]
    have "x = (?g o f) x"
      by (unfold inj_on_def, unfold comp_def, blast) }
  moreover 
  --{*@{term "?g"} is also a right-inverse of @{term "f"}*} 
  --{*relative to @{term "f ` A"}*} 
  { fix y; assume A: "y \<in> f ` A"
    with \<heartsuit> someI_ex [where P="% x. x \<in> A \<and> y = f x"]
    have "(f o ?g) y = y"
      by (unfold comp_def, fastsimp) }
  ultimately show ?thesis by (rule_tac x="?g" in exI, simp)
qed

lemma fin_inj_on_infi:
  assumes fin_A: "finite (A ::'a set)"
      and infi_B: "infinite (B :: 'b set)"
  shows "\<exists>g::'a \<Rightarrow> 'b. inj_on g A \<and> range g \<subseteq> B"
using fin_A infi_B
proof -
  from fin_A 
       finite_imp_nat_seg_image_inj_on
  obtain n f 
  where "A = (f::nat \<Rightarrow> 'a) ` {i. i < (n::nat)} \<and> inj_on f {i. i < n}"
    by fastsimp
  moreover with inj_on_inj_off obtain g
  where "inj_on (g::'a \<Rightarrow> nat) (f ` {i. i < n})" by blast
  ultimately have "inj_on g A" by fastsimp
  note \<heartsuit> = this
  from infi_B infinite_countable_subset [where S="B"]
  obtain h where "inj (h::nat \<Rightarrow> 'b) \<and> range h \<subseteq> B"
    by fastsimp
  note \<spadesuit> = this
  hence "inj_on h (g ` A)" by (unfold inj_on_def,blast)
  with \<heartsuit> comp_inj_on 
    have "inj_on (h o g) A" by blast
  moreover
  { fix g h; have "range (h o g) \<subseteq> range h"
      by (unfold comp_def, blast) }
  with \<spadesuit> have "range (h o g) \<subseteq> B" by fastsimp 
  ultimately show ?thesis by fastsimp
qed

end
