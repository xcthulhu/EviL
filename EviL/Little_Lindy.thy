header{* Finitary Lindenbaum Constructions *}

theory Little_Lindy
imports ClassAxClass Set_to_List
begin

no_notation (in ClassAx)
"op |"  (infixr "\<or>" 30) and
Not  ("\<not> _" [40] 40)

text
{* We first define \emph{pseudo-negation}, which
   is essential to the finite Lindenbaum construction. *}

definition (in ClassAx) pneg :: "'a \<Rightarrow> 'a" ("\<sim> _" [40] 40) where
"(\<sim> \<phi>) = (if (\<exists> \<psi>. (\<not> \<psi>) = \<phi>) then (SOME \<psi>. (\<not> \<psi>) = \<phi>) else \<not> \<phi>)"

text
{* We now turn to proving \emph{tertium non datur} for pseudo
   negation, as well as logical equivalence with negation. *}

lemma (in ClassAx) pneg_tnd: "\<turnstile> \<sim> \<phi> \<or> \<phi>"
proof cases
  assume "\<exists> \<psi>. (\<not> \<psi>) = \<phi>"
  -- "For clarification, the @{thm [source] someI_ex} states: @{thm someI_ex}"
  with someI_ex [where P="% \<psi> . (\<not> \<psi>) = \<phi>"] 
       pneg_def [where \<phi>="\<phi>"]
     have "(\<not> \<sim> \<phi>) = \<phi>" by fastsimp
  moreover from dblneg1 have "\<turnstile> \<not> \<sim> \<phi> \<or> \<sim> \<phi>" .
  with disj_comm mp have "\<turnstile> \<sim> \<phi> \<or> \<not> \<sim> \<phi>" by blast
  ultimately show ?thesis by simp

  next assume "~ (\<exists>\<psi>. (\<not> \<psi>) = \<phi>)"
  with pneg_def [where \<phi>="\<phi>"]
     have "(\<sim> \<phi>) = (\<not> \<phi>)" by fastsimp
  moreover from dblneg1 have "\<turnstile> \<not> \<phi> \<or> \<phi>" .
  ultimately show ?thesis by simp 
qed

lemma (in ClassAx) pneg_negimpI: "\<turnstile> \<not> \<phi> \<rightarrow> \<sim> \<phi>"
  by (blast intro: pneg_tnd disj_comm mp)

lemma (in ClassAx) pneg_negimpII: "\<turnstile> \<sim> \<phi> \<rightarrow> \<not> \<phi>"
proof cases
  assume a: "\<exists>\<psi>. (\<not> \<psi>) = \<phi>"
  then have "(\<sim> \<phi>) = (SOME \<psi>. (\<not> \<psi>) = \<phi>)"
    by (simp add: pneg_def)
  with a 
       someI_ex [where P="% \<psi>. (\<not> \<psi>) = \<phi>"] 
  have "(\<not> (\<sim> \<phi>)) = \<phi>" by simp
  with dblneg1 have "\<turnstile> \<not> \<not> \<phi> \<rightarrow> \<not> \<sim> \<phi>" 
      by simp
  with ax3 [where \<phi>="\<not> \<phi>"
              and \<psi>="\<sim> \<phi>"] 
  show ?thesis by (blast intro: mp)
  next assume b: "~ (\<exists>\<psi>. (\<not> \<psi>) = \<phi>)"
  then have "(\<sim> \<phi>) = (\<not> \<phi>)"
       by (simp add: pneg_def)
  with  refl show ?thesis
    by simp
qed

text
{* The following lemma is critical to the
   consistency proof of the Lindenbaum construction. *}

lemma (in ClassAx) cnst:
  assumes \<heartsuit>: "~ (\<Gamma> :\<turnstile> \<psi>)"
  shows "~ (\<phi> # \<Gamma> :\<turnstile> \<psi>) \<or> ~ ((\<sim> \<phi>) # \<Gamma> :\<turnstile> \<psi>)"
  using \<heartsuit>
proof -
  { assume a: "\<phi> # \<Gamma> :\<turnstile> \<psi>" 
       and b: "(\<sim> \<phi>) # \<Gamma> :\<turnstile> \<psi>"
    from a undisch have "\<Gamma> :\<turnstile> \<phi> \<rightarrow> \<psi>" by simp
   
    moreover from b undisch have "\<Gamma> :\<turnstile> \<sim> \<phi> \<rightarrow> \<psi>" 
      by simp
   
    moreover from pneg_tnd have "\<turnstile> (\<sim> \<phi>) \<or> \<phi>" .
    with lift have "\<Gamma> :\<turnstile> (\<sim> \<phi>) \<or> \<phi>" by fast
   
    moreover note cdil [where \<Gamma>="\<Gamma>"]
   
    ultimately have "\<Gamma> :\<turnstile> \<psi>" by blast }
  with \<heartsuit> show ?thesis by fastsimp
qed

text
{* We now turn to giving a general, finitistic Lindenbaum construction.
   The basis for our method is the following observation: finite sets
   always correspond to some list.  Wielding the axiom of choice, we choose
   a suitable representative list.  We then define a primitive recursive
   function, named {} with type @{typ "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"}, which 
   first takes a formula @{term [show_types] "\<psi>::'a"}. It then
   takes a @{term [show_types] "\<phi>::'a"} off the top of the second argument 
   @{term [show_types] "\<Phi>::'a list"} and adds it to the consistently first 
   argument @{term [show_types] "\<Gamma>:: 'a list"} if it may be consistently added 
   without proving @{term "\<psi>"}, and adds @{term "\<sim> \<phi>"} otherwise.  
   The procedure then recurses. *}

primrec (in ClassAx) lind :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "lind \<psi> \<Gamma> [] = \<Gamma>"
 | "lind \<psi> \<Gamma> (\<phi> # \<Phi>) = (let \<phi>' = if ~(\<phi> # \<Gamma> :\<turnstile> \<psi>) 
                                     then \<phi>
                                     else \<sim> \<phi> 
                         in (lind \<psi> (\<phi>' # \<Gamma>) \<Phi>))" 

text
{* We will show the two crucial properties of this construction: 
   (1) either @{term "\<phi>"} or @{term "\<sim> \<phi>"} are present in the final list 
   for all @{term "\<phi> \<in> \<Phi>"} and (2) if @{term "\<Gamma>"} is does not prove @{term "\<psi>"}, 
   then the resulting construction does not prove @{term "\<psi>"}.

   We start by proving several basic lemmas, which help us understand
   the results of a lindenbaum construction. As usual, we frequently
   use universal quantification in the statement of lemmas
   to strengthen inductive hypotheses. *}

lemma (in ClassAx) lind_is_mono:
"\<forall>\<Gamma>. set \<Gamma> \<subseteq> set (lind \<psi> \<Gamma> \<Phi>)"
proof (induct \<Phi>, simp)
  -- "The base case is trivial, so we only show the inductive step"
  fix \<phi> :: "'a"; fix \<Phi> :: "'a list"
  assume indh: "\<forall>\<Gamma>. set \<Gamma> \<subseteq> set (lind \<psi> \<Gamma> \<Phi>)"
  -- "From this assumption, we will show the consequent,"
  --{*where @{term "\<Gamma>"} is arbitrary *}
  { fix \<Gamma> :: "'a list"
    let ?if = "if ~(\<phi> # \<Gamma> :\<turnstile> \<psi>) 
                  then \<phi>
                  else (\<sim> \<phi>)"
    -- "Next, observe these two facts:"
    have a: "set \<Gamma> \<subseteq> set (?if # \<Gamma>)"
      by fastsimp
    have "lind \<psi> \<Gamma> (\<phi> # \<Phi>) = lind \<psi> (?if # \<Gamma>) \<Phi>" by simp
    with indh have b: "set (?if # \<Gamma>) \<subseteq> set (lind \<psi> \<Gamma> (\<phi> # \<Phi>))"
      by fastsimp
    --{*With these two facts, we can show, for any @{term "x"},*}
    --{*that @{term "x \<in> set (lind \<psi> \<Gamma> (\<phi> # \<Phi>))"} *}
    { fix x :: "'a"; assume "x \<in> set \<Gamma>"
      with a have "x \<in> set (?if # \<Gamma>)" by fast
      with b have "x \<in> set (lind \<psi> \<Gamma> (\<phi> # \<Phi>))" by fast }
    hence "set \<Gamma> \<subseteq> set (lind \<psi> \<Gamma> (\<phi> # \<Phi>))" by fast }
  -- "This suffices to prove the theorem"
  thus "\<forall>\<Gamma>. set \<Gamma> \<subseteq> set (lind \<psi> \<Gamma> (\<phi> # \<Phi>))" by fast
qed

lemma (in ClassAx) lind_is_max:
"\<forall>\<Gamma>. \<forall>\<phi> \<in> set \<Phi>. \<phi> \<in> set (lind \<psi> \<Gamma> \<Phi>) \<or> (\<sim> \<phi>) \<in> set (lind \<psi> \<Gamma> \<Phi>)"
proof (induct \<Phi>, simp)
  -- "We shall only prove the inductive step"
  fix \<chi> :: "'a"; fix \<Phi> :: "'a list"
  assume ind_hyp: "\<forall> \<Gamma>. \<forall>\<phi>\<in>set \<Phi>. \<phi> \<in> set (lind \<psi> \<Gamma> \<Phi>) 
                                   \<or> (\<sim> \<phi>) \<in> set (lind \<psi> \<Gamma> \<Phi>)"
  -- {* First, let @{term "\<Gamma>"} and @{term "\<phi>"} be arbitrary *}
  { fix \<Gamma> :: "'a list"; fix \<phi> :: "'a"
    -- {* Next, let we'll use our previous abbreviation *}
    let ?if = "if ~(\<chi> # \<Gamma> :\<turnstile> \<psi>) 
                   then \<chi>
                   else (\<sim> \<chi>)"
    --{*The following identity will turn out to be crucial *}
    have \<heartsuit>: 
       "lind \<psi> (?if # \<Gamma>) \<Phi> = lind \<psi> \<Gamma> (\<chi> # \<Phi>)" by fastsimp  
    --{*Next, assume the proper domain conditions for @{term "\<phi>"} *}
    assume \<diamondsuit>: "\<phi> \<in> set (\<chi> # \<Phi>)"
    have "\<phi> \<in> set (lind \<psi> \<Gamma> (\<chi> # \<Phi>)) 
          \<or> (\<sim> \<phi>) \<in> set (lind \<psi> \<Gamma> (\<chi> # \<Phi>))"
    proof cases
       assume "\<phi> \<in> set \<Phi>"
       with ind_hyp have 
        "\<phi> \<in> set (lind \<psi> (?if # \<Gamma>) \<Phi>) 
         \<or> (\<sim> \<phi>) \<in> set (lind \<psi> (?if # \<Gamma>) \<Phi>)" by fast
       with \<heartsuit> show ?thesis by fastsimp
      next 
       assume "\<phi> \<notin> set \<Phi>"
       with \<diamondsuit> have "\<phi> = \<chi>" by (induct \<Phi>, fastsimp+)
       hence "\<phi> = ?if \<or> (\<sim> \<phi>) = ?if" by fastsimp
       moreover have "?if \<in> set (?if # \<Gamma>)" by fastsimp
       with \<heartsuit> lind_is_mono have
        "?if \<in> set (lind \<psi> \<Gamma> (\<chi> # \<Phi>))" by fastsimp
       ultimately show ?thesis by fastsimp
    qed }
  thus 
  "\<forall>\<Gamma>. \<forall>\<phi>\<in>set (\<chi> # \<Phi>). \<phi> \<in> set (lind \<psi> \<Gamma> (\<chi> # \<Phi>)) 
                        \<or> (\<sim> \<phi>) \<in> set (lind \<psi> \<Gamma> (\<chi> # \<Phi>))"
   by fast
qed

lemma (in ClassAx) lind_is_bounded:   
  assumes pneg_closed: "(\<forall> \<phi> \<in> set \<Phi>. (\<sim> \<phi>) \<in> set \<Phi>)"
    shows "\<forall> \<Gamma>. set (lind \<psi> \<Gamma> \<Phi>) \<subseteq> set \<Gamma> \<union> set \<Phi>"
using pneg_closed
proof -
    -- "We cannot see how to perform this proof through direct"
    -- "induction, so we shall prove it a little, more obliquely." 
    -- "Observe the following statement:"
    let ?pnegset = "% \<Phi> . {\<phi>. \<exists> \<psi> . \<phi> = (\<sim> \<psi>) \<and> \<psi> \<in> set \<Phi>}" 
    from pneg_closed have "?pnegset \<Phi> \<subseteq> set \<Phi>" by fastsimp
    -- "This inspires an inductive proof which may be performed"
  moreover
    have "\<forall> \<Gamma>. set (lind \<psi> \<Gamma> \<Phi>) \<subseteq> set \<Gamma> \<union> set \<Phi> \<union> ?pnegset \<Phi>"
      proof (induct \<Phi>, simp)
        fix \<chi> :: "'a"; fix \<Phi> :: "'a list"
        assume ind_hyp: 
          "\<forall>\<Gamma>. set (lind \<psi> \<Gamma> \<Phi>) \<subseteq> set \<Gamma> \<union> set \<Phi> \<union> ?pnegset \<Phi>"
        --{*As usual, we will show for @{term "\<Gamma>"} arbitrary*}
        { fix \<Gamma> :: "'a list"
          from ind_hyp have
          "set (lind \<psi> \<Gamma> (\<chi> # \<Phi>)) \<subseteq> 
                set \<Gamma> \<union> set (\<chi> # \<Phi>) \<union> ?pnegset (\<chi> # \<Phi>)"
            by fastsimp }

        thus 
         "\<forall>\<Gamma>. set (lind \<psi> \<Gamma> (\<chi> # \<Phi>)) \<subseteq> 
               set \<Gamma> \<union> set (\<chi> # \<Phi>) \<union> ?pnegset (\<chi> # \<Phi>)"
           by fast
      qed
    ultimately show ?thesis by blast
qed

text
{* We now turn to perhaps the key lemma regarding
   Lindenbaum constructions: they preserve consistency! *}

lemma (in ClassAx) lind_is_cnst:
  "\<forall>\<Gamma>. ~ (\<Gamma> :\<turnstile> \<psi>) \<longrightarrow> ~ (lind \<psi> \<Gamma> \<Phi> :\<turnstile> \<psi>)"
proof (induct \<Phi>, simp)
   -- "As expected, all we prove is the inductive step."
   fix \<psi> \<chi> :: "'a"; fix \<Phi> :: "'a list"
   assume ind_hyp: "\<forall>\<Gamma>. ~ (\<Gamma> :\<turnstile> \<psi>) \<longrightarrow> ~ (lind \<psi> \<Gamma> \<Phi> :\<turnstile> \<psi>)"
   --{* We shall show the statement of the theorem where @{term "\<Gamma>"} is free *}
   { fix \<Gamma> :: "'a list"
     let ?if = "if ~(\<chi> # \<Gamma> :\<turnstile> \<psi>) 
                   then \<chi>
                   else (\<sim> \<chi>)"
     -- "We will need this key fact"
     have key: "lind \<psi> \<Gamma> (\<chi> # \<Phi>) = lind \<psi> (?if # \<Gamma>) \<Phi>" by simp
     -- {* From this, we turn to completing the proof *}
     assume \<heartsuit>: "~ (\<Gamma> :\<turnstile> \<psi>)" 
     have "~ (lind \<psi> \<Gamma> (\<chi> # \<Phi>) :\<turnstile> \<psi>)"
     proof cases
       assume a: "\<chi> # \<Gamma> :\<turnstile> \<psi>"
       with \<heartsuit> cnst have 
         "~ ((\<sim> \<chi>) # \<Gamma> :\<turnstile> \<psi>)" by fastsimp
       with ind_hyp have
         "~ (lind \<psi> ((\<sim> \<chi>) # \<Gamma>) \<Phi> :\<turnstile> \<psi>)" by blast
       with a key show ?thesis by fastsimp
      next 
       assume b: "~(\<chi> # \<Gamma> :\<turnstile> \<psi>)"
       with ind_hyp have 
         "~ (lind \<psi> (\<chi> # \<Gamma>) \<Phi> :\<turnstile> \<psi>)" by blast
       with b key show ?thesis by fastsimp
      qed }
   thus " \<forall>\<Gamma>. ~ (\<Gamma> :\<turnstile> \<psi>) \<longrightarrow> ~ (lind \<psi> \<Gamma> (\<chi> # \<Phi>) :\<turnstile> \<psi>)" by fast
qed

text
{* We now give a predicate for atoms, which are maximally 
   consistent sets relative to a finite set @{term "\<Phi>"}.  We 
   shall prove that they contain a formula @{term "\<phi> \<in> \<Phi>"}
   if and only if they deduce that formula. While we are at it,
   we shall prove that in the same context, 
   @{term "(\<phi> \<notin> \<Gamma>) = (\<sim> \<phi> \<in> \<Gamma>)"} *}

definition (in ClassAx) 
Atoms :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" ("At") where
"At \<Phi> \<Gamma> \<equiv>   \<Gamma> \<subseteq> \<Phi>
            \<and> (\<forall>\<phi> \<in> \<Phi>. \<phi> \<in> \<Gamma> \<or> (\<sim> \<phi>) \<in> \<Gamma>)
            \<and> ~(list \<Gamma> :\<turnstile> \<bottom>)"

lemma (in ClassAx) coincidence:
assumes A: "finite \<Phi>"
    and B: "\<Gamma> \<in> At(\<Phi>)"
    and C: "\<phi> \<in> \<Phi>"
    and D: "P (\<sim> \<phi>) = (~ P \<phi>)"
shows "(\<phi> \<in> \<Gamma>) = (list \<Gamma> :\<turnstile> \<phi>)"
  and "P \<phi> = (list \<Gamma> :\<turnstile> \<phi>) \<Longrightarrow> P (\<sim> \<phi>) = (list \<Gamma> :\<turnstile> \<sim> \<phi>)"
using A B C D
proof -
  --"We shall first make some observations:"
  from A B C
       mem_def [where x="\<Gamma>"
                  and S="At(\<Phi>)"]
       Atoms_def [where \<Gamma>="\<Gamma>" 
                    and \<Phi>="\<Phi>"]
  have "\<Gamma> \<subseteq> \<Phi>" 
   and E: "\<phi> \<in> \<Gamma> \<or> (\<sim> \<phi>) \<in> \<Gamma>"
   and F: "~(list \<Gamma> :\<turnstile> \<bottom>)"
         by fastsimp+
  with A finite_subset [where A="\<Gamma>"
                          and B="\<Phi>"]
       set_list [where A="\<Gamma>"]
  have G: "\<Gamma> = set (list \<Gamma>)" by fastsimp
 
 --"Our coincidence lemma has two statements; here is the first:"
  show H: "(\<phi> \<in> \<Gamma>) = (list \<Gamma> :\<turnstile> \<phi>)"
  proof -
    --"The first direction in this case is trivial"
    from G lift_elm have "\<phi> \<in> \<Gamma> \<Longrightarrow> list \<Gamma> :\<turnstile> \<phi>"
       by blast
    --"The other direction is evidently more challenging"
    moreover
    { assume \<heartsuit>: "list \<Gamma> :\<turnstile> \<phi>"
      have "\<phi> \<in> \<Gamma>"
      proof -
        --"The proof proceeds by contradiction:"
        { assume "\<phi> \<notin> \<Gamma>"
          with E have "(\<sim> \<phi>) \<in> \<Gamma>" by fastsimp
          with G lift_elm have "list \<Gamma> :\<turnstile> \<sim> \<phi>" by blast
          with pneg_negimpII
               lift [where \<Gamma>="list \<Gamma>"]
               lift_mp [where \<Gamma>="list \<Gamma>"]
          have "list \<Gamma> :\<turnstile> \<not> \<phi>" by blast
          with \<heartsuit> lift_mp have "list \<Gamma> :\<turnstile> \<bottom>" by fast
          with F have "False" by fast }
        thus ?thesis by fast
      qed }
    ultimately show ?thesis by blast
  qed

  --"We now turn to the second statement; but we shall first"
  --"make a critical observation:"
  have I: "\<phi> \<notin> \<Gamma> = (list \<Gamma> :\<turnstile> \<sim> \<phi>)"
  proof -
  --"Left to right:"
    { assume "\<phi> \<notin> \<Gamma>"
        with E have "(\<sim> \<phi>) \<in> \<Gamma>" by auto
        with G lift_elm
              have "list \<Gamma> :\<turnstile> \<sim> \<phi>" by blast }
  moreover
  --"Right to left:"
    { assume "\<phi> \<in> \<Gamma>"
         and "list \<Gamma> :\<turnstile> \<sim> \<phi>"
      moreover with G lift_elm 
               have "list \<Gamma> :\<turnstile> \<phi>" by blast
      moreover note F
           pneg_negimpII [where \<phi>="\<phi>"]
           lift [where \<Gamma>="list \<Gamma>"]
           lift_mp [where \<Gamma>="list \<Gamma>"]
      ultimately have "False" by blast }
    ultimately show ?thesis by auto
  qed

  --"This is enough to finally show the second statement:"
  assume "P \<phi> = (list \<Gamma> :\<turnstile> \<phi>)"
  with D H have "P (\<sim> \<phi>) = (\<phi> \<notin> \<Gamma>)" by simp
  with I show "P (\<sim> \<phi>) = (list \<Gamma> :\<turnstile> (\<sim> \<phi>))" by simp
qed

text
{* We finally turn to presenting the finitary Lindenbaum Lemma. 
   It is in terms of 
   atoms that we shall phrase the primary result we have been leading up to: *}

lemma (in ClassAx) little_lindy:
  assumes A: "finite \<Phi>"
      and B: "\<forall>\<phi> \<in> \<Phi>. (\<sim> \<phi>) \<in> \<Phi>"
      and C: "\<Gamma> \<subseteq> \<Phi>"
      and D: "~(list \<Gamma> :\<turnstile> \<psi>)" 
    shows "\<exists> \<Gamma>'. At \<Phi> \<Gamma>'
                 \<and> \<Gamma> \<subseteq> \<Gamma>'
                 \<and> ~(list \<Gamma>' :\<turnstile> \<psi>)"
using A B C D
proof -
  from A C finite_subset have 
     "finite \<Gamma>" by fastsimp
  with set_list [where A="\<Gamma>"] have
     E: "\<Gamma> = set (list \<Gamma>)" by auto
  from A set_list [where A="\<Phi>"] have
     F: "\<Phi> = set (list \<Phi>)" by auto
  let ?lindy = "set (lind \<psi> (list \<Gamma>) (list \<Phi>))" 
  from set_of_list_is_finite have
     "finite ?lindy" by fastsimp
  with set_list [where A="?lindy"] have
     G: "?lindy = set (list ?lindy)" by auto

  -- {* We have many things to prove: *}
  from B C E F 
       lind_is_bounded [where \<Phi>="list \<Phi>"]
  have I: "?lindy \<subseteq> \<Phi>" 
    by blast

  from F lind_is_max 
  have II: "\<forall>\<phi> \<in> \<Phi>. \<phi> \<in> ?lindy \<or> (\<sim> \<phi>) \<in> ?lindy"
    by fastsimp
  
  from D G
       lind_is_cnst [where \<Phi>="list \<Phi>"]
       lift_eq [where \<Gamma>="lind \<psi> (list \<Gamma>) (list \<Phi>)" 
                  and \<Psi>="list ?lindy"]
  have III: "~ (list ?lindy :\<turnstile> \<psi>)" 
    by blast

  from III
       expls [where \<phi>="\<psi>"]
       lift  [where \<Gamma>="list ?lindy"]
       lift_mp [where \<Gamma>="list ?lindy"]
  have IV: "~ (list ?lindy :\<turnstile> \<bottom>)" 
    by blast
  
  from E
       lind_is_mono [where \<psi>="\<psi>"
                       and \<Phi>="list \<Phi>"]
  have V: "\<Gamma> \<subseteq> ?lindy"
    by blast

  from I II IV 
       Atoms_def [where \<Phi>="\<Phi>"
                   and \<Gamma>="?lindy"]
  have VI: "At \<Phi> ?lindy" by fastsimp

  from III V VI show ?thesis by fastsimp
qed

end