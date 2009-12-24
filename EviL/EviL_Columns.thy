header{* EviL Column Lemmas *}

theory EviL_Columns
imports EviL_Semantics EviL_Properties
begin

text
{* We now turn to formalizing the concept of a \emph{column} in the Kripke 
   models we have been investigating, and show that \emph{partly EviL} 
   models make true certain lemmas regarding columns, which shall be key in 
   the subsequent model theory that we shall develop. *}

definition 
  col :: "('w,'a,'b) evil_kripke \<Rightarrow> 'w \<Rightarrow> 'w set" where
  "col M w == 
    ((\<Union>X. RBB(M)(X) \<union> (RBB(M)(X))^-1)^*) `` {w}"

text
{* We admit that the above definition is somewhat challenging, 
   but it can be understood by observing the following elementary 
   fact about relations. *}

lemma crazy_Un_equiv:
  "equiv UNIV ((\<Union>i\<in>S. (r i) \<union> (r i)^-1)^*)"
using sym_Un_converse
      sym_UNION [where r="% i. (r i) \<union> (r i)^-1"]
      refl_rtrancl [where r="\<Union>i\<in>S. (r i) \<union> (r i)^-1"] 
      sym_rtrancl [where r="\<Union>i\<in>S. (r i) \<union> (r i)^-1"]
      trans_rtrancl [where r="\<Union>i\<in>S. (r i) \<union> (r i)^-1"]
  by (unfold equiv_def, blast)

text
{* This means evidently that @{term "col M w"} is an
   \emph{equivalence class}, and by the properties of
   our definition it is a parition on the 
   \emph{universe} of possible worlds, regardless of 
   whether they happen to be in the scope of whatever 
   Kripke model we are worried about.  Intuitively,
   we can think of the above definition as breaking
   up the universe into \emph{connected components} of
   the graph that @{term "RBB(M)"} induces. 
   This has several immediate consequences: *}

lemma col_refl:
  "w \<in> col M w"
using crazy_Un_equiv [where S="UNIV" and r="RBB(M)"]
  and equiv_class_self [where A="UNIV" 
                          and r="\<Union>X. RBB(M)(X) \<union> (RBB(M)(X))^-1"]
by (unfold col_def,simp)

lemma col_mem_eq:
  "(v \<in> col M w) = (col M v = col M w)"
proof
  let ?R = "(\<Union>X. RBB(M)(X) \<union> (RBB(M)(X))^-1)^*"
    assume "v \<in> col M w"
    with crazy_Un_equiv [where S="UNIV" and r="RBB(M)"]
         eq_equiv_class_iff [where A="UNIV"
                             and r="?R"]
    show "col M v = col M w" by (unfold col_def, blast)
  next assume "col M v = col M w"
    with col_refl show "v \<in> col M w" by fast
qed

text
{* The previous lemma weakens to the following equality: *}

lemma weak_col_mem_eq:
  "(v \<in> col M w) = (w \<in> col M v)"
proof -
  from col_mem_eq
    have "(v \<in> col M w) = (col M v = col M w)" .
  moreover from col_mem_eq 
    have "(w \<in> col M v) = (col M w = col M v)" .
  ultimately show ?thesis by auto
qed

text
{* Next, we show, for partly EviL Kripke models, if
   @{term "w \<in> W(M)"} then @{term "col M w \<subseteq> W(M)"} *}

lemma (in partly_EviL) mem_col_subseteq:
  "(w \<in> W(M)) =  (col M w \<subseteq> W(M))"
proof -
  from col_refl have 
    "col M w \<subseteq> W(M) \<Longrightarrow> w \<in> W(M)" by fastsimp
  moreover
  { assume \<heartsuit>: "w \<in> W(M)"
    fix p; let ?R = "\<Union>X. RBB(M)(X) \<union> (RBB(M)(X))^-1"
    --"The idea is to pick an arbitrary element of the column"
    assume "p \<in> col M w"
    hence "(w,p) \<in> (?R)^*" by (simp add: col_def)
    --"And show set membership:"
    hence "p \<in> W(M)"
    proof(induct rule: rtrancl_induct)
    --{*We proceed by induction\ldots*}
      case base
        from \<heartsuit> show ?case by simp
      next case (step p z)
       with prop0 show "z \<in> W(M)" by fast
    qed }
  ultimately show ?thesis by fast
qed

text
{* We now turn to proving a central equality regarding
   valuation functions for partly EviL Kripke models
   over columns, and give a equivalent
   formulation that is our preference. *}

lemma (in partly_EviL) col_V_eqp:
  shows "V(M)(w) = \<Union> V(M) `(col M w)"
proof -
  from col_refl have "V(M)(w) \<subseteq> \<Union> V(M) `(col M w)"
    by fastsimp
  moreover
  { fix p; assume "p \<in> \<Union> V(M) `(col M w)"
    hence "p \<in> V(M)(w)"
    proof(unfold col_def,unfold Image_def,clarify)
      --"After clarification, this is what we need to prove:"
      let ?R = "\<Union>X. RBB(M)(X) \<union> (RBB(M)(X))^-1"
      fix v; assume "(w,v) \<in> ?R^*" and "p \<in> V(M)(v)"
      thus "p \<in> V(M)(w)"
      proof (rule converse_rtrancl_induct)
        --{*The trick here is to use \emph{converse} induction*}
        --{*@{thm [source] converse_rtrancl_induct} states:*}
        --{*@{thm converse_rtrancl_induct}*}
        --"we shall focus on the inductive step"
        fix y z; assume "p \<in> V(M)(z)" 
                    and "(y,z) \<in> ?R"
        moreover from prop5 have 
        "\<forall> X. (y,z) \<in> (RBB(M)(X))^-1
                \<longrightarrow> V(M)(z) = V(M)(y)"
        and
        "\<forall> X. (y,z) \<in> (RBB(M)(X))
                \<longrightarrow> V(M)(z) = V(M)(y)" 
        by (blast)+
        ultimately show "p \<in> V(M)(y)" by fast
      qed
    qed 
  }
  ultimately show ?thesis by fast
qed

lemma (in partly_EviL) col_V_eq:
  assumes "v \<in> col M w"
  shows "V(M)(w) = V(M)(v)"
using assms
proof -
  from assms col_mem_eq [where M="M"]
    have "col M v = col M w" by auto
  moreover from col_V_eqp
  have "V(M)(w) = \<Union> V(M) `(col M w)" 
   and "V(M)(v) = \<Union> V(M) `(col M v)" by blast+
  ultimately show ?thesis by simp
qed

text
{* Finally, the other main lemma we present here regards visibility with
   @{term "RB(M)(X)"} and columns. We also give two equivalent
   formulations; once again we prefer the second formulation.  *}

lemma (in partly_EviL) col_RB_eqp:
  "(w,v) \<in> RB(M)(X) = (\<forall>u \<in> col M v. (w,u) \<in> RB(M)(X))"
proof -
  from col_refl 
  have "\<forall>u \<in> col M v. (w,u) \<in> RB(M)(X) \<Longrightarrow> (w,v) \<in> RB(M)(X)"
    by fastsimp
  moreover
  { fix u; let ?R = "\<Union>X. RBB(M)(X) \<union> (RBB(M)(X))^-1"
    assume "u \<in> (col M v)"
    hence "(v,u) \<in> ?R^*" by (unfold col_def, simp)
    moreover assume "(w,v) \<in> RB(M)(X)"
    ultimately have "(w,u) \<in> RB(M)(X)"
    proof (rule rtrancl_induct)
      --"This time, the proof proceeds by ordinary induction"
      --"As usual, we focus on the inductive step"
      fix y z; assume "(w,y) \<in> RB(M)(X)" and "(y,z) \<in> ?R"
      moreover with prop7 have 
        "\<forall>Y. (y,z) \<in> (RBB(M)(Y))^-1
                \<longrightarrow> ((w,z) \<in> RB(M)(X))"
        and
        "\<forall>Y. (y,z) \<in> (RBB(M)(Y))
                \<longrightarrow> ((w,z) \<in> RB(M)(X))"
        by blast+
      ultimately show "(w,z) \<in> RB(M)(X)" by fast
    qed
  }
  ultimately show ?thesis by fast
qed

lemma (in partly_EviL) col_RB_eq:
assumes "v \<in> col M u"
  shows "(w,v) \<in> RB(M)(X) = ((w,u) \<in> RB(M)(X))"
using assms
proof -
  from assms col_mem_eq [where M="M"]
    have "col M v = col M u" by auto
  moreover 
  from col_RB_eqp
  have "(w,v) \<in> RB(M)(X) 
          = (\<forall>u \<in> col M v. (w,u) \<in> RB(M)(X))" 
   and "(w,u) \<in> RB(M)(X) 
          = (\<forall>v \<in> col M u. (w,v) \<in> RB(M)(X))" 
   by blast+
  ultimately show ?thesis by simp
qed

text
{* All of the above results suggest that columns are
   irreducible in at least three different ways.  The
   following lemmas express this: *}

lemma (in partly_EviL) col_W_irr:
  shows "(\<exists>u \<in> col M v. u \<in> W(M))
       = (\<forall>u \<in> col M v. u \<in> W(M))"
proof -
  from col_refl
  have "\<forall>u \<in> col M v. u \<in> W(M)
    \<Longrightarrow> \<exists>u \<in> col M v. u \<in> W(M)" 
    by fastsimp
  moreover
  { assume "\<exists>u \<in> col M v. u \<in> W(M)"
    from this obtain u where
        "u \<in> col M v" and \<heartsuit>: "u \<in> W(M)" 
          by fastsimp
    with col_mem_eq [where w="v"] have
        "col M u = col M v" by auto
    moreover from col_mem_eq [where w="u"] have
        "\<forall>t \<in> col M u. col M t = col M u" by auto
    ultimately have
        "\<forall>t \<in> col M v. col M t = col M u" by blast
    moreover from \<heartsuit> mem_col_subseteq have 
         "col M u \<subseteq> W(M)" by auto
    moreover note col_refl
    ultimately have "\<forall>t \<in> col M v. t \<in> W(M)" by fastsimp
  }
  ultimately show ?thesis by fast
qed

lemma (in partly_EviL) col_V_irr:
  shows "(\<exists>u \<in> col M v. V(M)(u)(p))
       = (\<forall>u \<in> col M v. V(M)(u)(p))"
proof -
  from col_refl
  have "\<forall>u \<in> col M v. V(M)(u)(p)
    \<Longrightarrow> \<exists>u \<in> col M v. V(M)(u)(p)" 
     by fastsimp
  moreover
  { assume "\<exists>u \<in> col M v. V(M)(u)(p)"
    from this obtain u where
        "u \<in> col M v" and \<heartsuit>: "V(M)(u)(p)" 
          by fastsimp
    with col_mem_eq [where w="v"] have
        "col M u = col M v" by auto
    moreover from col_mem_eq [where w="u"] have
        "\<forall>t \<in> col M u. col M t = col M u" by auto
    ultimately have
        "\<forall>t \<in> col M v. col M t = col M u" by blast
    moreover from col_V_eqp have
        "\<forall>t \<in> col M v. V(M)(t) = \<Union>V(M) ` col M t"
    and "V(M)(u) = \<Union>V(M) ` col(M)(u)"
        by blast+
    moreover note \<heartsuit>
    ultimately have "\<forall>t \<in> col M v. V(M)(t)(p)" by fastsimp
  }
  ultimately show ?thesis by fast
qed

lemma (in partly_EviL) col_RB_irr:
  shows "(\<exists>u \<in> col M v. (w,u) \<in> RB(M)(X)) 
       = (\<forall>u \<in> col M v. (w,u) \<in> RB(M)(X))"
proof -
  from col_refl 
  have "\<forall>u \<in> col M v. (w,u) \<in> RB(M)(X) 
    \<Longrightarrow> \<exists>u \<in> col M v. (w,u) \<in> RB(M)(X)"
    by fastsimp
  moreover
  { assume "\<exists>u \<in> col M v. (w,u) \<in> RB(M)(X)"
    from this obtain u where 
      "u \<in> col M v" and \<heartsuit>:"(w,u) \<in> RB(M)(X)" 
        by fastsimp
    with col_mem_eq [where M="M"]
      have "col M v = col M u" by fastsimp
    moreover 
    from \<heartsuit> col_RB_eqp 
    have "\<forall>v \<in> col M u. (w, v) \<in> RB(M)(X)" by fast
    ultimately 
    have "\<forall>u \<in> col M v. (w, u) \<in> RB(M)(X)" by fast
  }
  ultimately show ?thesis by fast
qed

end