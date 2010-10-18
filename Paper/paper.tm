<TeXmacs|1.0.7.2>

<style|acmconf>

<\body>
  <doc-data|<doc-title|Epistemic Logics of
  Argument>|<doc-author-data|<author-name|Matthew P. Wampler-Doty>>>

  <\abstract>
    In <cite|van_benthem_reflectionsepistemic_1991>, Johan van Benthem
    proposed a research program for logic of <with|font-shape|italic|explicit
    knowledge>. \ Two efforts have since emerged with proposals for logic of
    explicit knowledge: the <with|font-shape|italic|Dynamics of Awareness>
    <cite|van_benthem_inference_2009> and
    <with|font-shape|italic|Justification Logic>
    <cite|artemov_introducing_2005>. \ The purpose of this paper is to
    propose novel, argument based semantics for various modal logics related
    to these previous efforts, for use in reasoning about knowledge bases.
    \ We conclude with an application to naturalized epistemology. \ The
    results in this paper are based on previous work carried out in (FIXME).
  </abstract>

  <section|Introduction<label|intro>>

  The modern tradition in epistemic logic is to assume knowledge modalities
  conform to the <math|S5> axiom schema. \ As noted in
  <cite|halpern_set-theoretic_1999|rubinstein_modeling_1998>, the semantics
  of <math|S5> knowledge correspond exactly to partitioning a collection of
  situations into <with|font-shape|italic|information sets>, which is the
  tradition in game theory and decision theory. \ While it is not commonly
  acknowledged in epistemic logic, economists and philosophers accept that
  traditional decision theory is externalist and behaviourist in
  nature<\footnote>
    An early essay by Amartya Sen on the philosophical foundations of
    traditional decision theory makes the behaviorist reading of decision
    theory clear <cite|sen_behaviour_1973>. \ Kaushik Basu also discusses the
    behaviorist nature of decision theory
    <cite-detail|basu_revealed_1980|pgs. 53--54>. \ Finally, Donald Davidson
    appeals to decision theory to motivate an externalist epistemology in
    <cite|davidson_could_1995>.
  </footnote>.

  \;

  In <cite|van_benthem_reflectionsepistemic_1991>, Johan van Benthem proposed
  a research program to find logics for explicit knowledge, providing the
  first suggestion of an internalist perspective on epistemic logic.
  \ Subsequently, Sergei Artemov and Elena Nogina proposed a logic of
  explicit justification, which has come to be known as
  <with|font-shape|italic|Justification Logic> (JL)
  <cite|artemov_introducing_2005>, based on Artemov's
  <with|font-shape|italic|Logic of Proofs> <cite|artemov_logic_1994>. \ While
  the original semantics of JL was interpretability into Peano Arithmetic,
  Melvin Fitting proposed Kripke semantics for JL in
  <cite|fitting_logic_2005>. \ Recently, Fernando Velázquez-Quesada and Johan
  van Benthem have developed a simpler framework for explicit epistemics in
  <cite|van_benthem_inference_2009>, entitled the
  <with|font-shape|italic|Dynamics of Awareness>. \ This work was based on
  Joseph Halpern and Ronald Fagin's original
  <with|font-shape|italic|Awareness Logic> <cite|fagin_belief_1987>.

  \;

  In this essay we repurpose various modal logics to take on an internalist
  reading. \ The concept of a <with|font-shape|italic|knowledge base>, from
  which beliefs may be implicitly deduced, will play a crucial role in our
  discussion. \ We propose this as an avenue for representing foundationalist
  perspectives on epistemology in epistemic logic. \ Our philosophical
  motivation is taken from two sources. \ The first is Vincent Hendricks in
  <cite|hendricks_mainstream_2006>, where he characterizes the principal of
  <em|logical omniscience> for implicit knowledge in epistemic
  logic<\footnote>
    We have modified Hendricks notation here slightly to match our own.
  </footnote>:

  <\quote-env>
    <em|Whenever an agent <math|\<Xi\>> knows all of the formulae in
    <math|<with|math-font|cal|A>>, and <math|\<phi\>> follows logically from
    <math|<with|math-font|cal|A>>, then <math|\<Xi\>> [implicitly] knows
    <math|\<phi\>>.>
  </quote-env>

  We will design our semantics such that ``<math|\<box\>\<phi\>>'' may be
  equated with ``<math|\<phi\>> follows logically from a knowledge base
  <math|<with|math-font|cal|A>>,'' which is sometimes written as
  <math|\<phi\>\<in\>Cn(<with|math-font|cal|A>)> in the artificial
  intelligence literature. \ Our second inspiration comes from what Hilary
  Kornblith calls the <with|font-shape|italic|the arguments on paper thesis>
  <cite|kornblith_beyond_1980>, which he feels characterizes apsychological,
  internalist theories of knowledge:

  <\quote-env>
    Let us suppose that, for any person, it is possible, at least in
    principle, to list all of the propositions that person believes. \ The
    arguments-on-paper thesis is just the view that a person has a justified
    belief that a particular proposition is true just in case that
    proposition appears on the list of propositions that person believes, and
    either it requires no argument, or a <em|good argument> can be given for
    it which takes as premises certain other propositions on the list.
  </quote-env>

  Kornblith asserts that foundationalism and coherentism vie for accounts of
  a ``good argument'' in the above thesis. \ He provides an extensive
  bibliography citing proposals for this principle by a number of 20th
  century epistemologists, including figures such as A.J. Ayer and C.I.
  Lewis. \ The rest of Kornblith's paper is devoted to attacking this view
  and proposing a form of naturalized epistemology; we will not address this
  debate here, however.

  \;

  We adopt a arguments-on-paper-thesis perspective on epistemic logic in this
  paper. \ We consider a <with|font-shape|italic|good argument> to be a
  logical derivation from propositions present in a knowledge base. \ In this
  fashion, our \ \ Special attention will be given to
  <with|font-shape|italic|sound derivations>, which will be thought of as a
  form of knowledge. \ In Awareness Logic, we will interpret awareness of a
  formula as membership in a knowledge base. \ We prove completeness for
  basic awareness logic and a hybrid logic extension. \ Logics of multiple
  knowledge bases are also presented: a simplified form of Justification
  Logic, a logic with neighborhood semantics, an a logic with modalities for
  quantifying over knowledge bases. \ We conclude with an application to
  naturalized epistemology found in the psychological literature.

  <section|Basic Explicit Logics of Knowledge Bases>

  <subsection|Awareness Logic<label|awarenesslogic>>

  In this section, we give the explicit semantics to basic awareness logic,
  originally presented in <cite|fagin_belief_1987>, with an additional axiom.
  \ One difference in our presentation is the inclusion of a novel letter and
  a superficial change in notation. \ This work is inspired by the
  developments in van Benthem and Velázquez-Quesada
  <cite|van_benthem_inference_2009>.

  <\definition>
    Let <math|\<Phi\>> be a set of letters and define the language
    <math|<with|math-font|cal|L><rsub|A>(\<Phi\>)> as:

    <\equation*>
      \<phi\> <space|1spc>: :=<space|1spc>p\<in\>\<Phi\><space|1spc>\|<space|1spc>\<circlearrowleft\><space|1spc>\|<space|1spc>\<bot\><space|1spc>\|<space|1spc>\<phi\>\<rightarrow\>\<psi\><space|1spc>\|<space|1spc>\<box\>\<phi\><space|1spc>\|<space|1spc>A:\<phi\><space|1spc>
    </equation*>
  </definition>

  We define the other connectives and modal operators as usual for classical
  modal logics.

  <\definition>
    <label|awarenessmodels>An <strong|awareness model>
    <math|\<bbb-M\>=\<langle\>W,V,R,<with|math-font|cal|A>\<rangle\>> is a
    Kripke model with a valuation <math|V:\<Phi\>\<cup\>{\<circlearrowleft\>}\<rightarrow\>2<rsup|W>>
    and an awareness function <math|<with|math-font|cal|A>:W\<rightarrow\>2<rsup|<with|math-font|cal|L><rsub|A>(\<Phi\>)>>.
    \ We will usually denote <math|<with|math-font|cal|A>(w)> as
    <math|<with|math-font|cal|A><rsub|w>>.

    \;

    Define the semantic entailment relation <math|\<vDash\>> where atomic
    propositions, logical connectives and modality are interpreted as usual.
    \ We employ the following novel definition:

    <\eqnarray*>
      <tformat|<table|<row|<cell|\<bbb-M\>,w\<vDash\>A:
      \<phi\>>|<cell|<with|mode|text|iff>>|<cell|\<phi\>\<in\><with|math-font|cal|A<rsub|w>>>>>>
    </eqnarray*>
  </definition>

  The following definition distinguishes us from previously investigations of
  awareness logic:

  <\definition>
    Define the ``<with|font-series|bold|theory of a model> <math|\<bbb-M\>>''
    as:

    <\equation*>
      Th(\<bbb-M\>)\<assign\>{\<phi\><space|1spc>\|<space|1spc>\<bbb-M\>,v\<vDash\>\<phi\><with|mode|text|
      for all >v\<in\>W}
    </equation*>

    We define the following properties that a model <math|\<bbb-M\>> may
    posses:

    <\description-dash>
      <item*|CSQ><math|\<bbb-M\>,w\<vDash\>\<box\>\<phi\><with|mode|text| iff
      >Th(\<bbb-M\>)\<cup\><with|math-font|cal|A><rsub|w>\<vdash\>\<phi\>>

      <item*|SND><math|\<bbb-M\>,w\<vDash\>\<circlearrowleft\><with|mode|text|
      iff >\<bbb-M\>,w\<vDash\>\<phi\>> for all
      <math|\<phi\>\<in\><with|math-font|cal|A><rsub|w>>
    </description-dash>

    ere <math|\<vdash\>> is any sound logical consequence relation for
    <math|\<vDash\>> with <with|font-series|bold|modus ponens> and
    <with|font-series|bold|reflection> (ie, <math|\<Gamma\>\<vdash\>\<phi\>>
    if <math|\<phi\>\<in\>\<Gamma\>>).
  </definition>

  Intuitively, the <with|font-series|bold|CSQ> asserts that an agent believes
  a formula <math|\<phi\>> if and only if it follows from their knowledge
  base and their background knowledge, represented by <math|Th(\<bbb-M\>)>.
  \ <with|font-series|bold|CSQ> is Vincent Hendrik's principle of logical
  omniscience mentioned in Ÿ<reference|intro>.

  \;

  <with|font-series|bold|SND> asserts that
  <with|mode|math|\<circlearrowleft\>> corresponds to the agent's knowledge
  base being sound. A sound knowledge base will only render true conclusions
  when used in deductions. \ If one equates knowledge with ``The existance of
  a sound deduction'' then <with|mode|math|\<circlearrowleft\>> is a
  mechanism for investigating this notion. \ That is, if
  <math|\<bbb-M\>,w\<vDash\>\<circlearrowleft\>\<wedge\>\<box\>\<phi\>>, this
  is sufficient for the agent (implicitly) <em|knowing> <math|\<phi\>> on the
  basis of <math|<with|math-font|cal|A><rsub|w>>, rather than merely
  believing <math|\<phi\>> on the basis of
  <math|<with|math-font|cal|A><rsub|w>>.

  \;

  Neither <with|font-series|bold|CSQ> nor <with|font-series|bold|SND>
  correspond to simple modally definable properties.

  <big-table|<tabular|<tformat|<table|<row|<cell|<math|\<vdash\>\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>(\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<chi\>)\<rightarrow\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<phi\>\<rightarrow\>\<chi\>>>>|<row|<cell|<math|\<vdash\>((\<phi\>\<rightarrow\>\<bot\>)\<rightarrow\>(\<psi\>\<rightarrow\>\<bot\>))\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>\<box\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<box\>\<phi\>\<rightarrow\>\<box\>\<psi\>>>>|<row|<cell|<math|\<vdash\>A:\<phi\>\<rightarrow\>\<box\>\<phi\>>>>|<row|<cell|<math|\<vdash\>\<circlearrowleft\>\<rightarrow\>\<box\>\<phi\>\<rightarrow\>\<phi\>>>>|<row|<cell|>>|<row|<cell|<tabular|<tformat|<table|<row|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\><space|4spc>\<vdash\>\<phi\>|\<vdash\>\<psi\>>>>>|<cell|<space|6spc>>|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>|\<vdash\>\<box\>\<phi\>>>>>>>>>>>>>>|<label|logic1>An
  awareness logic for <with|font-series|bold|CSQ><math|<rsub|\<vdash\>>> and
  <with|font-series|bold|SND>>

  <\theorem>
    <label|completeness1>Assuming an infinite store of proposition letters
    <math|\<Phi\>>, the logic in Table <reference|logic1> is sound and weakly
    complete for awareness models making true <with|font-series|bold|CSQ> and
    <with|font-series|bold|SND>
  </theorem>

  <\proof>
    Soundness is straightforward, so we will only address completeness.
    \ Assume <math|\<nvdash\>\<psi\>>. \ Consider the finite canonical model
    <math|\<bbb-M\>=\<langle\>W,V,R,<with|math-font|cal|A>\<rangle\>> formed
    of maximally consistent sets of subformulae of <math|\<phi\>> (closed
    under pseudo-negation), as per the modal completeness proofs suggested in
    <cite-detail|boolos_logic_1995|chapter 5>. \ We have that
    <math|\<bbb-M\>,w\<nvDash\>\<psi\>> for some world <math|w>. \ Moreover,
    it is straightforward to verify that <math|\<bbb-M\>> makes true

    <\enumerate-numeric>
      <item><math|W> is finite and <math|<with|math-font|cal|A><rsub|v>> is
      finite for all <math|v\<in\>W>

      <item>if <math|\<bbb-M\>,v\<vDash\>A:\<phi\>> then
      <math|\<bbb-M\>,v\<vDash\>\<box\>\<phi\>>

      <item>if <math|\<bbb-M\>,v\<vDash\>\<circlearrowleft\>> then <math|v R
      v>
    </enumerate-numeric>

    \;

    We next produce a finite bisimular model <math|\<bbb-M\><rprime|'>> which
    makes true (1), (2) and a stronger from of (3):

    \;

    <htab|5mm><tabular|<tformat|<table|<row|<cell|<with|font-series|bold|3<math|<rprime|'>>.>>|<cell|<math|\<bbb-M\><rprime|'>,v\<vDash\>\<circlearrowleft\>>
    iff <math|v R v>>>>>><htab|5mm>

    \;

    To this end define <math|\<bbb-M\><rprime|'>\<assign\>\<langle\>W<rprime|'>,V<rprime|'>,R<rprime|'>,<with|math-font|cal|A><rprime|'>\<rangle\>>
    such that<htab|5mm>

    <\itemize-dot>
      <item><with|mode|math|W<rprime|'>\<assign\>W\<uplus\>W>; furthermore,
      let <math|l,r> be the two canonical injections associated with the
      coproduct <math|W\<uplus\>W>. We denote <math|l(v)> and <math|r(v)> as
      <math|v<rsub|l>> and <math|v<rsub|r>> respectively

      <item><math|V<rprime|'>(p)\<assign\>{v<rsub|l>,v<rsub|r><space|1spc>\|<space|1spc>v\<in\>V(p)}>

      <item><math|R<rprime|'> \<assign\> {(v<rsub|l>,u<rsub|r>),(v<rsub|r>,u<rsub|l>)<space|1spc>\|<space|1spc>v
      R u}\<cup\>{(v<rsub|l>,v<rsub|l>),(v<rsub|r>,v<rsub|r>)<space|1spc>\|<space|1spc>\<bbb-M\>,v\<vDash\>\<circlearrowleft\>}>

      <item><math|<with|math-font|cal|A><rprime|'>(v<rsub|l>)\<assign\><with|math-font|cal|A><rprime|'>(v<rsub|r>)\<assign\><with|math-font|cal|A>(v)><math|>
    </itemize-dot>

    \;

    It is straightforward to verify that <math|\<bbb-M\><rprime|'>> makes
    true the desired properties. \ If we let
    <math|Z\<assign\>{(v,v<rsub|l>),(v,v<rsub|r>)<space|1spc>\|<space|1spc>v\<in\>W}>,
    \ then <math|Z> is a bisimulation between <math|\<bbb-M\>> and
    <math|\<bbb-M\><rprime|'>>. \ Therefore we know there is some
    <math|w\<in\>W> such that <math|\<bbb-M\><rprime|'>,w<rsub|l>\<nvDash\>\<psi\>>
    and <math|\<bbb-M\><rprime|'>,w<rsub|r>\<nvDash\>\<psi\>>.

    \;

    Finally we construct a model <math|\<bbb-M\><rprime|''>> which agrees
    with <math|\<bbb-M\><rprime|'>> for all subformulae of <math|\<psi\>>,
    which makes true <with|font-series|bold|CSQ> and
    <with|font-series|bold|SND>. \ Let <math|\<Lambda\>> be the set of
    proposition letters occuring in <math|\<psi\>>. \ We will make use
    members of <math|\<Phi\>\<backslash\>\<Lambda\>> as <em|nominals>, as per
    the tradition in hybrid logic. \ This is possible since both
    <math|W<rprime|'>> and <math|\<Lambda\>> are finite and <math|\<Phi\>> is
    infinite by hypothesis. \ Let <math|\<iota\>:W\<uplus\>W\<hookrightarrow\>\<Phi\>\<backslash\>\<Lambda\>>
    be an injection assigning a fresh nominal associated with each world in
    <math|\<bbb-M\><rprime|'>>. \ Now define
    <math|\<bbb-M\><rprime|''>\<assign\>\<langle\>W<rprime|''>,V<rprime|''>,R<rprime|''>,<with|math-font|cal|A><rprime|''>\<rangle\>>,
    where:

    \;

    <\with|par-mode|center>
      <tabular|<tformat|<table|<row|<cell|<math|\<bullet\>>>|<cell|<math|W<rprime|''>\<assign\>W<rprime|'>>>|<cell|>|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-display|true|V<rprime|''>(p)\<assign\><choice|<tformat|<table|<row|<cell|V<rprime|'>(p)>|<cell|p\<in\>\<Lambda\>>>|<row|<cell|{v}>|<cell|p=\<iota\>(v)>>|<row|<cell|\<varnothing\>>|<cell|o/w>>>>>>>>>|<row|<cell|<math|\<bullet\>>>|<cell|<math|R<rprime|''>\<assign\>R<rprime|'>>>|<cell|<space|3spc>>|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-font|cal|A><rprime|''><rsub|v>\<assign\>{\<phi\><space|1spc>\|\<phi\>\<in\><with|math-font|cal|A><rprime|'><rsub|v><with|mode|text|
      and <math|\<phi\>> is a subformula of <math|\<psi\>>>}
      \<cup\>{\<neg\>\<iota\>(u)<space|1spc>\|<space|1spc>\<neg\>v
      R<rprime|'> u}>>>>>>
    </with>

    \;

    It is easy to verify that for every subformula <math|\<phi\>> of
    <math|\<psi\>> that <math|\<bbb-M\><rprime|'>,v\<vDash\>\<phi\>> if and
    only if <math|\<bbb-M\><rprime|''>,v\<vDash\>\<phi\>>, hence
    <math|\<bbb-M\><rprime|''>,w<rsub|l>\<nvDash\>\<psi\>>.

    \;

    All that is left to show is that <math|\<bbb-M\><rprime|''>> makes true
    <with|font-series|bold|SND> and <with|font-series|bold|CSQ>.
    \ <math|\<bbb-M\><rprime|''>> has three further properties:

    <\enumerate-roman>
      <item><math|<with|math-font|cal|A><rprime|''><rsub|v>> is finite for
      all worlds <math|v>

      <item> <math|v R<rprime|'> u> if and only if
      <math|\<bbb-M\><rprime|''>,u\<vDash\><big|wedge><with|math-font|cal|A><rprime|''>(v)>

      <item>The logic presented in Table <reference|logic1> is sound for
      <math|\<bbb-M\><rprime|''>>
    </enumerate-roman>

    From (ii) and the fact that <math|\<bbb-M\><rprime|'>> makes true
    (3<math|<rprime|'>>), we have <with|font-series|bold|SND> for
    <math|\<bbb-M\><rprime|''>>.

    \;

    All that is left is to demonstrate <with|font-series|bold|CSQ> for some
    sound logic. \ We will use the logic in Table <reference|logic1> itself.
    \ From (i), (ii), (iii), and the <with|font-shape|italic|deduction
    theorem> for modal logic, we have the following line of reasoning:

    <\align*>
      <tformat|<table|<row|<cell|Th(\<bbb-M\><rprime|''>)\<cup\><with|math-font|cal|A><rprime|''><rsub|v>\<vdash\>\<phi\>>|<cell|\<Longleftrightarrow\>Th(\<bbb-M\><rprime|''>)\<vdash\><big|wedge><with|math-font|cal|A><rprime|''><rsub|v>\<rightarrow\>\<phi\>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><big|wedge><with|math-font|cal|A><rprime|''><rsub|v>\<rightarrow\>\<phi\>\<in\>Th(\<bbb-M\><rprime|''>)>>|<row|<cell|>|<cell|\<Longleftrightarrow\>\<bbb-M\><rprime|''>,u\<vDash\><big|wedge><with|math-font|cal|A><rprime|''><rsub|v>\<rightarrow\>\<phi\><with|mode|text|<with|mode|text|
      for all ><math|u\<in\>W<rprime|''>>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<with|mode|text|
      for all ><math|u\<in\>W<rprime|''>>, if
      >\<bbb-M\><rprime|''>,u\<vDash\><with|math-font|cal|A><rprime|''><rsub|v><with|mode|text|
      then >\<bbb-M\><rprime|''>,u\<vDash\>\<phi\>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<with|mode|text|
      for all ><math|u\<in\>W<rprime|''>>, if >v R <rprime|'>u
      <with|mode|text| then >\<bbb-M\><rprime|''>,u\<vDash\>\<phi\>>>|<row|<cell|>|<cell|\<Longleftrightarrow\>\<bbb-M\><rprime|''>,v\<models\>\<box\>\<phi\>>>>>
    </align*>
  </proof>

  <\remark>
    The logic presented in Table <reference|logic1> is a conservative
    extension of the basic modal logic <math|K>, which means that its
    decision problem is <with|font-family|ss|PSPACE> hard (a lower bound).
    \ Our finitary completeness proof establishes that its complexity is in
    <with|font-family|ss|EXP2-TIME> (an upper bound).
  </remark>

  <subsection|Hybrid Logic>

  The method of the above completeness proof makes implicit use of hybrid
  logic concepts. \ We adapt hybrid logic, first presented in
  <cite|prior_revised_1969> and then formally developed in
  <cite|bull_approach_1970>, and show that it is a complete for reasoning
  about knowledge bases. \ We note that because of the increased expressive
  power of hybrid logic, our completeness theorem is simpler.

  <\definition>
    Let <math|\<Phi\>> be a set of letters and <math|\<Psi\>> a set of
    nominals, and define the language <math|<with|math-font|cal|L><rsub|H>(\<Phi\>,\<Psi\>)>
    as:

    <\equation*>
      \<phi\> <space|1spc>: :=<space|1spc>p\<in\>\<Phi\><space|1spc>\|<space|1spc>i\<in\>\<Psi\><space|1spc>\|<space|1spc>\<bot\><space|1spc>\|<space|1spc>\<phi\>\<rightarrow\>\<psi\><space|1spc>\|<space|1spc>\<box\>\<phi\><space|1spc>\|<space|1spc>A:\<phi\><space|1spc>\|<space|1spc>\<forall\>\<phi\>
    </equation*>
  </definition>

  Our approach in hybrid logic is to employ a universal modality along with
  nominals. \ This framework presents a logic where the agent may reason
  about various labeled scenarios. \ Scenarios may be multiply labeled or not
  labeled at all. \ From these intuitions we have the following definition:

  <\definition>
    <label|hybridsemantics>Let a <with|font-series|bold|hybrid model>
    <math|\<bbb-M\>=\<langle\>W,V,R,<with|math-font|cal|A>,\<ell\>\<rangle\>>
    be an awareness model as in Definition <reference|awarenessmodels>, along
    with a partial labeling function <math|\<ell\>:\<Psi\>\<nrightarrow\>W>

    \;

    The semantics for <math|\<vDash\>> are the same as in Definition
    <reference|awarenessmodels>, only we have

    <\eqnarray*>
      <tformat|<table|<row|<cell|\<bbb-M\>,w\<vDash\>\<forall\>\<phi\>>|<cell|<with|mode|text|iff>>|<cell|\<forall\>v\<in\>W.\<bbb-M\>,v\<vDash\>\<phi\>>>|<row|<cell|\<bbb-M\>,w\<vDash\>i>|<cell|<with|mode|text|iff>>|<cell|\<ell\>(i)=w>>>>
    </eqnarray*>
  </definition>

  The other connectives and operators are defined as usual, although we
  employ a few special shorthands:

  <\definition>
    We employ the following special abbreviations:

    <\eqnarray>
      <tformat|<table|<row|<cell|<with|mode|text|<with|font-shape|right|@>><rsub|i>\<phi\>\<assign\>\<forall\>(i\<rightarrow\>\<phi\>)<space|2spc>>|<cell|\<exists\>\<phi\>\<assign\>\<neg\>\<forall\>\<neg\>\<phi\><space|3spc>>|<cell|\<circlearrowleft\><rsub|i>\<assign\>\<diamondsuit\>i>>>>
    </eqnarray>
  </definition>

  This gives rise to a validity reflecting one of the axioms we saw in
  Ÿ<reference|awarenesslogic>:

  <\equation*>
    \<vDash\>\<circlearrowleft\><rsub|i>\<rightarrow\>\<box\>\<phi\>\<rightarrow\><with|mode|text|<with|font-shape|right|@>><rsub|i>\<phi\>
  </equation*>

  This can be read as ``If the agent's knowledge base is sound at world
  <math|i>, then if they can deduce something from it, it must be true at
  world <math|i>.'' \ In a way, this relativises knowledge to a world
  <math|i>. \ Worlds in epistemic logic might correspond to fantastic,
  pretend scenarios; however, it may be desirable for some philosophers to
  model knowledge about imaginary lands. \ After all, many children ``know''
  a lot about Tolkien's <em|middle earth> or Rowling's <em|Hogwarts> (the
  school Harry Potter attends).

  \;

  The semantics in Definition <reference|hybridsemantics> obviates the
  <with|font-series|bold|SND> principle we previously presented, since there
  is no explicit <with|mode|math|\<circlearrowleft\>> symbol in this setting.
  <with|font-series|bold|CSQ> still makes sense without modification,
  however. \ The following gives a logic for hybrid models making true
  <with|font-series|bold|CSQ>:

  <big-table|<tabular|<tformat|<cwith|8|8|1|2|cell-row-span|1>|<cwith|8|8|1|2|cell-col-span|2>|<cwith|8|8|1|1|cell-halign|c>|<table|<row|<cell|<math|\<vdash\>\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>|<cell|<math|\<vdash\>\<forall\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<forall\>\<phi\>\<rightarrow\>\<forall\>\<psi\>>>>|<row|<cell|<math|\<vdash\>(\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<chi\>)\<rightarrow\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<phi\>\<rightarrow\>\<chi\>>>|<cell|<math|\<vdash\>\<forall\>\<phi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>((\<phi\>\<rightarrow\>\<bot\>)\<rightarrow\>(\<psi\>\<rightarrow\>\<bot\>))\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>|<cell|<math|\<vdash\>\<forall\>\<phi\>\<rightarrow\>\<forall\>\<forall\>\<phi\>>>>|<row|<cell|<math|\<vdash\>\<box\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<box\>\<phi\>\<rightarrow\>\<box\>\<psi\>>>|<cell|<math|\<vdash\>\<exists\>\<phi\>\<rightarrow\>\<forall\>\<exists\>\<phi\>>>>|<row|<cell|<math|\<vdash\>A:\<phi\>\<rightarrow\>\<box\>\<phi\>>>|<cell|<math|\<vdash\>\<forall\>\<phi\>\<rightarrow\>\<box\>\<phi\>>>>|<row|<cell|>|<cell|<math|\<vdash\>i\<rightarrow\>\<phi\>\<rightarrow\><with|mode|text|<with|font-shape|right|@>><rsub|i>\<phi\>>>>|<row|<cell|>|<cell|>>|<row|<cell|<tabular|<tformat|<cwith|1|1|4|4|cell-halign|c>|<table|<row|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\><space|4spc>\<vdash\>\<phi\>|\<vdash\>\<psi\>>>>>|<cell|<space|6spc><with|math-display|true|<math|<frac|\<vdash\>\<phi\>|\<vdash\>\<box\>\<phi\>>>>>|<cell|<space|6spc>>|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>|\<vdash\>\<forall\>\<phi\>>>>>>>>>>|<cell|>>>>>|<label|logic2>A
  hybrid logic for <with|font-series|bold|CSQ>>

  <\theorem>
    Assuming an infinite store of nominals <math|\<Psi\>>, The logic in Table
    <reference|logic2> is sound and weakly complete for all hybrid models
    making true <with|font-series|bold|CSQ>
  </theorem>

  <\proof>
    As before, soundness is trivial. \ Completeness is based on a
    modification of techniques found in <cite-detail|boolos_logic_1995|chapter
    5>. \ Assume that <math|\<nvdash\>\<psi\>> and let
    <math|\<Sigma\><rsub|0>> be the set of subformulae of <math|\<psi\>>, and
    let <math|\<Upsilon\>> be the set of nominals occuring in <math|\<psi\>>.
    \ Define:

    <\align*>
      <tformat|<table|<row|<cell|\<Sigma\><rsub|1>>|<cell|\<assign\>\<Sigma\><rsub|0>\<cup\>{\<forall\>\<phi\><space|1spc>\|<space|1spc>\<box\>\<phi\>\<in\>\<Sigma\><rsub|0>}>>|<row|<cell|\<Sigma\><rsub|2>>|<cell|\<assign\>\<Sigma\><rsub|1>\<cup\>{<with|mode|text|@><rsub|i>\<phi\><space|1spc>,i\<rightarrow\>\<phi\>\|<space|1spc>\<phi\>\<in\>\<Sigma\><rsub|1><space|1spc>&<space|1spc>i\<in\>\<Upsilon\>}>>|<row|<cell|\<Sigma\><rsub|3>>|<cell|\<assign\>\<Sigma\><rsub|2>\<cup\>{\<neg\>\<phi\><space|1spc>\|<space|1spc>\<phi\>\<in\>\<Sigma\><rsub|2>}>>>>
    </align*>

    It is easy to see that <math|\<Sigma\><rsub|3>> is finite and closed
    under subformulae. Now let <with|mode|math|\<bbb-M\>=\<langle\>W,V,R<rsub|\<box\>>,\<sim\><rsub|\<forall\>>,<with|math-font|cal|A>\<rangle\>>
    be the finite cannonical model formed of maximally consistent subsets of
    <math|\<Sigma\><rsub|3>>, where everything is defined as usual, except
    <math|\<sim\><rsub|\<forall\>>>, which is specified as follows:

    <\align*>
      <tformat|<table|<row|<cell|w \<sim\><rsub|\<forall\>>v>|<cell|\<Longleftrightarrow\>((\<forall\>\<phi\>)\<in\>w
      \<Longleftrightarrow\>(\<forall\>\<phi\>)\<in\>v)>>>>
    </align*>

    This model makes true the following properties:

    <\enumerate-roman>
      <item><math|\<sim\><rsub|\<forall\>>> is an equivalence relation

      <item><math|R<rsub|\<box\>>\<subseteq\>\<sim\><rsub|\<forall\>>>

      <item>In each equivalence class specified by
      <math|\<sim\><rsub|\<forall\>>>, there is at most one world making true
      <math|i> for all <math|i\<in\>\<Upsilon\>>
    </enumerate-roman>

    The Truth Lemma for this structure is straightforward to prove. With the
    finitary Lindenbaum Lemma we have that some world <math|w> where
    <math|\<bbb-M\>,w\<nvDash\>\<psi\>>. \ Let
    <math|\<bbb-M\><rprime|'>=\<langle\>W<rprime|'>,V<rprime|'>,R<rsub|\<box\>><rprime|'>,\<sim\><rsub|\<forall\>><rprime|'>,<with|math-font|cal|A><rprime|'>\<rangle\>>
    be the submodel generated by <math|{w}>; we have that
    <math|\<bbb-M\><rprime|'>,w\<nvDash\>\<psi\>>
    <cite-detail|blackburn_modal_2001|see chapter 2.1 for details on
    generated submodels>. \ In this model <math|\<forall\>> is a universal
    modality and either <math|<left|llbracket>i<right|rrbracket><rsup|\<bbb-M\><rprime|'>>=\<varnothing\>>
    or <math|<left|llbracket>i<right|rrbracket><rsup|\<bbb-M\><rprime|'>>={v}><\footnote>
      Here <math|<left|llbracket>\<phi\><right|rrbracket><rsup|\<bbb-M\>>>
      denotes <math|{w\<in\>W<space|1spc>\|<space|1spc>\<bbb-M\>,w\<vDash\>\<phi\>}>
    </footnote>. Since <math|>the store <math|\<Psi\>> of nominals is
    infinite and <math|\<Upsilon\>> is finite, we have that
    <math|\<Psi\>\<backslash\>\<Upsilon\>> is infinite, so there is some
    <math|\<iota\>:W\<hookrightarrow\>\<Psi\>\<backslash\>\<Upsilon\>> which
    assigns a fresh nominal ot every world. \ Let
    <math|\<bbb-M\><rprime|''>=\<langle\>W<rprime|''>,V<rprime|''>,R<rprime|''>,<with|math-font|cal|A><rprime|''>,\<ell\>\<rangle\>>,
    where:

    <\with|par-mode|center>
      <tabular|<tformat|<cwith|3|3|1|1|cell-row-span|1>|<cwith|3|3|1|1|cell-col-span|5>|<cwith|3|3|1|1|cell-halign|c>|<table|<row|<cell|<math|\<bullet\>>>|<cell|<math|W<rprime|''>\<assign\>W<rprime|'>>>|<cell|>|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-display|true|V<rprime|''>(p)\<assign\>V<rprime|'>(p)>>>>|<row|<cell|<math|\<bullet\>>>|<cell|<math|R<rprime|''>\<assign\>R<rprime|'><rsub|\<box\>>>>|<cell|<space|3spc>>|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-font|cal|A><rprime|''>(v)\<assign\>{\<phi\><space|1spc>\|<space|1spc>\<phi\>
      \<in\><with|math-font|cal|A><rprime|'>(v)<with|mode|text| and
      <math|\<phi\>> is a subformulae of <math|\<psi\>>>}\<cup\>{\<neg\>\<iota\>(u)<space|1spc>\|<space|1spc>\<neg\>v
      R<rprime|'> u}>>>|<row|<cell|<tabular|<tformat|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-display|true|\<ell\>(i)\<assign\><choice|<tformat|<table|<row|<cell|w>|<cell|i\<in\>\<Upsilon\><space|1spc>&<space|1spc>\<bbb-M\>,w\<vDash\>i>>|<row|<cell|\<iota\><rsup|-1>(i)>|<cell|i\<in\>\<iota\>[W]>>|<row|<cell|<with|mode|text|undefined>>|<cell|<with|mode|text|o/w>>>>>>>>>>>>>>|<cell|<math|R<rprime|''>\<assign\>R<rprime|'><rsub|\<box\>>>>|<cell|>|<cell|>|<cell|>>>>>
    </with>

    The the worlds is <math|\<bbb-M\><rprime|'>> and
    <math|\<bbb-M\><rprime|''>> agree on all subformulae of <math|\<psi\>>,
    hence <math|\<bbb-M\><rprime|''>,w\<nvDash\>\<psi\>>. The same reasoning
    as in the proof of Theorem <reference|completeness1> establishes and that
    the logic in Table <reference|logic2> itself is sound for
    <math|\<bbb-M\><rprime|''>> and makes true
    <with|font-series|bold|CSQ<math|>>, establishing completeness.
  </proof>

  <section|Logics of Multiple Knowledge Bases>

  So far, we have only dealt with systems that reason over a single knowledge
  base. \ In this section, we present various logics for reasoning over
  multiple knowledge bases.

  <subsection|Simplified Justification Logic>

  Justification Logic (JL) was originally developed by Artemov as the
  <with|font-shape|italic|Logic of Proofs> (LP) <cite|artemov_logic_1994>.
  \ Its original purpose was to provide a framework for reasoning about
  explicit provability in Peano Arithmetic. \ The first introduction of
  Justification Logic can be found in <cite|artemov_introducing_2005>, where
  Artemov and Nogina propose LP as a logic for reasoning about evidence. \ In
  <cite|fitting_logic_2005>, Melvin Fitting provided Justification Logic with
  Kripke model based semantics.

  \;

  The innovation of LP/JL is to extend awareness logic so that awareness
  operations are <with|font-shape|italic|proof terms>. \ A proof term
  <math|X> witnesses a proposition <math|\<phi\>>; the notation for this is
  <math|X:\<phi\>>. \ Proof terms are thought be operating in a
  <with|font-shape|italic|multi-conclusion> proof system, so the same proof
  term may witness many different propositions. Operators over proof terms
  are also studied. \ One operation of particular interest is <em|choice>,
  denoted <math|\<oplus\>>. \ The expression ``<math|X\<oplus\>Y:\<phi\>>''
  denotes that either <math|X> or <math|Y> witness <math|\<phi\>>. \ There
  are other operations which correspond to <with|font-shape|italic|modus
  ponens> and <with|font-shape|italic|proof-theoretic reflection>, however we
  do not consider these operations here.

  \;

  In this section we reinterpret a simplified form of JL as a logic of
  multiple knowledge bases. \ This is in the spirit of JL as a logic of
  evidence. However, instead of reasoning about proof terms as evidence, we
  instead use the terms of JL for considering knowledge bases, which are
  taken as as corpi of evidence. \ We will allow for the ``names'' of
  different knowledge bases to be denoted by different terms, and terms may
  not refer to the same knowledge base at different worlds. \ This is just as
  how in awareness logic the agent need not be aware of the same formulae at
  different worlds. \ Finally, we will make use of JL's <em|choice> operator
  as a mechanism for forming unions of knowledge bases.

  <\definition>
    Let <math|\<Pi\>> be a set of primitive terms. \ Define
    <math|\<tau\>(\<Pi\>)> with the following grammar:

    <\equation*>
      X<space|1spc>: :=<space|1spc>t\<in\>\<Pi\><space|1spc>\|<space|1spc>X\<oplus\>Y
    </equation*>

    \;

    Let <math|\<Phi\>> be a set of letters and <math|\<Pi\>> a set of
    primitive terms, and define the language
    <math|<with|math-font|cal|L><rsub|SJL>(\<Phi\>,\<Pi\>)> as:

    <\equation*>
      \<phi\> <space|1spc>: :=<space|1spc>p\<in\>\<Phi\><space|1spc>\|<space|1spc>\<circlearrowleft\><rsub|X><space|1spc>\|<space|1spc>\<bot\><space|1spc>\|<space|1spc>\<phi\>\<rightarrow\>\<psi\><space|1spc>\|<space|1spc>\<box\><rsub|X>\<phi\><space|1spc>\|<space|1spc>X:\<phi\>
    </equation*>

    where <math|X\<in\>\<tau\>(\<Pi\>)>
  </definition>

  <\definition>
    <label|justmodels>A <strong|simple justification model>
    <math|\<bbb-M\>=\<langle\>W,V,R,<with|math-font|cal|A>\<rangle\>> is a
    Kripke model with a valuation <with|mode|math|V:\<Phi\>\<cup\>{\<circlearrowleft\><rsub|X><space|1spc>\|<space|1spc>X\<in\>\<tau\>(\<Pi\>)}\<rightarrow\>2<rsup|W>>,
    an indexed relation <math|R:\<tau\>(\<Pi\>)\<rightarrow\>2<rsup|W\<times\>W>>,
    along with a modified awareness function
    <math|<with|math-font|cal|A>:W\<times\>\<tau\>(\<Pi\>)\<rightarrow\>2<rsup|<with|math-font|cal|L><rsub|SJL>(\<Phi\>,\<Pi\>)>>.
    \ In practice we will denote <math|<with|math-font|cal|A>(w,X)> by a
    curried shorthand, namely <math|<with|math-font|cal|A><rsub|w>(X)>.

    \;

    The semantics for <math|\<vDash\>> have the following modifications:

    <\eqnarray*>
      <tformat|<table|<row|<cell|\<bbb-M\>,w\<vDash\>\<box\><rsub|X>\<phi\>>|<cell|<with|mode|text|iff>>|<cell|<with|mode|text|for
      all <math|v\<in\>W> where <math|w R<rsub|X>v> we have
      <math|\<bbb-M\>,v\<vDash\>v>>>>|<row|<cell|\<bbb-M\>,w\<vDash\>X:
      \<phi\>>|<cell|<with|mode|text|iff>>|<cell|\<phi\>\<in\><with|math-font|cal|A><rsub|w>(X)>>>>
    </eqnarray*>
  </definition>

  <\definition>
    The following defines properties a simply justification model may make
    true:

    <\description-dash>
      <item*|JCSQ><math|\<bbb-M\>,w\<vDash\>\<box\><rsub|X>\<phi\><with|mode|text|
      iff > Th(\<bbb-M\>)\<cup\><with|math-font|cal|A><rsub|w>(X)\<vdash\>\<phi\>>

      <item*|JSND><math|\<bbb-M\>,w\<vDash\>\<circlearrowleft\><rsub|X><with|mode|text|
      iff <with|mode|math|\<bbb-M\>,w\<vDash\>\<phi\>> for all
      <math|\<phi\>\<in\><with|math-font|cal|A><rsub|w>(X)>>>

      <item*|CHOICE><math|<with|math-font|cal|A><rsub|w>(X\<oplus\>Y)=<with|math-font|cal|A><rsub|w>(X)\<cup\><with|math-font|cal|A><rsub|w>(Y)>
    </description-dash>

    as before, <math|\<vdash\>> is any sound logical consequence relation for
    <math|\<vDash\>> with <with|font-series|bold|modus ponens> and
    <with|font-series|bold|reflection>
  </definition>

  The above semantics are familiar. \ <with|font-series|bold|JCSQ> is the
  same as <with|font-series|bold|CSQ> from Ÿ<reference|awarenesslogic>, only
  we now consider the theory denoted by <math|X> at <math|w>, rather than
  considering a single awareness function. \ Indeed, we may naturally see
  that the logic simply justification logic is a conservative extension of
  the awareness logic in Ÿ<reference|awarenesslogic>. The awareness logic of
  knowledge bases is special case of simple justification logic where there
  is only one term.

  <subsection|Neighborhood Semantics>

  Neighborhood semantics were originally developed by Dana Scott and Richard
  Montague in the early 1970s as a generalization of Kripke semantics
  \ <cite|montague_universal_2008|scott_advice_1970>. \ In
  <cite|fagin_belief_1988>, Halpern and Fagin adapted neighborhood semantics
  for reasoning about epistemic agents without logical omniscience. \ In this
  section will demonstrate how these semantics may be modified so that every
  neighborhood corresponds to the logical consequences of a different
  knowledge base. \ This allows for using logics with neighborhood semantics
  for reasoning about multiple knowledge bases.

  <\definition>
    Let <math|\<Phi\>> be a set of letters and <math|\<Psi\>> a set of
    nominals, and define the language <math|<with|math-font|cal|L><rsub|N>(\<Phi\>)>
    as:

    <\equation*>
      \<phi\> <space|1spc>: :=<space|1spc>p\<in\>\<Phi\><space|1spc>\|<space|1spc>\<bot\><space|1spc>\|<space|1spc>\<phi\>\<rightarrow\>\<psi\><space|1spc>\|<space|1spc>\<box\>\<phi\><space|1spc>\|<space|1spc>A:\<phi\><space|1spc>\|<space|1spc>K\<phi\>
    </equation*>
  </definition>

  Just as previous semantics, ``<math|\<box\>\<phi\>>'' is intended to mean
  that the agent has an argument for <math|\<phi\>> from some knowledge base.
  \ A novelty we present here is that ``<math|K\<phi\>>'' means that the
  agent has an argument for <math|\<phi\>> from some
  <with|font-shape|italic|sound> knowledge base.

  \;

  <\definition>
    <label|neighborhoodmodels>A <strong|neighborhood model>
    <math|\<bbb-M\>=\<langle\>W,V,<with|math-font|cal|N>,<with|math-font|cal|A>\<rangle\>>
    has a neighborhood function <math|<with|math-font|cal|N>:W\<rightarrow\>2<rsup|2<rsup|W>>>
    and a multi-awareness function <math|<with|math-font|cal|A>:W\<rightarrow\>2<rsup|2<rsup|<with|math-font|cal|L><rsub|N>(\<Phi\>)>>>

    \;

    The semantics for <math|\<vDash\>> have the following modifications:

    <\eqnarray*>
      <tformat|<table|<row|<cell|\<bbb-M\>,w\<vDash\>\<box\>
      \<phi\>>|<cell|<with|mode|text|iff>>|<cell|<with|mode|text|there exists
      a <math|U\<in\><with|math-font|cal|N><rsub|w>> where
      <math|\<bbb-M\>,v\<vDash\>\<phi\>> for all
      <math|v\<in\>U>>>>|<row|<cell|\<bbb-M\>,w\<vDash\>K
      \<phi\>>|<cell|<with|mode|text|iff>>|<cell|<with|mode|text|there exists
      a <math|U\<in\><with|math-font|cal|N><rsub|w>> where <math|w\<in\>U>
      and <math|\<bbb-M\>,v\<vDash\>\<phi\>> for all
      <math|v\<in\>U>>>>|<row|<cell|\<bbb-M\>,w\<vDash\>A:
      \<phi\>>|<cell|<with|mode|text|iff>>|<cell|\<phi\>\<in\><big|cup><with|math-font|cal|A<rsub|w>>>>>>
    </eqnarray*>
  </definition>

  Here we modify our previous notion of <with|font-series|bold|CSQ> and
  <with|font-series|bold|SND> to match how our semantics are intended for
  reasoning over multiple bases:

  <\definition>
    The following defines properties a neighborhood model may make true:

    <\description-dash>
      <item*|NCSQ><math|\<bbb-M\>,w\<vDash\>\<box\>\<phi\><with|mode|text|
      iff there exists a set <math|X\<in\><with|math-font|cal|A><rsub|w>>
      such that > Th(\<bbb-M\>)\<cup\>X\<vdash\>\<phi\>>

      <item*|NSND><math|\<bbb-M\>,w\<vDash\>K\<phi\><with|mode|text| iff
      there exists a set <math|X\<in\><with|math-font|cal|A><rsub|w>> such
      that <with|mode|math|\<bbb-M\>,w\<vDash\>X> and
      >Th(\<bbb-M\>)\<cup\>X\<vdash\>\<phi\>>
    </description-dash>

    as before, <math|\<vdash\>> is any sound logical consequence relation for
    <math|\<vDash\>> with <with|font-series|bold|modus ponens> and
    <with|font-series|bold|reflection>
  </definition>

  <big-table|<tabular|<tformat|<table|<row|<cell|<math|\<vdash\>\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>(\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<chi\>)\<rightarrow\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<phi\>\<rightarrow\>\<chi\>>>>|<row|<cell|<math|\<vdash\>((\<phi\>\<rightarrow\>\<bot\>)\<rightarrow\>(\<psi\>\<rightarrow\>\<bot\>))\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>K\<phi\>\<rightarrow\>\<box\>\<phi\>>>>|<row|<cell|<math|\<vdash\>K\<phi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>A:\<phi\>\<rightarrow\>\<box\>\<phi\>>>>|<row|<cell|>>|<row|<cell|<tabular|<tformat|<table|<row|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\><space|4spc>\<vdash\>\<phi\>|\<vdash\>\<psi\>>>>>|<cell|<space|6spc><with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\>|\<vdash\>\<box\>\<phi\>\<rightarrow\>\<box\>\<psi\>>>>>|<cell|<space|6spc>>|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\>|\<vdash\>K\<phi\>\<rightarrow\>K\<psi\>>>>>>>>>>>>>>|<label|logic3>A
  neighborhood logic for <with|font-series|bold|NCSQ> and <strong|NSND>>

  <\theorem>
    Assuming an infinite store of letters <math|\<Phi\>>, the logic in Table
    <reference|logic3> is sound and weakly complete for neighborhood
    semantics making true <with|font-series|bold|NCSQ<math|>> and
    <with|font-series|bold|NSND>.
  </theorem>

  <\proof>
    As in previous proofs, we only establish completeness. \ Assume that
    <math|\<nvdash\>\<psi\>>, and define the finitary canonical model
    <math|\<bbb-M\>=\<langle\>W,V,<with|math-font|cal|K>,<with|math-font|cal|N>,<with|math-font|cal|A>\<rangle\>>
    where:

    <\itemize-dot>
      <item><math|W\<assign\><with|mode|text|the maximally consistent sets of
      subformulae of <math|\<psi\>>, closed under pseudo-negation>>

      <item><math|V(p)\<assign\>{v\<in\>W<space|1spc>\|<space|1spc>p\<in\>v}>

      <item><with|mode|math|<with|math-font|cal|K><rsub|w>\<assign\>{S\<in\>\<wp\>W<space|1spc>\|<space|1spc>{v\<in\>W<space|1spc>\|<space|1spc>\<phi\>\<in\>v}\<subseteq\>S<space|1spc>&<space|1spc>K\<phi\>\<in\>w}>

      <item><with|mode|math|<math|<with|math-font|cal|N><rsub|w>\<assign\>{S\<in\>\<wp\>W<space|1spc>\|<space|1spc>{v\<in\>W<space|1spc>\|<space|1spc>\<phi\>\<in\>v}\<subseteq\>S<space|1spc>&<space|1spc>\<box\>\<phi\>\<in\>w}>>

      <item><with|mode|math|<math|<with|math-font|cal|A><rsub|w>\<assign\>{{\<phi\>}<space|1spc>\|<space|1spc>A:\<phi\>\<in\>w}>>
    </itemize-dot>

    Note that in this model, there are neighborhoods for both knowledge and
    belief; more work is necessary to find a model based on this one which
    conforms to the semantics in Definition <reference|neighborhoodmodels>.
    \ For now, assume that <math|K> is just another modality governed by the
    neighborhoods in <math|<with|math-font|cal|K><rsub|w>>. \ In both
    neighborhood functions, our idea is that the neighborhoods of <math|w> in
    are supersets <math|S\<supseteq\><left|llbracket>\<phi\><right|rrbracket>>
    where <math|\<box\>\<phi\>\<in\>w> or <math|K\<phi\>\<in\>w>,
    respectively.

    \;

    There are steps of the inductive proof of the Truth Lemma for this
    structure which are not obvious nor obviously documented elsewhere.
    \ Assume <math|\<bbb-M\>,w\<vDash\>\<box\>\<chi\>>, where the Truth Lemma
    has been proven to hold for <math|\<chi\>>; we must show
    <math|\<box\>\<chi\>\<in\>w>. \ By our assumption there is some
    <math|\<phi\>> and <math|S> where <math|\<box\>\<phi\>\<in\>w> and
    <math|S\<supseteq\>{v\<in\>W<space|1spc>\|<space|1spc>\<phi\>\<in\>v}>.
    \ We argue that <math|\<vdash\>\<phi\>\<rightarrow\>\<chi\>>; for if not
    then by the finitary Lindenbaum lemma there is some <math|u\<in\>W> where
    <math|\<phi\>\<in\>u> and <math|\<chi\>\<nin\>u>. \ Hence <math|u\<in\>S>
    and <math|\<bbb-M\>,u\<nvDash\>\<chi\>>, a contradiction. \ Since
    <math|\<vdash\>\<phi\>\<rightarrow\>\<chi\>> then we know that
    <math|\<vdash\>\<box\>\<phi\>\<rightarrow\>\<box\>\<chi\>> by our rules,
    which means that <math|\<box\>\<chi\>\<in\>w> by maximality.

    \;

    By the Lindenbaum Lemma we have that there is some <math|w\<in\>W> where
    <math|\<bbb-M\>,w\<nvDash\>\<psi\>>. \ <math|\<bbb-M\>> makes true a
    number of properties:

    <\enumerate-numeric>
      <item><math|W> is finite and <math|<with|math-font|cal|A><rsub|v>> is
      finite for all <math|v\<in\>W>

      <item><math|<with|math-font|cal|K><rsub|w>\<subseteq\><with|math-font|cal|N><rsub|w>>

      <item>If <math|S\<in\><with|math-font|cal|K><rsub|w>> then
      <math|w\<in\>S>

      <item><math|\<bbb-M\>,v\<vDash\>A:\<phi\>\<rightarrow\>\<box\>\<phi\>>
      for all <math|v\<in\>W>

      <item><math|<with|math-font|cal|N><rsub|w>> and
      <math|<with|math-font|cal|K><rsub|w>> are closed under supersets
    </enumerate-numeric>

    \;

    As in the proof of Theorem <reference|completeness1>, we use a
    bisimulation to move to a model where property (3) is strengthened to
    (3<math|<rprime|'>>): for all <math|S\<in\><with|math-font|cal|N><rsub|w>>,
    <math|w\<in\>S> if and only if <math|S\<in\><with|math-font|cal|K><rprime|'><rsub|w>>.
    \ We defer the reader to <cite|hansen_bisimulation_2007|pauly_bisimulation_1999>
    for details regarding bisimulation in neighborhood semantics. \ Define
    <math|\<bbb-M\><rprime|'>\<assign\>\<langle\>W<rprime|'>,V<rprime|'>,<with|math-font|cal|K><rprime|'>,<with|math-font|cal|N><rprime|'>,<with|math-font|cal|A><rprime|'>\<rangle\>>
    such that:

    <\itemize-dot>
      <item><with|mode|math|W<rprime|'>\<assign\>W\<uplus\>W> where
      \ <math|l,r> its associated canonical injections and
      <math|\<theta\>(v<rsub|l>)\<assign\>\<theta\>(v<rsub|r>)\<assign\>v> is
      a left-inverse of <math|l,r>

      <item><math|V<rprime|'>(p)\<assign\>{v<rsub|l>,v<rsub|r><space|1spc>\|<space|1spc>v\<in\>V(p)}>

      <item><math|<with|math-font|cal|K><rprime|'>(v<rsub|i>)\<assign\>{S<space|1spc>\|<space|1spc>v<rsub|i>\<in\>S<space|1spc>&<space|1spc>\<theta\>[S]\<in\><with|math-font|cal|K<rsub|v>>}>
      where <math|i=l,r>

      <item><math|<with|math-font|cal|N><rprime|'>(v<rsub|i>)\<assign\><with|math-font|cal|K><rprime|'>(v<rsub|i>)\<cup\>{S<space|1spc>\|<space|1spc>v<rsub|i>\<nin\>S<space|1spc>&<space|1spc>\<theta\>[S]\<in\><with|math-font|cal|N<rsub|v>>}>
      where <math|i=l,r>

      <item><math|<with|math-font|cal|A><rprime|'>(v<rsub|l>)\<assign\><with|math-font|cal|A><rprime|'>(v<rsub|r>)\<assign\><with|math-font|cal|A>(v)><math|>
    </itemize-dot>

    \;

    If we let <math|Z\<assign\>{(v,v<rsub|r>),(v,v<rsub|l>)<space|1spc>\|<space|1spc>v\<in\>W}>,
    it is straightforward to verify that <math|Z> is a neighborhood
    bisimulation. \ Hence <math|\<bbb-M\>,w<rsub|l>\<nvDash\>\<psi\>>.
    \ Along with (3<math|<rprime|'>>), this model makes true (1), (2), (4).
    \ In fact, in light of (<math|3<rprime|'>>), we can see that this model
    does not need <math|<with|math-font|cal|K><rprime|'>>, and conforms to
    the semantics in Definition <reference|neighborhoodmodels>.<htab|5mm>

    \;

    As in previous proofs, let <math|\<Lambda\>> be the proposition letters
    occuring in <math|\<psi\>> and define an injection
    <math|\<iota\>:W<rprime|'>\<hookrightarrow\>\<Phi\>\<backslash\>\<Lambda\>>,
    assigning a nominal to every world in <math|\<bbb-M\><rprime|'>>.
    \ Define <math|\<bbb-M\><rprime|''>\<assign\>\<langle\>W<rprime|''>,
    V<rprime|''>,<with|math-font|cal|N><rprime|''>,<with|math-font|cal|A><rprime|''>\<rangle\>>
    such that:

    \;

    <\with|par-mode|center>
      <tabular|<tformat|<table|<row|<cell|<math|\<bullet\>>>|<cell|<math|W<rprime|''>\<assign\>W<rprime|'>>>|<cell|>|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-display|true|V<rprime|''>(p)\<assign\><choice|<tformat|<table|<row|<cell|V<rprime|'>(p)>|<cell|p\<in\>\<Lambda\>>>|<row|<cell|{v}>|<cell|p=i(v)>>|<row|<cell|\<varnothing\>>|<cell|o/w>>>>>>>>>|<row|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-font|cal|N><rprime|''><rsub|w>\<assign\><with|math-font|cal|N><rprime|'><rsub|w>>>|<cell|<space|3spc>>|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-font|cal|A><rprime|''><rsub|v>\<assign\>{\<partial\><rsub|v>S<space|1spc>\|<space|1spc>S\<in\><with|math-font|cal|N><rprime|'><rsub|w>}>>>>>>
    </with>

    \;

    \;

    Where <math|\<partial\><rsub|v>S\<assign\>{\<phi\><space|1spc>\|<space|1spc>\<phi\>\<in\><big|cup><with|math-font|cal|A><rsub|v><rprime|'>,
    <with|mode|text|<math|\<phi\>> is a subformula of <math|\<psi\>>
    and><space|1spc>S\<subseteq\><left|llbracket>\<phi\><right|rrbracket><rsup|\<bbb-M\><rprime|'>>}\<cup\>{\<neg\>\<iota\>(u)<space|1spc>\|<space|1spc>u\<nin\>S}>.

    As before, this model agrees with <math|\<bbb-M\><rprime|'>> on all
    subformulae of <math|\<psi\>>, using the semantics in Definition
    <reference|neighborhoodmodels>, hence
    <math|\<bbb-M\><rprime|''>,w<rsub|l>\<nvDash\>\<phi\>>. \ 

    \;

    All that is left is to show <with|font-series|bold|NCSQ> and
    <with|font-series|bold|NSND> three new properties:

    <\enumerate-roman>
      <item>For all words <math|v> and all
      <math|X\<in\><with|math-font|cal|A><rsub|v><rprime|''>>, then <math|X>
      is finite and \ <math|X=\<partial\><rsub|v>S> for some
      <math|S\<in\><with|math-font|cal|N><rsub|v>>

      <item>For all <math|v> and all <math|S\<in\><with|math-font|cal|N><rsub|v>>,
      <math|u\<in\>S> if and only if <math|\<bbb-M\><rprime|''>,u\<vDash\><big|wedge>\<partial\><rsub|v>S>

      <item>The logic presented in Table <reference|logic3> is sound for
      <math|\<bbb-M\><rprime|''>>
    </enumerate-roman>

    Along with the deduction theorem for <math|\<vdash\>>, these properties
    establish <with|font-series|bold|NCSQ> for this model using the logic of
    Table <reference|logic3> itself:

    <\align*>
      <tformat|<table|<row|<cell|<with|mode|text|<math|\<exists\>X\<in\><with|math-font|cal|A<rprime|''><rsub|v>><with|mode|text|
      s.t. >Th(\<bbb-M\><rprime|''>)\<cup\>X\<vdash\>\<phi\>>>>|<cell|\<Longleftrightarrow\><with|mode|text|<math|\<exists\>S\<in\><with|math-font|cal|N<rprime|''><rsub|v>><with|mode|text|
      s.t. >Th(\<bbb-M\><rprime|''>)\<cup\>\<partial\><rsub|v>S\<vdash\>\<phi\>>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<math|\<exists\>S\<in\><with|math-font|cal|N<rprime|''><rsub|v>><with|mode|text|
      s.t. >Th(\<bbb-M\><rprime|''>)\<vdash\><big|wedge>\<partial\><rsub|v>S\<rightarrow\>\<phi\>>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<math|\<exists\>S\<in\><with|math-font|cal|N<rprime|''><rsub|v>><with|mode|text|
      s.t. ><big|wedge>\<partial\><rsub|v>S\<rightarrow\>\<phi\>\<in\>Th(\<bbb-M\><rprime|''>)>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<math|\<exists\>S\<in\><with|math-font|cal|N<rprime|''><rsub|v>><with|mode|text|
      s.t. ><left|llbracket><big|wedge>\<partial\><rsub|v>S<right|rrbracket>\<subseteq\><left|llbracket>\<phi\><right|rrbracket>>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<math|\<exists\>S\<in\><with|math-font|cal|N<rprime|''><rsub|v>><with|mode|text|
      s.t. <with|mode|math|\<forall\>u\<in\>W> if
      >\<bbb-M\>,u\<vDash\><big|wedge>\<partial\><rsub|v>S<with|mode|text|
      then >\<bbb-M\>,u\<vDash\>\<phi\>>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<math|\<exists\>S\<in\><with|math-font|cal|N<rprime|''><rsub|v>><with|mode|text|
      s.t. >\<bbb-M\>,u\<vDash\>\<phi\>><with|mode|math|<with|mode|text| for
      all >u\<in\>S>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\>\<bbb-M\>,v\<vDash\>\<box\>\<phi\>>>>>
    </align*>

    <with|font-series|bold|NSND> follows from <with|font-series|bold|NCSQ>
    and the semantics of Definition <reference|neighborhoodmodels>.
  </proof>

  It is not too hard to identify the fragment of this logic that governs
  knowledge alone. \ This fragment has special importance, since it governs
  the notion of knowledge presented in Ÿ<reference|quantifying>.

  <big-table|<tabular|<tformat|<table|<row|<cell|<math|\<vdash\>\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>(\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<chi\>)\<rightarrow\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<phi\>\<rightarrow\>\<chi\>>>>|<row|<cell|<math|\<vdash\>((\<phi\>\<rightarrow\>\<bot\>)\<rightarrow\>(\<psi\>\<rightarrow\>\<bot\>))\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>K\<phi\>\<rightarrow\>\<phi\>>>>|<row|<cell|>>|<row|<cell|<tabular|<tformat|<table|<row|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\><space|4spc>\<vdash\>\<phi\>|\<vdash\>\<psi\>>>>>|<cell|>|<cell|>|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\>|\<vdash\>K\<phi\>\<rightarrow\>K\<psi\>>>>>>>>>>>>>>|<label|logic4>A
  knowledge-only neighborhood logic for <with|font-series|bold|NCSQ> and
  <strong|NSND>>

  <\proposition>
    The logic in Table <reference|logic4> governs the <math|\<box\>>-free
    fragment of the logic in Table <reference|logic3>
  </proposition>

  This concludes our analysis of knowledge bases using neighborhood
  semantics.

  <\subsection>
    <label|quantifying>Using Modalities to Quantify over Knowledge Bases
  </subsection>

  <\bibliography|bib|plain|~/Documents/EviL/Paper/zotero.bib>
    <\bib-list|10>
      <bibitem*|1><label|bib-artemov_introducing_2005>S.<nbsp>Artemov and
      E.<nbsp>Nogina. <newblock>Introducing justification into epistemic
      logic. <newblock><with|font-shape|italic|Journal of Logic and
      Computation>, 15(6):1059, 2005.

      <bibitem*|2><label|bib-artemov_logic_1994>S.<nbsp>N Artemov.
      <newblock>Logic of proofs. <newblock><with|font-shape|italic|Annals of
      Pure and Applied Logic>, 67(1):29â€“60, 1994.

      <bibitem*|3><label|bib-basu_revealed_1980>Kaushik Basu.
      <newblock><with|font-shape|italic|Revealed preference of government>.
      <newblock>Cambridge University Press, Cambridge; New York, 1980.

      <bibitem*|4><label|bib-blackburn_modal_2001>P.<nbsp>Blackburn,
      M.<nbsp>De Rijke, and Y.<nbsp>Venema.
      <newblock><with|font-shape|italic|Modal logic>. <newblock>Cambridge
      Univ Pr, 2001.

      <bibitem*|5><label|bib-boolos_logic_1995>George Boolos.
      <newblock><with|font-shape|italic|The logic of provability>.
      <newblock>Cambridge University Press, 1995.

      <bibitem*|6><label|bib-bull_approach_1970>R.<nbsp>A. Bull. <newblock>An
      approach to tense logic. <newblock><with|font-shape|italic|Theoria>,
      36(3):282--300, December 1970.

      <bibitem*|7><label|bib-davidson_could_1995>Donald Davidson.
      <newblock>Could there be a science of rationality?
      <newblock><with|font-shape|italic|International Journal of
      Philosophical Studies>, 3(1):1â€“16, 1995.

      <bibitem*|8><label|bib-fagin_belief_1987>R.<nbsp>Fagin and J.<nbsp>Y
      Halpern. <newblock>Belief, awareness, and limited reasoning* 1.
      <newblock><with|font-shape|italic|Artificial Intelligence>,
      34(1):39â€“76, 1987.

      <bibitem*|9><label|bib-fitting_logic_2005>M.<nbsp>Fitting.
      <newblock>The logic of proofs, semantically.
      <newblock><with|font-shape|italic|Annals of Pure and Applied Logic>,
      132(1):1â€“25, 2005.

      <bibitem*|10><label|bib-halpern_set-theoretic_1999>Joseph<nbsp>Y.
      Halpern. <newblock>Set-theoretic completeness for epistemic and
      conditional logic. <newblock><with|font-shape|italic|Annals of
      Mathematics and Artificial Intelligence>, 26(1-4):1--27, 1999.

      <bibitem*|11><label|bib-hendricks_mainstream_2006>V.<nbsp>F Hendricks.
      <newblock><with|font-shape|italic|Mainstream and formal epistemology>.
      <newblock>Cambridge Univ Pr, 2006.

      <bibitem*|12><label|bib-kornblith_beyond_1980>Hilary Kornblith.
      <newblock>Beyond foundationalism and the coherence theory.
      <newblock><with|font-shape|italic|The Journal of Philosophy>,
      77(10):597--612, October 1980.

      <bibitem*|13><label|bib-montague_universal_2008>Richard Montague.
      <newblock>Universal grammar. <newblock><with|font-shape|italic|Theoria>,
      36(3):373--398, 2008.

      <bibitem*|14><label|bib-prior_revised_1969>Arthur<nbsp>N. Prior.
      <newblock><with|font-shape|italic|Revised and Expanded Edition of
      Arthur N. Prior: Papers on Time and Tense>. <newblock>Oxford University
      Press, 1969. <newblock>reprinted in 2003.

      <bibitem*|15><label|bib-rubinstein_modeling_1998>Ariel Rubinstein.
      <newblock><with|font-shape|italic|Modeling Bounded Rationality>.
      <newblock>MIT Press, 1998.

      <bibitem*|16><label|bib-scott_advice_1970>D.<nbsp>Scott.
      <newblock>Advice on modal logic. <newblock><with|font-shape|italic|Philosophical
      problems in Logic>, 143:74, 1970.

      <bibitem*|17><label|bib-sen_behaviour_1973>Amartya Sen.
      <newblock>Behaviour and the concept of preference.
      <newblock><with|font-shape|italic|Economica>, 40(159):241--259, August
      1973.

      <bibitem*|18><label|bib-van_benthem_inference_2009>Johan van Benthem
      and F.<nbsp>R VelÃ¡zquez-Quesada. <newblock>Inference, promotion, and
      the dynamics of awareness. <newblock><with|font-shape|italic|ILLC
      Amsterdam. To appear in Knowledge, Rationality and Action>, 2009.
    </bib-list>
  </bibliography>
</body>

<\initial>
  <\collection>
    <associate|language|american>
    <associate|page-type|letter>
    <associate|par-columns|1>
    <associate|par-first|0fn>
    <associate|par-par-sep|1fns>
    <associate|sfactor|4>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|?>>
    <associate|auto-10|<tuple|3|?>>
    <associate|auto-11|<tuple|4|?>>
    <associate|auto-12|<tuple|3.3|?>>
    <associate|auto-13|<tuple|3.3|?>>
    <associate|auto-14|<tuple|3.4|?>>
    <associate|auto-2|<tuple|2|?>>
    <associate|auto-3|<tuple|2.1|?>>
    <associate|auto-4|<tuple|1|?>>
    <associate|auto-5|<tuple|2.2|?>>
    <associate|auto-6|<tuple|2|?>>
    <associate|auto-7|<tuple|3|?>>
    <associate|auto-8|<tuple|3.1|?>>
    <associate|auto-9|<tuple|3.2|?>>
    <associate|awarenesslogic|<tuple|2.1|?>>
    <associate|awarenessmodels|<tuple|2|?>>
    <associate|basic-modal|<tuple|2|?>>
    <associate|bib-artemov_introducing_2005|<tuple|1|?>>
    <associate|bib-artemov_logic_1994|<tuple|2|?>>
    <associate|bib-basu_revealed_1980|<tuple|3|?>>
    <associate|bib-blackburn_modal_2001|<tuple|4|?>>
    <associate|bib-boolos_logic_1995|<tuple|5|?>>
    <associate|bib-bull_approach_1970|<tuple|6|?>>
    <associate|bib-castaneda_knowing_1970|<tuple|10|?>>
    <associate|bib-davidson_could_1995|<tuple|7|?>>
    <associate|bib-fagin_belief_1987|<tuple|8|?>>
    <associate|bib-fitting_logic_2005|<tuple|9|?>>
    <associate|bib-ginet_what_1970|<tuple|8|?>>
    <associate|bib-halpern_set-theoretic_1999|<tuple|10|?>>
    <associate|bib-hendricks_mainstream_2006|<tuple|11|?>>
    <associate|bib-kornblith_beyond_1980|<tuple|12|?>>
    <associate|bib-montague_universal_2008|<tuple|13|?>>
    <associate|bib-prior_revised_1969|<tuple|14|?>>
    <associate|bib-rubinstein_modeling_1998|<tuple|15|?>>
    <associate|bib-scott_advice_1970|<tuple|16|?>>
    <associate|bib-sen_behaviour_1973|<tuple|17|?>>
    <associate|bib-van_benthem_inference_2009|<tuple|18|?>>
    <associate|bib-van_benthem_reflectionsepistemic_1991|<tuple|11|?>>
    <associate|completeness1|<tuple|4|?>>
    <associate|footnote-1|<tuple|1|?>>
    <associate|footnote-2|<tuple|2|?>>
    <associate|footnote-3|<tuple|3|?>>
    <associate|footnr-1|<tuple|1|?>>
    <associate|footnr-2|<tuple|2|?>>
    <associate|footnr-3|<tuple|3|?>>
    <associate|hybridsemantics|<tuple|7|?>>
    <associate|intro|<tuple|1|?>>
    <associate|justmodels|<tuple|11|?>>
    <associate|logic|<tuple|1|?>>
    <associate|logic1|<tuple|1|?>>
    <associate|logic2|<tuple|2|?>>
    <associate|logic3|<tuple|3|?>>
    <associate|logic4|<tuple|4|?>>
    <associate|neighborhoodmodels|<tuple|14|?>>
    <associate|quantifying|<tuple|3.3|?>>
    <associate|semdef1|<tuple|2|?>>
    <associate|simplyjustificationmodels|<tuple|11|?>>
    <associate|theorem-theorem|<tuple|4|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      van_benthem_reflectionsepistemic_1991

      van_benthem_inference_2009

      artemov_introducing_2005

      halpern_set-theoretic_1999

      rubinstein_modeling_1998

      sen_behaviour_1973

      basu_revealed_1980

      davidson_could_1995

      van_benthem_reflectionsepistemic_1991

      artemov_introducing_2005

      artemov_logic_1994

      fitting_logic_2005

      van_benthem_inference_2009

      fagin_belief_1987

      hendricks_mainstream_2006

      kornblith_beyond_1980

      fagin_belief_1987

      van_benthem_inference_2009

      boolos_logic_1995

      prior_revised_1969

      bull_approach_1970

      boolos_logic_1995

      blackburn_modal_2001

      montague_universal_2008

      scott_advice_1970

      hansen_bisimulation_2007

      pauly_bisimulation_1999
    </associate>
    <\associate|table>
      <tuple|normal|<label|logic1>An awareness logic for
      <with|font-series|<quote|bold>|CSQ><with|mode|<quote|math>|<rsub|\<vdash\>>>
      and <with|font-series|<quote|bold>|SND>|<pageref|auto-4>>

      <tuple|normal|<label|logic2>A hybrid logic for
      <with|font-series|<quote|bold>|CSQ>|<pageref|auto-6>>

      <tuple|normal|<label|logic3>A neighborhood logic for
      <with|font-series|<quote|bold>|NCSQ> and
      <with|font-series|<quote|bold>|math-font-series|<quote|bold>|NSND>|<pageref|auto-9>>

      <tuple|normal|<label|logic4>A knowledge-only neighborhood logic for
      <with|font-series|<quote|bold>|NCSQ> and
      <with|font-series|<quote|bold>|math-font-series|<quote|bold>|NSND>|<pageref|auto-10>>
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Introduction<label|intro>>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Basic
      Explicit Logics of Knowledge Bases>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|2.1<space|2spc>Awareness
      Logic<label|awarenesslogic> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|1.5fn>|2.2<space|2spc>Hybrid Logic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Logics
      of Multiple Knowledge Bases> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|3.1<space|2spc>Neighborhood Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>