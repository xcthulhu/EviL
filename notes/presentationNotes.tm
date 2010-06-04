<TeXmacs|1.0.7.2>

<style|generic>

<\body>
  In the preamble:

  Set <math|\<wp\>> to powerset

  Set <with|mode|math|\<ominus\>> to diamondminus

  Set <math|\<oplus\>> to diamondplus

  Set <math|\<diamondsuit\>> to MNSDiamond

  Set <math|\<Vvdash\>> to VDash

  \;

  Make sure to fix Godel!

  <with|font-shape|small-caps|EviL>

  Introduction to Epistemic Logic

  <\itemize-dot>
    <item>Epistemic Logic (<with|font-family|ss|EL>) is a branch of applied
    modal logic

    <item>Since its conception in Hintikka's , <with|font-family|ss|EL>
    traditionally takes knowledge as a primitive notion

    <item>The language of basic <with|font-family|ss|EL> is the common
    language of modal logic:

    <\equation*>
      \<phi\><space|1spc> \<colons\><space|-0.6spc>=<space|1spc>p\<in\>\<Phi\><space|1spc>\|<space|1spc>\<phi\>\<rightarrow\>\<psi\><space|1spc>\|<space|1spc>\<bot\><space|1spc>\|<space|1spc>K\<phi\>
    </equation*>
  </itemize-dot>

  framebreak

  <\itemize-dot>
    <item>Modern <with|font-family|ss|EL> can be thought of as a general
    intentional framework for reasoning about information; that being the
    case it naturally finds applications beyond philosophy. \ Specifically,
    <with|font-family|ss|EL> finds application in:

    <\itemize-dot>
      <item><em|Computer Science> -- in multi-agent systems and security
      protocol analysis

      <item><with|font-shape|italic|Economics> -- <with|font-family|ss|EL> is
      particularly suited to game theory; the notion of <em|information
      states> are shared between the two frameworks
    </itemize-dot>
  </itemize-dot>

  The Axioms of <with|font-family|ss|EL>

  <\itemize-dot>
    <item>Basic <with|font-family|ss|EL> of one agent is generally assumed to
    be the modal logic <with|font-family|ss|S5>

    <item>The axioms of <with|font-family|ss|S5> are:

    <\itemize-dot>
      <item>All classical propositional tautologies

      <item><math|K\<phi\>\<rightarrow\>\<phi\>><htab|5mm>Axiom <math|T>

      <with|font-shape|italic|Truth: If the agent knows something, then its
      true>

      <item><math|K\<phi\>\<rightarrow\>K K\<phi\>><htab|5mm>Axiom <math|4>

      <with|font-shape|italic|Positive Introspection: If the agent knows
      something, she knows that she knows it>

      <item><math|\<neg\>K\<phi\>\<rightarrow\>K\<neg\>K\<phi\>><htab|5mm>Axiom
      <math|5>

      <\with|font-shape|italic>
        Negative Introspection: There are no unknown unknowns (despite Donald
        Rumsfeld)
      </with>

      <item><math|K(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>K\<phi\>\<rightarrow\>K\<psi\>><htab|5mm>Axiom
      <math|K>

      <with|font-shape|italic|Logical Omniscience: The agent knows all the
      logical consequences of her knowledge>
    </itemize-dot>
  </itemize-dot>

  framebreak

  <\itemize-dot>
    <item><with|font-family|ss|EL> is also closed under the following rules:

    <htab|5mm><with|mode|math|<with|math-display|true|<frac|\<vdash\>\<phi\><space|1em>\<vdash\>\<phi\>\<rightarrow\>\<psi\>|\<vdash\>\<psi\>>>><htab|5mm><math|<with|math-display|true|<frac|\<vdash\>\<phi\>|\<vdash\>K\<phi\>>>><htab|5mm>
  </itemize-dot>

  The Semantics of <with|font-family|ss|EL>

  <\itemize-dot>
    <item>The semantics of <with|font-family|ss|EL> are
    <with|font-shape|italic|Kripke Structures> with equivalence relations

    <item>An equivalence relation <math|\<sim\>> over a set <math|W>
    satisfies the following rules for all <math|x,y,z\<in\>W>:

    <\itemize-dot>
      <item><math|\<sim\>> is <em|reflexive> -- <math|x \<sim\> x>

      <item><math|\<sim\>> is <em|transitive> -- if <math|x \<sim\>y> and
      <math|y\<sim\>z> then <math|x \<sim\>z>

      <item><math|\<sim\>> is <with|font-shape|italic|symmetric> -- if
      <math|x \<sim\>y> then <math|y\<sim\>x>
    </itemize-dot>
  </itemize-dot>

  framebreak

  <\itemize-dot>
    <item>Let <math|\<bbb-M\>\<assign\>\<langle\>W,\<sim\>,V\<rangle\>> be a
    Kripke model where <math|\<sim\>> is an equivalence relation.

    <item>The semantic truth predicate <math|(\<Vdash\>)> of
    <with|font-family|ss|EL> is defined as follows:

    <\itemize-dot>
      <item><math|\<bbb-M\>,w\<Vdash\>p\<Longleftrightarrow\>p\<in\>V(w)>

      <item><math|\<bbb-M\>,w\<Vdash\>\<phi\>\<rightarrow\>\<psi\>\<Longleftrightarrow\>>either
      <math|\<bbb-M\>,w\<nVdash\>\<phi\>> or
      <math|\<bbb-M\>,w\<Vdash\>\<psi\>>

      <item><math|\<bbb-M\>,w\<Vdash\>\<bot\>> never

      <item><math|\<bbb-M\>,w\<Vdash\>K\<phi\>\<Longleftrightarrow\>>forall
      <math|v\<in\>W>, if <math|w\<sim\>v> then
      <math|\<bbb-M\>,v\<Vdash\>\<phi\>>
    </itemize-dot>

    <item>Such a model is called an <with|font-family|ss|S5> model
  </itemize-dot>

  \;

  Thermometer in a Box

  <\itemize-dot>
    <item>Basic <with|font-family|ss|EL> ascribes knowledge to inanimate
    objects as readily as it models agents

    <item>To understand this, consider the case of a thermometer in a
    <math|1> m<math|<rsup|3>> box:

    <big-figure|FIXME Picture of Thermometer in a
    Box|<label|thermometer-picture>>

    <item>If the thermometer reads 290 Kelvin, how many moles of gas are in
    the chamber?
  </itemize-dot>

  Ideal Gas Law

  <\itemize-dot>
    <item>There is no one answer for how many moles of gas are in the
    chamber. \ Rather, the answer is governed by the
    <with|font-shape|italic|ideal gas law>:

    <\equation*>
      P V = n R T
    </equation*>

    <item>Here <math|P> is the <with|font-shape|italic|pressure>, <math|V> is
    the <with|font-shape|italic|volume>, <math|n> stands for
    <with|font-shape|italic|moles>, <math|R> is the
    <with|font-shape|italic|ideal gas constant>, and <math|T> is the
    <with|font-shape|italic|temperature>
  </itemize-dot>

  Thermometer Models

  <\itemize-dot>
    <item>We may use epistemic logic to model the beliefs of this thermometer
    in a box. \ The following minor adaptation of the basic epistemic logic
    grammar is suited to this purpose:

    <\equation*>
      \<phi\><with|mode|text| >\<colons\><space|-0.8spc>=<with|mode|text| >x
      <with|mode|text| Pascals><with|mode|text| >\|<with|mode|text|
      >y<with|mode|text| moles><with|mode|text| >\|<with|mode|text|
      >z<with|mode|text| Pascals><with|mode|text| >\|<with|mode|text|
      >\<phi\>\<rightarrow\>\<psi\><with|mode|text| >\|<with|mode|text|
      >\<bot\><with|mode|text| >\|<with|mode|text| >K\<phi\>
    </equation*>
  </itemize-dot>

  framebreak

  <\itemize-dot>
    <item>With appropriate interpretation we can think of an
    <with|font-family|ss|EL> model <math|\<langle\>W,V,\<sim\>\<rangle\>> for
    the thermometer in a box, expressed as follows (remember that the volume
    in constant!):

    <\itemize-dot>
      <item><math|W> is pairs <math|(P,n)> where <math|P> is some positive
      pressure in <with|font-shape|italic|Pascals> and\ 

      <item><math|V> is defined so:

      <\itemize-dot>
        <item><math|(P,n)\<in\>V(x <with|mode|text| Pascals>)> if <math|P=x>

        <item><math|(P,n)\<in\>V(y <with|mode|text| moles>)> if <math|n=y>

        <item><math|(P,n)\<in\>V(z <with|mode|text| Kelvin>)> if
        <math|z=<frac|P|n\<cdot\>R>>
      </itemize-dot>

      <item>Finally, <math|(P,n)\<sim\>(P<rprime|'>,n<rprime|'>)> if and only
      if <math|z=<frac|P|n\<cdot\>R>>
    </itemize-dot>
  </itemize-dot>

  Thermometer Models (Visualization)

  <\itemize-dot>
    <item>We can visualize the information states of the thermometer in a box
    as follows:

    <big-figure|FIXME Picture of Thermometer information
    states|<label|thermometer-picture>>
  </itemize-dot>

  Thermometers are People Too<math|\<ldots\>> Sort of

  <\itemize-dot>
    <item>The view suggests that, under the view put forward by modern
    <with|font-family|ss|EL>, objects like thermometers have mental states
    just like people.

    <item>This view originates with Daniel Dennet in his book
    <with|font-shape|italic|The Intentional Stance>:

    <\quote-env>
      <with|font-shape|italic|It is not that we attribute (or should
      attribute) beliefs and desires only to things in which we find internal
      representations, but rather that when we discover some object for which
      the intentional strategy works, we endeavor to interpret some of its
      internal states or processes as internal representations. What makes
      some internal feature of a thing a representation could only be its
      role in regulating the behavior of an intentional system.>

      \;

      Now the reason for stressing our kinship with the thermostat should be
      clear. There is no magic moment in the transition from a simple
      thermostat to a system that really has an internal representation of
      the world around it. The thermostat has a minimally demanding
      representation of the world, fancier thermostats have more demanding
      representations of the world, fancier robots for helping around the
      house would have still more demanding representations of the world.
      Finally you reach us.
    </quote-env>
  </itemize-dot>

  Unreasonable

  <\itemize-dot>
    <item>Sadly, while the above framework of <with|font-family|ss|EL> is a
    powerful system for analyzing informational aspects of knowledge, it does
    not do a very good job at modeling justifications

    <item><with|font-shape|italic|That is to say, <with|font-family|ss|S5>
    Kripke structures, like thermometers, can convey the informational
    interplay of knowledge for an epistemic agent, but they cannot adequately
    model anything recognizable as a <with|font-series|bold|reason> for
    possessing knowledge>
  </itemize-dot>

  Desiderata

  <\itemize-dot>
    <item>Roughly, one way model reasons in epistemic logic would be to
    enforce the following:

    <\with|par-mode|center>
      <math|\<bbb-M\>,w\<Vdash\>K \<phi\>> if and only if the agent has some
      kind of proof of <math|\<phi\>> at <math|w>
    </with>

    <item>The purpose of <with|font-shape|italic|Evidentialist Logic>, or
    <with|font-shape|small-caps|EviL>, is to provide a framework which
    enforces this

    <item>Analogous approaches are taken by
    <with|font-shape|italic|Justification Logic>, developed at CUNY, and in
    Fernando Velazquez-Quesada's PhD thesis
  </itemize-dot>

  The Language of <with|font-shape|small-caps|EviL>

  <\itemize-dot>
    <item>Define the language <math|<with|math-font|cal|L><rsub|0>> as basic
    propositional logic over an infinite set of proposition letters
    <math|\<Phi\>>:

    <\equation*>
      \<phi\><with|mode|text| >\<colons\>=<with|mode|text|
      >p\<in\>\<Phi\><with|mode|text| >\|<with|mode|text|
      >\<phi\>\<rightarrow\>\<psi\><with|mode|text| >\|<with|mode|text|
      >\<bot\>
    </equation*>

    <item>The language <math|<with|math-font|cal|L><rsub|<with|font-shape|small-caps|EviL>>>
    extends this as follows:

    <\equation*>
      \<phi\>\<colons\>=<with|mode|text| >p\<in\>\<Phi\><with|mode|text|
      >\|<with|mode|text| >\<phi\>\<rightarrow\>\<psi\><with|mode|text|
      >\|<with|mode|text| >\<bot\><with|mode|text| >\|<with|mode|text|
      >\<box\>\<phi\><with|mode|text| >\|<with|mode|text|
      >\<boxminus\>\<phi\><with|mode|text| >\|<with|mode|text|
      >\<boxplus\>\<phi\><with|mode|text| >\|<with|mode|text|
      >\<circlearrowleft\>
    </equation*>
  </itemize-dot>

  Reading the <math|<with|math-font|cal|L><rsub|<with|font-shape|small-caps|EviL>>>

  <\itemize-dot>
    <item>Before jumping into the semantics, here is how to read these
    operations:

    <\itemize-minus>
      <math|\<box\>\<phi\>><item>means the agent can deduce <math|\<phi\>>
      from her basic beliefs

      <with|mode|math|\<circlearrowleft\>><item>means that all of the agent's
      basic beliefs are true

      <math|\<ominus\>\<phi\>><item>holds if there is a way the agent could
      cast some of her experience and background assumptions into doubt, and
      after which <math|\<phi\>> holds

      <math|\<oplus\>\<phi\>><item>holds if there is a way that the agent
      could extend her beliefs (or perhaps remember something) in some way,
      after which <math|\<phi\>> holds
    </itemize-minus>
  </itemize-dot>

  <\itemize-dot>
    <item>The following deserves special attention:

    <\itemize-minus>
      <math|\<box\>\<phi\>><item>means the agent can deduce <math|\<phi\>>
      from her basic beliefs
    </itemize-minus>

    <item>This is in line with a <with|font-shape|italic|foundationalist>
    epistemology - namely that there are some beliefs that get the privilege
    of being <em|basic> or <em|grounded>. \ Other beliefs are then deduced
    appropriately from these basic beliefs.

    <item>This is not so unreasonable -- to help develop one's intuitions
    regarding this, here are some examples of Basic and Non-Basic beliefs
    which some people might hold

    <\with|par-mode|center>
      <tabular|<tformat|<twith|table-lborder|1px>|<twith|table-rborder|1px>|<twith|table-bborder|1px>|<twith|table-tborder|1px>|<cwith|1|2|2|2|cell-lborder|1px>|<cwith|1|5|1|2|cell-halign|c>|<cwith|1|5|1|2|cell-width|>|<cwith|1|5|1|2|cell-hmode|auto>|<cwith|4|5|1|1|cell-halign|c>|<cwith|4|5|1|1|cell-width|>|<cwith|4|5|1|1|cell-hmode|auto>|<cwith|6|6|1|1|cell-halign|c>|<cwith|5|7|2|2|cell-lborder|1px>|<cwith|5|7|2|2|cell-rborder|1px>|<cwith|5|7|2|2|cell-bborder|1px>|<cwith|5|7|2|2|cell-tborder|1px>|<cwith|6|7|2|2|cell-tborder|0pt>|<cwith|5|6|2|2|cell-bborder|0pt>|<cwith|4|4|1|2|cell-bborder|1px>|<cwith|4|4|1|1|cell-lborder|1px>|<cwith|4|4|1|1|cell-rborder|1px>|<cwith|4|4|1|1|cell-bborder|1px>|<cwith|4|4|1|1|cell-tborder|1px>|<cwith|4|4|2|2|cell-lborder|1px>|<cwith|4|4|2|2|cell-rborder|1px>|<cwith|4|4|2|2|cell-bborder|1px>|<cwith|4|4|2|2|cell-tborder|1px>|<cwith|1|1|2|2|cell-lborder|1px>|<cwith|1|1|2|2|cell-rborder|1px>|<cwith|1|1|2|2|cell-bborder|1px>|<cwith|1|1|2|2|cell-tborder|1px>|<cwith|1|1|1|1|cell-lborder|1px>|<cwith|1|1|1|1|cell-rborder|1px>|<cwith|1|1|1|1|cell-bborder|1px>|<cwith|1|1|1|1|cell-tborder|1px>|<cwith|3|3|2|2|cell-lborder|1px>|<table|<row|<cell|Basic>|<cell|Non-Basic>>|<row|<cell|I
      have a hand on the end of my arm>|<cell|I cannot go to Albert Heijn
      right now>>|<row|<cell|>|<cell|(because I'm in a Logic Tea
      talk)>>|<row|<cell|Peano Arithmetic is
      consistent>|<cell|<with|font-shape|small-caps|EviL> is
      consistent>>|<row|<cell|>|<cell|God is not benevolent>>|<row|<cell|God
      is benevolent>|<cell|(because there is so much
      suffering>>|<row|<cell|>|<cell| in the world)>>>>>
    </with>
  </itemize-dot>

  Charlotte Example

  <\itemize-dot>
    <item>To get a feel of how <with|font-shape|small-caps|EviL> works,
    consider an agent named Charlotte. \ In this toy model, Charlotte has two
    basic beliefs:\ 

    <\description-dash>
      <item*|<with|mode|math|\<checked\>>>If Abelard has tried to kill Alex,
      then Alex has survived

      <item*|<math|\<checked\>>>Abelard has tried to kill Alex
    </description-dash>

    <item>Assume these two statements are true. \ Then we have that\ 

    <\equation*>
      \<circlearrowleft\>\<wedge\>\<box\><with|mode|text|``Alex has
      survived''>
    </equation*>

    <item>Moreover, logical conclusions drawn from true premises are true.
    \ In this little example, it is also the case that

    <\equation*>
      <with|mode|text|``Alex has survived''>
    </equation*>
  </itemize-dot>

  A First Stab a Definition of Knowledge

  <\itemize-dot>
    <item>One first idea of how to define knowledge in this system would then
    be:

    <\equation*>
      K\<phi\>\<assign\>\<circlearrowleft\>\<wedge\>\<box\>\<phi\>
    </equation*>

    <item>This is not an adequate analysis, however
  </itemize-dot>

  <\itemize-dot>
    <item>But suppose that Charlotte also believes the following:

    <\description-dash>
      <item*|<with|mode|math|\<checked\>>>If Abelard has tried to kill Alex,
      then Alex has survived

      <item*|<math|\<checked\>>>Abelard has tried to kill Alex

      <item*|<with|mode|math|\<times\>>>Vietnam is south of Malaysia
    </description-dash>

    <item>The last statement is false<math|\<ldots\>>

    <item>Moreover, now not all of Charlotte's basic beliefs are true, so
    under the previous definition we have

    <\equation*>
      \<neg\>K<with|mode|text|``Alex has survived''>
    </equation*>
  </itemize-dot>

  \;

  <\itemize-dot>
    <\equation*>
      \<neg\>K<with|mode|text|``Alex has survived''>
    </equation*>

    <item>This is not in line with intuition however, since it seems like
    Vietnam's position with relation to Malaysia is <em|irrelevant> to
    Charlotte's conclusions about Alex

    <item>If Charlotte could <em|cast into doubt> the idea that ``Vietnam is
    south of Malaysia'', and then carry on deducing with only relevant
    information, she might reasonably be expected to have Knowledge

    <item>A refined definition of knowledge that accomodates the above
    observation is:

    <\equation*>
      K\<phi\>\<assign\>\<ominus\>(\<circlearrowleft\>\<wedge\>\<box\>\<phi\>)
    </equation*>
  </itemize-dot>

  Logical Omniscience

  <\itemize-dot>
    <item>This definition of knowledge has the feature that the following is
    <with|font-shape|italic|invalid> (known as logical omniscience):

    <\equation*>
      <frac|K\<phi\><with|mode|text| \ \ \ >K(\<phi\>\<rightarrow\>\<psi\>)|K
      \<psi\>>\<times\>
    </equation*>
  </itemize-dot>

  Example

  <\itemize-dot>
    <\itemize-minus>
      <math|A><item>It's the harvest season for cranberries

      <math|B><item>If it's the harvest season for cranberries, there is a
      risk of bear attacks

      <math|C><item>A study in 2008 showed that black bear attacks in
      cranberry bogs in New England have been in steady decline
    </itemize-minus>
  </itemize-dot>

  framebreak

  <\itemize-dot>
    <\itemize-minus>
      <math|A><item>It's the harvest season for cranberries

      <math|B><item>If it's the harvest season for cranberries, there is a
      risk of bear attacks

      <math|C><item>A study in 2008 showed that black bear attacks in
      cranberry bogs in New England have been in steady decline
    </itemize-minus>

    <item>The field biologist knows the first statement given her background
    in botony, and the second statement given her background in biology
  </itemize-dot>

  framebreak

  <\itemize-dot>
    <\itemize-minus>
      <math|\<checked\>><item>It's is the harvest season for cranberries

      <math|\<checked\>><item>If it's the harvest season for cranberries,
      there is a risk of bear attacks

      <math|\<times\>><item>A study in 2008 showed that black bear attacks in
      cranberry bogs in New England have been in steady decline
    </itemize-minus>

    <item>Now assume the study is erroneous - perhaps not enough evidence was
    gathered
  </itemize-dot>

  framebreak

  <\itemize-dot>
    <\itemize-minus>
      <math|A><item>It's the harvest season for cranberries

      <math|B><item>If it's the harvest season for cranberries, bears will be
      attracted, hence there is a risk of bear attacks

      <math|C><item>A study in 2008 showed that black bear attacks in
      cranberry bogs in New England have been in steady decline
    </itemize-minus>

    <item>In the case of this biologist, she cannot think about bear attacks
    in cranberry bogs in New England without appealing to the 2008 study

    <item>When thinking about bears in New England, she cannot cast it into
    doubt and just use her other beliefs as a biologist
  </itemize-dot>

  framebreak

  <\itemize-dot>
    <item>The biologist will not have knowledge of the risk of bear attacks
    in this scenario, only inconsistent ideas on the subject

    <item>Despite the fact that she knows that it is harvest season for
    cranberries and if it is harvest season for cranberries, there's a risk
    of bear attacks, she cannot formulate a sound argument for there being a
    risk of bear attacks
  </itemize-dot>

  <with|font-shape|small-caps|EviL> Semantics

  <\itemize-dot>
    <item><with|font-shape|small-caps|EviL> models are sets
    <math|<with|math-font|Euler|M>\<subseteq\>\<wp\>\<Phi\>\<times\>\<wp\><with|math-font|cal|L><rsub|0>>;
    that is to say they are sets of pairs <math|(a,A)> where:

    <\itemize-dot>
      <item><math|a> is a set of proposition letters

      <item><math|A> is a set of proposition formulae -- the agent's basic
      beliefs
    </itemize-dot>
  </itemize-dot>

  framebreak

  <\itemize-dot>
    <item>The <with|font-shape|small-caps|EviL> truth predicate
    <math|\<Vvdash\>> is defined recursively as follows:

    <\itemize-dot>
      <item><math|<with|math-font|Euler|M>,(a,A)\<Vvdash\>p\<Longleftrightarrow\>p\<in\>a>

      <item><math|<with|math-font|Euler|M>,(a,A)\<Vvdash\>\<phi\>\<rightarrow\>\<psi\>\<Longleftrightarrow\>>either
      <with|mode|math|<with|math-font|Euler|M>,(a,A)<neg|\<Vvdash\>>\<phi\>>
      or <with|mode|math|<with|math-font|Euler|M>,(a,A)\<Vvdash\>\<psi\>>

      <item><with|mode|math|<with|math-font|Euler|M>,(a,A)\<Vvdash\>\<bot\>>
      never

      <item><with|mode|math|<with|math-font|Euler|M>,(a,A)\<Vvdash\>\<box\>\<phi\>\<Longleftrightarrow\>\<forall\>(b,B)\<in\><with|math-font|Euler|M>.>
      if <with|mode|math|<with|math-font|Euler|M>,(b,B)\<Vvdash\>\<alpha\>>
      for all <math|\<alpha\>\<in\>A>, then
      <with|mode|math|<with|math-font|Euler|M>,(b,B)\<Vvdash\>\<phi\>>

      <item><with|mode|math|<with|math-font|Euler|M>,(a,A)\<Vvdash\>\<boxminus\>\<phi\>\<Longleftrightarrow\>\<forall\>(b,B)\<in\><with|math-font|Euler|M>.>
      if <math|a=b> and <math|A\<supseteq\>B>, then
      <with|mode|math|<with|math-font|Euler|M>,(b,B)\<Vvdash\>\<phi\>>

      <item><with|mode|math|<with|math-font|Euler|M>,(a,A)\<Vvdash\>\<boxplus\>\<phi\>\<Longleftrightarrow\>\<forall\>(b,B)\<in\><with|math-font|Euler|M>.>
      if <math|a=b> and <math|A\<subseteq\>B>, then
      <with|mode|math|<with|math-font|Euler|M>,(b,B)\<Vvdash\>\<phi\>>

      <item><with|mode|math|<with|math-font|Euler|M>,(a,A)\<Vvdash\>\<circlearrowleft\>\<Longleftrightarrow\>>if
      <with|mode|math|<with|math-font|Euler|M>,(a,A)\<Vvdash\>\<alpha\>> for
      all <math|\<alpha\>\<in\>A>
    </itemize-dot>
  </itemize-dot>

  Theorem Theorem

  <\equation*>
    <with|math-font|Euler|M>,(a,A)\<Vvdash\>\<box\>\<phi\>\<Longleftrightarrow\>Th(<with|math-font|Euler|M>)\<cup\>A\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<phi\>
  </equation*>

  This illustrates that the semantics of <with|font-shape|small-caps|EviL>
  reflect the intuitions previously presented

  \;

  Conservative Extension

  Let <math|K> denote basic modal logic. \ <with|font-shape|small-caps|EviL>
  is a <with|font-shape|italic|conservative extension> of <math|K>; that is,
  for any modal formula <math|\<phi\>>

  <\equation*>
    \<vdash\><rsub|K>\<phi\>\<Longleftrightarrow\>\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<phi\>
  </equation*>

  But <math|K> is not the same as <with|font-shape|small-caps|EviL>, since in
  modal logic you do not have <math|\<boxplus\>,\<boxminus\>> and
  <with|mode|math|\<circlearrowleft\>>

  \;

  <with|font-shape|small-caps|EviL> Is Not Compact

  Suppose the set of proposition letters <math|\<Phi\>> is infinite.
  \ Consider the infinite set of formulae, <math|\<tau\>[\<Phi\>]>, where
  <math|\<tau\>:\<Phi\>\<rightarrow\><with|math-font|cal|L><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>>
  is:

  <\equation*>
    \<tau\>(p)\<assign\>p\<wedge\>\<box\>p\<wedge\>\<diamondsuit\>\<top\>\<wedge\>\<box\>\<box\>\<bot\>
  </equation*>

  Every finite subset of <math|\<tau\>[\<Phi\>]> is satisfiable in
  <with|font-shape|small-caps|EviL>, but not the entirity

  Hence, <with|font-shape|small-caps|EviL> is <with|font-shape|italic|not
  compact>

  \;

  <with|font-shape|small-caps|EviL> Axioms

  <with|font-shape|small-caps|EviL> is <with|font-shape|italic|not normal>;
  it is not closed under replacement of proposition letters with arbitrary
  formulae. \ Hence the axioms of <with|font-shape|small-caps|EviL> are
  schematic:

  <\with|par-mode|center>
    <tabular|<tformat|<cwith|2|2|1|1|cell-halign|r>|<cwith|1|1|2|2|cell-halign|c>|<cwith|2|2|2|2|cell-halign|c>|<cwith|3|3|1|1|cell-halign|l>|<cwith|4|4|1|1|cell-halign|l>|<cwith|5|5|1|1|cell-halign|l>|<cwith|6|6|1|1|cell-halign|l>|<cwith|1|1|1|1|cell-halign|l>|<table|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>|<cell|<math|\<vdash\><rsub|<with|font-shape|small-caps|EviL>>p\<rightarrow\>\<boxplus\>p<space|1spc>(\<ast\>)>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>(\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<chi\>)\<rightarrow\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<phi\>\<rightarrow\>\<chi\>>>|<cell|<math|\<vdash\><rsub|<with|font-shape|small-caps|EviL>>p\<rightarrow\>\<boxminus\>p<space|1spc>(\<ast\>)>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>(\<neg\>\<phi\>\<rightarrow\>\<neg\>\<psi\>)\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>|<cell|<math|\<vdash\><rsub|<with|font-shape|small-caps|EviL>>\<phi\>\<rightarrow\>\<boxminus\>\<oplus\>\<phi\>>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<box\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<box\>\<phi\>\<rightarrow\>\<box\>\<psi\>>>|<cell|<with|mode|math|\<vdash\><rsub|<with|font-shape|small-caps|EviL>>\<phi\>\<rightarrow\>\<boxplus\>\<ominus\>\<phi\>>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<boxminus\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<boxminus\>\<phi\>\<rightarrow\>\<boxminus\>\<psi\>>>|<cell|<math|\<vdash\><rsub|<with|font-shape|small-caps|EviL>>\<box\>\<phi\>\<rightarrow\>\<box\>\<boxminus\>\<phi\>>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<boxplus\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<boxplus\>\<phi\>\<rightarrow\>\<boxplus\>\<psi\>>>|<cell|<math|\<vdash\><rsub|<with|font-shape|small-caps|EviL>>\<box\>\<phi\>\<rightarrow\>\<box\>\<boxplus\>\<phi\>>>>>>>
  </with>

  <tabular|<tformat|<cwith|1|1|1|1|cell-halign|l>|<cwith|2|2|1|1|cell-halign|l>|<cwith|5|5|1|1|cell-halign|l>|<cwith|4|4|1|1|cell-halign|c>|<cwith|5|5|1|1|cell-halign|l>|<table|<row|<cell|<math|\<vdash\><rsub|<with|font-shape|small-caps|EviL>>\<boxminus\>\<phi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\><rsub|<with|font-shape|small-caps|EviL>>\<boxminus\>\<phi\>\<rightarrow\>\<boxminus\>\<boxminus\>\<phi\>>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|font-shape|small-caps|EviL>>\<box\>\<phi\>\<rightarrow\>\<boxplus\>\<box\>\<phi\>>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<circlearrowleft\>\<rightarrow\>\<box\>\<phi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<circlearrowleft\>\<rightarrow\>\<boxminus\>\<circlearrowleft\>>>>>>>

  <with|mode|math|(\<ast\>)> indicates a non-normal axiom

  <with|font-shape|small-caps|EviL> is closed under modus ponens, and
  Necessitation for <math|\<box\>>, <math|\<boxminus\>> and
  <math|\<boxplus\>>

  \;

  <with|font-shape|small-caps|EviL> Soundness and Weak Completeness

  For all formulae <math|\<phi\>> in <math|<with|math-font|cal|L><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>>

  <\eqnarray*>
    <tformat|<table|<row|<cell|>|<cell|<with|math-font|Euler|M,>(a,A)\<Vvdash\>\<phi\><with|mode|text|
    for all <with|font-shape|small-caps|EviL> models
    <math|<with|math-font|Euler|M>>, for all
    <math|(a,A)\<in\><with|math-font|Euler|M>>>>|<cell|>>|<row|<cell|>|<cell|<with|mode|text|if
    and only if>>|<cell|>>|<row|<cell|>|<cell|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<phi\>>|<cell|>>>>
  </eqnarray*>

  Moreover, <with|font-shape|small-caps|EviL> has the finite model property
  (where all of the basic beliefs sets are finite too)

  \;

  Complexity

  <with|font-shape|small-caps|EviL> is decidable; specifically, we have the
  following bounds on its complexity:

  <\with|par-mode|center>
    PSPACE<math|\<subseteq\>><with|font-shape|small-caps|EviL><math|\<subseteq\>>EXP2
  </with>

  \;

  Elimination Theorem

  One way to read <math|\<box\>\<phi\>> as ``the agent believes
  <math|\<phi\>>'' and <math|\<diamondsuit\>\<phi\>> as ``the agent can
  imagine <math|\<phi\>>''

  It is well known that they are each other's <with|font-shape|italic|dual>,
  so they exhibit quite a bit of symmetry

  Since <math|\<boxplus\>> is associated with going up in basic beliefs, it
  may be thought of as sort of symmetrical to <math|\<boxminus\>>, which is
  associated with going down in basic beliefs

  framebreak

  This symmetry is exhibited in the following validities:

  <\with|par-mode|center>
    <tabular|<tformat|<cwith|1|1|2|2|cell-halign|l>|<table|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<boxminus\>p\<leftrightarrow\>p>>|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<boxplus\>p\<leftrightarrow\>p>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<boxminus\>\<neg\>p\<leftrightarrow\>\<neg\>p>>|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<boxplus\>\<neg\>p\<leftrightarrow\>\<neg\>p>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<boxminus\>\<diamondsuit\>\<phi\>\<leftrightarrow\>\<diamondsuit\>\<phi\>>>|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<boxplus\>\<box\>\<phi\>\<leftrightarrow\>\<box\>\<phi\>>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<oplus\>\<diamondsuit\>\<phi\>\<leftrightarrow\>\<diamondsuit\>\<phi\>>>|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<ominus\>\<box\>\<phi\>\<leftrightarrow\>\<box\>\<phi\>>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<boxminus\>\<boxminus\>\<phi\>\<leftrightarrow\>\<boxminus\>\<phi\>>>|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<boxplus\>\<boxplus\>\<phi\>\<leftrightarrow\>\<boxplus\>\<phi\>>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<boxminus\>\<oplus\>\<phi\>\<leftrightarrow\>\<oplus\>\<phi\>>>|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<boxplus\>\<ominus\>\<phi\>\<leftrightarrow\>\<ominus\>\<phi\>>>>|<row|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>><with|mode|math|\<boxminus\>\<circlearrowleft\>\<leftrightarrow\>\<circlearrowleft\>>>|<cell|<with|mode|math|\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>><with|mode|math|\<boxplus\>\<neg\>\<circlearrowleft\>\<leftrightarrow\>\<neg\>\<circlearrowleft\>>>>>>>
  </with>

  Note that all of these validities are <with|font-shape|italic|reductions>
  -- the formula on left of the biimplication is always more complex than the
  formula on the right

  framebreak

  Now consider the following two <with|font-shape|italic|dual> fragments of
  <math|<with|math-font|cal|L><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>>:

  <htab|5mm><with|mode|math|\<phi\><with|mode|text|
  >\<colons\>=<with|mode|text| >p<with|mode|text| >\|<with|mode|text|
  >\<neg\>p<with|mode|text| >\|<with|mode|text| >\<top\><with|mode|text|
  >\|<with|mode|text| >\<bot\><with|mode|text| >\|<with|mode|text|
  >\<circlearrowleft\><with|mode|text| >\|<with|mode|text|
  >\<phi\>\<vee\>\<psi\><with|mode|text| >\|<with|mode|text|
  >\<phi\>\<wedge\>\<psi\><with|mode|text| >\|<with|mode|text|
  >\<diamondsuit\> \<phi\><with|mode|text| >\|<with|mode|text|
  >\<boxminus\>\<phi\><with|mode|text| >\|<with|mode|text|
  >\<oplus\>\<phi\>><htab|5mm>(<math|<with|math-font|cal|L><rsub|A>>)

  <htab|5mm><with|mode|math|\<phi\><with|mode|text|
  >\<colons\>=<with|mode|text| >\<neg\>p<with|mode|text| >\|<with|mode|text|
  >p<with|mode|text| >\|<with|mode|text| >\<bot\><with|mode|text|
  >\|<with|mode|text| >\<top\><with|mode|text| >\|<with|mode|text|
  >\<neg\>\<circlearrowleft\><with|mode|text| >\|<with|mode|text|
  >\<phi\>\<wedge\>\<psi\><with|mode|text| >\|<with|mode|text|
  >\<phi\>\<vee\>\<psi\><with|mode|text| >\|<with|mode|text| >\<box\>
  \<phi\><with|mode|text| >\|<with|mode|text|
  >\<ominus\>\<phi\><with|mode|text| >\|<with|mode|text|
  >\<boxplus\>\<phi\>><htab|5mm>(<math|<with|math-font|cal|L><rsub|B>>)

  The observed reductions give rise to <with|font-shape|italic|elimination
  theorems> on these fragments

  framebreak

  Specifically, recursively define an <with|font-shape|italic|elimination
  operation> <math|(\<cdot\>)<rsup|\<ast\>>> such that

  <\with|par-mode|center>
    <tabular|<tformat|<cwith|2|2|2|2|cell-halign|l>|<cwith|3|3|2|2|cell-halign|l>|<cwith|1|1|2|2|cell-halign|l>|<cwith|2|2|1|1|cell-halign|l>|<cwith|1|1|1|1|cell-halign|l>|<table|<row|<cell|<math|p<rsup|\<ast\>>><with|mode|math|\<assign\>p>>|<cell|<math|(\<neg\>p)<rsup|\<ast\>>\<assign\>\<neg\>p>>>|<row|<cell|<math|\<top\><rsup|\<ast\>>><with|mode|math|\<assign\>\<top\>>>|<cell|<math|\<bot\><rsup|\<ast\>>\<assign\>\<bot\>>>>|<row|<cell|<math|\<circlearrowleft\><rsup|\<ast\>>><with|mode|math|\<assign\>\<circlearrowleft\>>>|<cell|<math|(\<neg\>\<circlearrowleft\>)<rsup|\<ast\>>><with|mode|math|\<assign\>\<neg\>\<circlearrowleft\>>>>|<row|<cell|<with|mode|math|(\<phi\>\<vee\>\<psi\>)<rsup|\<ast\>>\<assign\>\<phi\><rsup|\<ast\>>\<vee\>\<psi\><rsup|\<ast\>>>>|<cell|<with|mode|math|(\<phi\>\<wedge\>\<psi\>)<rsup|\<ast\>>\<assign\>\<phi\><rsup|\<ast\>>\<wedge\>\<psi\><rsup|\<ast\>>>>>|<row|<cell|<math|(\<diamondsuit\>\<phi\>)<rsup|\<ast\>>\<assign\>\<diamondsuit\>(\<phi\><rsup|\<ast\>>)>>|<cell|<math|(\<box\>\<phi\>)<rsup|\<ast\>>\<assign\>\<box\>(\<phi\><rsup|\<ast\>>)>>>|<row|<cell|<math|(\<boxminus\>\<phi\>)<rsup|\<ast\>>\<assign\>\<phi\><rsup|\<ast\>>>>|<cell|<math|(\<ominus\>\<phi\>)<rsup|\<ast\>>\<assign\>\<phi\><rsup|\<ast\>>>>>|<row|<cell|<math|(\<oplus\>\<phi\>)<rsup|\<ast\>>\<assign\>\<phi\><rsup|\<ast\>>>>|<cell|<math|(\<boxplus\>\<phi\>)<rsup|\<ast\>>\<assign\>\<phi\><rsup|\<ast\>>>>>>>>
  </with>

  framebreak

  For <math|\<phi\>\<in\><with|math-font|cal|L><rsub|A>\<cup\><with|math-font|cal|L><rsub|B>>
  we have

  <\equation*>
    \<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<phi\>\<leftrightarrow\>\<phi\><rsup|\<ast\>>
  </equation*>

  This is a consequence of the previous observed reductions, along with
  duality

  framebreak

  This gives rise to the following <with|font-shape|small-caps|EviL> validity

  (FIXME: Insert very silly picture)

  \;

  <with|font-shape|small-caps|EviL> Intuitionism

  In <with|font-shape|italic|Reason, Truth and History> (1981), Hilary Putnam
  writes:

  <\quote-env>
    To claim a statement is true is to claim that it could be justified (pg.
    56)
  </quote-env>

  This intuition presents two things:

  <\enumerate-numeric>
    <item>It suggests an anti-realist, constructivist perspective on truth

    <item>Reading <math|\<box\>p> as ``<math|p> can be justified'' is natural
    in <with|font-shape|small-caps|EviL>. This suggests that truth conditions
    in models for intuitionistic logic can be translated into deductions an
    <with|font-shape|small-caps|EviL> agent might perform
  </enumerate-numeric>

  framebreak

  Recall the grammar of intuitionistic logic:

  <htab|5mm><with|mode|math|\<phi\><with|mode|text|
  >\<colons\>=<with|mode|text| >p<with|mode|text| >\|<with|mode|text|
  >\<bot\><with|mode|text| >\|<with|mode|text|
  >\<phi\>\<vee\>\<psi\><with|mode|text| >\|<with|mode|text|
  >\<phi\>\<wedge\>\<psi\><with|mode|text| >\|<with|mode|text|
  >\<phi\>\<rightarrow\>\<psi\>><htab|5mm>(<math|<with|math-font|cal|L><rsub|Int>>)

  \;

  Define <math|(\<cdot\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>:<with|mode|text|<math|<with|math-font|cal|L><rsub|Int>>>\<rightarrow\><with|math-font|cal|L><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>>
  to be a variation on the Godel Tarski McKinsey embedding:

  <\with|par-mode|center>
    <tabular|<tformat|<cwith|2|2|1|1|cell-valign|c>|<cwith|3|3|1|1|cell-row-span|1>|<cwith|3|3|1|1|cell-col-span|2>|<cwith|1|1|2|2|cell-halign|l>|<cwith|3|3|1|1|cell-halign|c>|<table|<row|<cell|<math|p<rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<assign\>\<box\>p>>|<cell|<math|\<bot\><rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<assign\>\<bot\>>>>|<row|<cell|<math|(\<phi\>\<vee\>\<psi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<assign\>(\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<vee\>\<psi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>)<rsup|>>>|<cell|<math|(\<phi\>\<wedge\>\<psi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<assign\>(\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<wedge\>\<psi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>)<rsup|>>>>|<row|<cell|<math|(\<phi\>\<rightarrow\>\<psi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<assign\>\<boxplus\>(\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<rightarrow\>\<psi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>)>>|<cell|>>>>>
  </with>

  framebreak

  We have the following:

  <\equation*>
    \<vdash\><rsub|Int>\<phi\>\<Longleftrightarrow\>\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviL>>>
  </equation*>

  Intuitionist Logic as <with|font-shape|small-caps|EviL> Epistemic Logic

  The above embedding involves equating truth conditions in Intuitionistic
  Kripke Structures with beliefs in <with|font-shape|small-caps|EviL> models

  It may be modified to <math|(\<cdot\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>:<with|mode|text|<math|<with|math-font|cal|L><rsub|Int>>>\<rightarrow\><with|math-font|cal|L><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>>

  <\with|par-mode|center>
    <tabular|<tformat|<cwith|2|2|1|1|cell-valign|c>|<cwith|3|3|1|1|cell-row-span|1>|<cwith|3|3|1|1|cell-col-span|2>|<cwith|1|1|2|2|cell-halign|l>|<cwith|3|3|1|1|cell-halign|c>|<table|<row|<cell|<math|p<rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>\<assign\>K
    p>>|<cell|<math|\<bot\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>\<assign\>\<bot\>>>>|<row|<cell|<math|(\<phi\>\<vee\>\<psi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>\<assign\>(\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>\<vee\>\<psi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>)<rsup|>>>|<cell|<math|(\<phi\>\<wedge\>\<psi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>\<assign\>(\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>\<wedge\>\<psi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>)<rsup|>>>>|<row|<cell|<math|(\<phi\>\<rightarrow\>\<psi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>\<assign\>\<boxplus\>(\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>\<rightarrow\>\<psi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>)>>|<cell|>>>>>
  </with>

  \ Where <math|K\<phi\>\<assign\>\<ominus\>(\<circlearrowleft\>\<wedge\>\<box\>\<phi\>)>,
  the formulation of knowledge previously suggested

  framebreak

  One again, we have:

  <\equation*>
    \<vdash\><rsub|Int>\<phi\>\<Longleftrightarrow\>\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiL>>>
  </equation*>

  Intuitionistic Logic as the Logic of Imagination

  One way to read <math|\<box\>\<phi\>> is ``can deduce <math|\<phi\>>'', and
  its dual <math|\<diamondsuit\>\<phi\>> as ``can imagine <math|\<phi\>>''

  Because of the symmetry of <math|\<boxplus\>> and <math|\<boxminus\>>, and
  their interplay with <math|\<box\>> and <math|\<diamondsuit\>> as
  previously illustrated, we have yet another embedding
  <math|(\<cdot\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>:<with|mode|text|<math|<with|math-font|cal|L><rsub|Int>>>\<rightarrow\><with|math-font|cal|L><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>>
  of intuitionistic logic into <with|font-shape|small-caps|EviL>:

  <\with|par-mode|center>
    <tabular|<tformat|<cwith|2|2|1|1|cell-valign|c>|<cwith|3|3|1|1|cell-row-span|1>|<cwith|3|3|1|1|cell-col-span|2>|<cwith|1|1|2|2|cell-halign|l>|<cwith|3|3|1|1|cell-halign|c>|<table|<row|<cell|<math|p<rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>\<assign\>\<diamondsuit\>
    p>>|<cell|<math|\<bot\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>\<assign\>\<bot\>>>>|<row|<cell|<math|(\<phi\>\<vee\>\<psi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>\<assign\>(\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>\<vee\>\<psi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>)<rsup|>>>|<cell|<math|(\<phi\>\<wedge\>\<psi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>\<assign\>(\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>\<wedge\>\<psi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>)<rsup|>>>>|<row|<cell|<math|(\<phi\>\<rightarrow\>\<psi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>\<assign\>\<boxminus\>(\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>\<rightarrow\>\<psi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>)>>|<cell|>>>>>
  </with>

  framebreak

  As before, we have:

  <\equation*>
    \<vdash\><rsub|Int>\<phi\>\<Longleftrightarrow\>\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EviiiL>>>
  </equation*>

  Modal Intuitionistic Logic

  Furthermore, this embedding can be extended to the modal intuitionistic
  logic <with|mode|math|ImK<rsub|\<box\>>>:

  <htab|5mm><with|mode|math|\<phi\><with|mode|text|
  >\<colons\>=<with|mode|text| >p<with|mode|text| >\|<with|mode|text|
  >\<bot\><with|mode|text| >\|<with|mode|text|
  >\<phi\>\<vee\>\<psi\><with|mode|text| >\|<with|mode|text|
  >\<phi\>\<wedge\>\<psi\><with|mode|text| >\|<with|mode|text|
  >\<phi\>\<rightarrow\>\<psi\><with|mode|text| >\|<with|mode|text|
  >\<box\>\<phi\>><htab|5mm>(<math|<with|math-font|cal|L><rsub|ImK<rsub|\<box\>>>>)

  This gives rise to <math|(\<cdot\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>:<with|mode|text|<math|<with|math-font|cal|L><rsub|Int>>>\<rightarrow\><with|math-font|cal|L><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>>

  <\with|par-mode|center>
    <tabular|<tformat|<cwith|2|2|1|1|cell-valign|c>|<cwith|1|1|2|2|cell-halign|l>|<table|<row|<cell|<math|p<rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>\<assign\>\<box\>
    p>>|<cell|<math|\<bot\><rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>\<assign\>\<bot\>>>>|<row|<cell|<math|(\<phi\>\<vee\>\<psi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>\<assign\>(\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>\<vee\>\<psi\><rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>)<rsup|>>>|<cell|<math|(\<phi\>\<wedge\>\<psi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>\<assign\>(\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>\<wedge\>\<psi\><rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>)<rsup|>>>>|<row|<cell|<with|mode|math|(\<phi\>\<rightarrow\>\<psi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>\<assign\>\<boxplus\>(\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>\<rightarrow\>\<psi\><rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>)>>|<cell|<with|mode|math|(\<box\>\<phi\>)<rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>\<assign\>\<box\>\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>>>>>>>
  </with>

  Not surprisingly, we have:

  <\equation*>
    \<vdash\><rsub|ImK<rsub|\<box\>>>\<phi\>\<Longleftrightarrow\>\<vdash\><rsub|<with|mode|text|<with|font-shape|small-caps|EviL>>>\<phi\><rsup|<with|mode|text|<with|font-shape|small-caps|EixL>>>
  </equation*>

  Conclusion

  <with|font-shape|small-caps|EviL> admittedly presents a somewhat different
  perspective on knowledge than traditional epistemic logic

  Regardless, the tools of <with|font-shape|small-caps|EviL> and
  <with|font-family|ss|EL> are the same; they are after all both modal logics

  It is my sincerest hope that <with|font-shape|small-caps|EviL> will help
  the field to progress into new areas of investigation
</body>

<\initial>
  <\collection>
    <associate|language|american>
    <associate|page-type|letter>
    <associate|sfactor|3>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|?>>
    <associate|auto-2|<tuple|2|?>>
    <associate|auto-3|<tuple|3|?>>
    <associate|thermometer-picture|<tuple|2|?>>
  </collection>
</references>