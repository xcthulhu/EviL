<TeXmacs|1.0.7.2>

<style|generic>

<\body>
  <with|font-shape|small-caps|EviL>

  <\itemize-dot>
    <item>Epistemic Logic (<with|font-family|ss|EL>) is a branch of applied
    modal logic

    <item>Since its conception in (FIXME:HINTIKKA), <with|font-family|ss|EL>
    traditionally takes knowledge as a primitive notion

    <item>The language of basic <with|font-family|ss|EL> is the common
    language of modal logic:

    <\equation*>
      \<phi\><space|1spc> \<colons\><space|-0.6spc>=<space|1spc>p\<in\>\<Phi\><space|1spc>\|<space|1spc>\<phi\>\<rightarrow\>\<psi\><space|1spc>\|<space|1spc>\<bot\><space|1spc>\|<space|1spc>\<box\>\<phi\>
    </equation*>
  </itemize-dot>

  \;

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

  \;

  <\itemize-dot>
    <item>Basic <with|font-family|ss|EL> of one agent is generally assumed to
    be the modal logic <with|font-family|ss|S5>

    <item>The axioms of <with|font-family|ss|S5> are:

    <\itemize-dot>
      <item>All classical propositional tautologies

      <item><math|\<box\>\<phi\>\<rightarrow\>\<phi\>><htab|5mm>Axiom
      <math|T>

      <with|font-shape|italic|Truth: If the agent knows something, then its
      true>

      <item><math|\<box\>\<phi\>\<rightarrow\>\<box\>\<box\>\<phi\>><htab|5mm>Axiom
      <math|4>

      <with|font-shape|italic|Positive Introspection: If the agent knows
      something, she knows that she knows it>

      <item><math|\<neg\>\<box\>\<phi\>\<rightarrow\>\<box\>\<neg\>\<box\>\<phi\>><htab|5mm>Axiom
      <math|5>

      <\with|font-shape|italic>
        Negative Introspection: There are no unknown unknowns (despite Donald
        Rumsfeld)
      </with>

      <item><math|\<box\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<box\>\<phi\>\<rightarrow\>\<box\>\<psi\>><htab|5mm>Axiom
      <math|K>

      <with|font-shape|italic|Logical Omniscience: The agent knows all the
      logical consequences of her knowledge>
    </itemize-dot>
  </itemize-dot>

  \;

  <\itemize-dot>
    <item><with|font-family|ss|EL> is also closed under the following rules:

    <htab|5mm><with|mode|math|<with|math-display|true|<frac|\<vdash\>\<phi\><space|1em>\<vdash\>\<phi\>\<rightarrow\>\<psi\>|\<vdash\>\<psi\>>>><htab|5mm><math|<with|math-display|true|<frac|\<vdash\>\<phi\>|\<vdash\>\<box\>\<phi\>>>><htab|5mm>
  </itemize-dot>

  \;

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

  \;

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

      <item><math|\<bbb-M\>,w\<Vdash\>\<box\>\<phi\>\<Longleftrightarrow\>>forall
      <math|v\<in\>W>, if <math|w\<sim\>v> then
      <math|\<bbb-M\>,v\<Vdash\>\<phi\>>
    </itemize-dot>

    <item>Such a model is called an <with|font-family|ss|S5> model
  </itemize-dot>

  \;

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

  \;

  <\itemize-dot>
    <item>There is no one answer for how many mols of gas are in the chamber.
    \ Rather, the answer is governed by the <with|font-shape|italic|ideal gas
    law>:

    <\equation*>
      P V = n R T
    </equation*>

    <item>Here <math|P> is the <with|font-shape|italic|pressure>, <math|V> is
    the <with|font-shape|italic|volume>, <math|n> stands for
    <with|font-shape|italic|moles>, <math|R> is the
    <with|font-shape|italic|ideal gas constant>, and <math|T> is the
    <with|font-shape|italic|temperature>

    <item>We may use epistemic logic to model the beliefs of this thermometer
    in a box. \ The following minor adaptation of the basic epistemic logic
    grammar is suited to this purpose:

    <\equation*>
      \<phi\><with|mode|text| >\<colons\><space|-0.8spc>=<with|mode|text| >x
      <with|mode|text| Pascals><with|mode|text| >\|<with|mode|text|
      >y<with|mode|text| moles><with|mode|text| >\|<with|mode|text|
      >z<with|mode|text| Pascals><with|mode|text| >\|<with|mode|text|
      >\<phi\>\<rightarrow\>\<psi\><with|mode|text| >\|<with|mode|text|
      >\<bot\><with|mode|text| >\|<with|mode|text| >\<box\>\<phi\>
    </equation*>
  </itemize-dot>

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

  <\itemize-dot>
    <item>We can visualize the information states of the thermometer in a box
    as follows:

    <big-figure|FIXME Picture of Thermometer information
    states|<label|thermometer-picture>>
  </itemize-dot>

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

  <\itemize-dot>
    <item>
  </itemize-dot>
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
    <associate|thermometer-picture|<tuple|3|?>>
  </collection>
</references>