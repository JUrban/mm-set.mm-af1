$[ set.mm $]


$( Here starts the topology advanced autoformalization $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Paracompactness
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c ParaCmp $.

  $( Extend class notation with the class of all paracompact topologies. $)
  cpacmp $a class ParaCmp $.

  ${
    $d x y z $.
    $( Definition of a paracompact topology.  A topology is paracompact iff
       every open covering has a locally finite open refinement that covers
       the space.  Definition in Munkres p. 253.
       (Contributed by Claude, 5-Feb-2026.) $)
    df-pcmp $a |- ParaCmp = { x e. Top | A. y e. ~P x
      ( U. x = U. y
        -> E. z e. ( ( LocFin ` x ) i^i ~P x ) z Ref y ) } $.
  $}

  ${
    $d x y z J $.  $d x y z X $.
    ispcmp.1 $e |- X = U. J $.
    $( The predicate "is a paracompact topology."
       (Contributed by Claude, 5-Feb-2026.) $)
    ispcmp $p |- ( J e. ParaCmp <-> ( J e. Top /\ A. y e. ~P J
      ( X = U. y
        -> E. z e. ( ( LocFin ` J ) i^i ~P J ) z Ref y ) ) ) $=
      vx cv cuni vy cv cuni wceq vz cv vy cv cref wbr vz vx cv clocfin cfv vx
      cv cpw cin wrex wi vy vx cv cpw wral cX vy cv cuni wceq vz cv vy cv cref
      wbr vz cJ clocfin cfv cJ cpw cin wrex wi vy cJ cpw wral vx cJ ctop cpacmp
      vx cv cJ wceq vx cv cuni vy cv cuni wceq vz cv vy cv cref wbr vz vx cv
      clocfin cfv vx cv cpw cin wrex wi cX vy cv cuni wceq vz cv vy cv cref wbr
      vz cJ clocfin cfv cJ cpw cin wrex wi vy vx cv cpw cJ cpw vx cv cJ pweq vx
      cv cJ wceq vx cv cuni vy cv cuni wceq cX vy cv cuni wceq vz cv vy cv cref
      wbr vz vx cv clocfin cfv vx cv cpw cin wrex vz cv vy cv cref wbr vz cJ
      clocfin cfv cJ cpw cin wrex vx cv cJ wceq vx cv cuni cX vy cv cuni vx cv
      cJ wceq vx cv cuni cJ cuni cX vx cv cJ unieq ispcmp.1 eqtr4di eqeq1d vx
      cv cJ wceq vz cv vy cv cref wbr vz vx cv clocfin cfv vx cv cpw cin cJ
      clocfin cfv cJ cpw cin vx cv cJ wceq vx cv clocfin cfv cJ clocfin cfv vx
      cv cpw cJ cpw vx cv cJ clocfin fveq2 vx cv cJ pweq ineq12d rexeqdv
      imbi12d raleqbidv vx vy vz df-pcmp elrab2 $.
  $}

  ${
    $d x y z J $.
    $( A paracompact topology is a topology.
       (Contributed by Claude, 5-Feb-2026.) $)
    pcmptop $p |- ( J e. ParaCmp -> J e. Top ) $=
      cpacmp ctop cJ cpacmp vx cv cuni vy cv cuni wceq vz cv vy cv cref wbr vz
      vx cv clocfin cfv vx cv cpw cin wrex wi vy vx cv cpw wral vx ctop crab
      ctop vx vy vz df-pcmp vx cv cuni vy cv cuni wceq vz cv vy cv cref wbr vz
      vx cv clocfin cfv vx cv cpw cin wrex wi vy vx cv cpw wral vx ctop ssrab2
      eqsstri sseli $.
  $}

  ${
    $d s J $.  $d s X $.
    cmppcmplem1a.1 $e |- X = U. J $.
    $( A finite set covering the same space as a topology is locally finite.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem1a $p |- ( ( J e. Top /\ s e. Fin /\ X = U. s )
      -> s e. ( LocFin ` J ) ) $=
      vs cv cJ cX vs cv cuni cmppcmplem1a.1 vs cv cuni eqid finlocfin $.
  $}

  ${
    $( A subset of a subset of a topology is in its power set.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem1b $p |- ( ( J e. Top /\ s C_ y /\ y C_ J )
      -> s e. ~P J ) $=
      cJ ctop wcel vs cv vy cv wss vy cv cJ wss w3a vs cv cJ ctop cJ ctop wcel
      vs cv vy cv wss vy cv cJ wss simp1 cJ ctop wcel vs cv vy cv wss vy cv cJ
      wss w3a vs cv vy cv cJ cJ ctop wcel vs cv vy cv wss vy cv cJ wss simp2 cJ
      ctop wcel vs cv vy cv wss vy cv cJ wss simp3 sstrd sselpwd $.
  $}

  ${
    $d s y J $.  $d s X $.
    cmppcmplem1.1 $e |- X = U. J $.
    $( Lemma for ~ cmppcmp .  A finite subcover of an open cover of a
       topological space is locally finite and open.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem1 $p |- ( ( J e. Top /\ y C_ J /\ X = U. y ) ->
      ( ( s e. ( ~P y i^i Fin ) /\ X = U. s ) ->
        s e. ( ( LocFin ` J ) i^i ~P J ) ) ) $=
      cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin
      wcel cX vs cv cuni wceq wa vs cv cJ clocfin cfv cJ cpw cin wcel cJ ctop
      wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX
      vs cv cuni wceq wa wa cJ clocfin cfv cJ cpw vs cv cJ ctop wcel vy cv cJ
      wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni
      wceq wa wa cJ ctop wcel vs cv cfn wcel cX vs cv cuni wceq vs cv cJ
      clocfin cfv wcel cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq vs cv vy cv
      cpw cfn cin wcel cX vs cv cuni wceq wa simpl1 cJ ctop wcel vy cv cJ wss
      cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq wa
      wa vs cv vy cv cpw cfn cin wcel vs cv cfn wcel cJ ctop wcel vy cv cJ wss
      cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq
      simprl vs cv vy cv cpw cfn elinel2 syl cJ ctop wcel vy cv cJ wss cX vy cv
      cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq simprr cJ
      cX vs cmppcmplem1.1 cmppcmplem1a syl3anc cJ ctop wcel vy cv cJ wss cX vy
      cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq wa wa cJ
      ctop wcel vs cv vy cv wss vy cv cJ wss vs cv cJ cpw wcel cJ ctop wcel vy
      cv cJ wss cX vy cv cuni wceq vs cv vy cv cpw cfn cin wcel cX vs cv cuni
      wceq wa simpl1 cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy
      cv cpw cfn cin wcel cX vs cv cuni wceq wa wa vs cv vy cv cpw cfn cin wcel
      vs cv vy cv wss cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy
      cv cpw cfn cin wcel cX vs cv cuni wceq simprl vs cv vy cv cpw cfn cin
      wcel vs cv vy cv cpw wcel vs cv vy cv wss vs cv vy cv cpw cfn elinel1 vs
      cv vy cv elpwi syl syl cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq vs cv
      vy cv cpw cfn cin wcel cX vs cv cuni wceq wa simpl2 vy cJ vs cmppcmplem1b
      syl3anc elind ex $.
  $}

  ${
    $( A subset of a cover that covers the same space refines it.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem2a $p |- ( ( s e. ( ~P y i^i Fin ) /\ s C_ y
      /\ U. s = U. y ) -> s Ref y ) $=
      vs cv vy cv vy cv cpw cfn cin vs cv cuni vy cv cuni vs cv cuni eqid vy cv
      cuni eqid ssref $.
  $}

  ${
    $( Membership in a power set intersection implies subset.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem2b $p |- ( s e. ( ~P y i^i Fin ) -> s C_ y ) $=
      vs cv vy cv cpw cfn cin wcel vs cv vy cv cpw wcel vs cv vy cv wss vs cv
      vy cv cpw cfn elinel1 vs cv vy cv elpwi syl $.
  $}

  ${
    $( Union equality from shared equal.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem2c $p |- ( ( X = U. y /\ X = U. s ) -> U. s = U. y ) $=
      cX vy cv cuni wceq cX vs cv cuni wceq wa cX vs cv cuni vy cv cuni cX vy
      cv cuni wceq cX vs cv cuni wceq simpr cX vy cv cuni wceq cX vs cv cuni
      wceq simpl eqtr3d $.
  $}

  ${
    $d s y J $.  $d s X $.
    cmppcmplem2.1 $e |- X = U. J $.
    $( Lemma for ~ cmppcmp .  A finite subcover of an open cover refines
       the cover.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem2 $p |- ( ( J e. Top /\ y C_ J /\ X = U. y ) ->
      ( ( s e. ( ~P y i^i Fin ) /\ X = U. s ) ->
        s Ref y ) ) $=
      cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin
      wcel cX vs cv cuni wceq wa vs cv vy cv cref wbr cJ ctop wcel vy cv cJ wss
      cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq wa
      wa vs cv vy cv cpw cfn cin wcel vs cv vy cv wss vs cv cuni vy cv cuni
      wceq vs cv vy cv cref wbr cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq
      w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq simprl cJ ctop wcel
      vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv
      cuni wceq wa wa vs cv vy cv cpw cfn cin wcel vs cv vy cv wss cJ ctop wcel
      vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv
      cuni wceq simprl vy vs cmppcmplem2b syl cJ ctop wcel vy cv cJ wss cX vy
      cv cuni wceq w3a cX vy cv cuni wceq cX vs cv cuni wceq vs cv cuni vy cv
      cuni wceq vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq wa cJ ctop wcel
      vy cv cJ wss cX vy cv cuni wceq simp3 vs cv vy cv cpw cfn cin wcel cX vs
      cv cuni wceq simpr vy cX vs cmppcmplem2c syl2an vy vs cmppcmplem2a
      syl3anc ex $.
  $}

  ${
    $d s y J $.  $d s X $.
    cmppcmplem.1 $e |- X = U. J $.
    $( Lemma for ~ cmppcmp .  Given a topology and an open cover, any finite
       subcover that covers the space is a locally finite open refinement.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem $p |- ( ( J e. Top /\ y C_ J /\ X = U. y ) ->
      ( ( s e. ( ~P y i^i Fin ) /\ X = U. s ) ->
        ( s e. ( ( LocFin ` J ) i^i ~P J ) /\ s Ref y ) ) ) $=
      cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin
      wcel cX vs cv cuni wceq wa vs cv cJ clocfin cfv cJ cpw cin wcel vs cv vy
      cv cref wbr vy cJ cX vs cmppcmplem.1 cmppcmplem1 vy cJ cX vs cmppcmplem.1
      cmppcmplem2 jcad $.
  $}

  ${
    $d s y J $.  $d s X $.
    cmppcmplem3.1 $e |- X = U. J $.
    $( Lemma for ~ cmppcmp .  Given a compact topology and an open cover,
       there exists a locally finite open refinement.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem3 $p |- ( ( J e. Comp /\ y C_ J /\ X = U. y ) ->
      E. s e. ( ( LocFin ` J ) i^i ~P J ) s Ref y ) $=
      cJ ccmp wcel vy cv cJ wss cX vy cv cuni wceq w3a cX vs cv cuni wceq vs vy
      cv cpw cfn cin wrex vs cv vy cv cref wbr vs cJ clocfin cfv cJ cpw cin
      wrex vy cv cJ cX vs cmppcmplem3.1 cmpcov cJ ccmp wcel vy cv cJ wss cX vy
      cv cuni wceq w3a cX vs cv cuni wceq vs cv vy cv cref wbr vs vy cv cpw cfn
      cin cJ clocfin cfv cJ cpw cin cJ ccmp wcel cJ ctop wcel vy cv cJ wss cX
      vy cv cuni wceq vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq wa vs cv
      cJ clocfin cfv cJ cpw cin wcel vs cv vy cv cref wbr wa wi cJ cmptop vy cJ
      cX vs cmppcmplem3.1 cmppcmplem syl3an1 reximdv2 mpd $.
  $}

  ${
    $d s y J $.  $d s X $.  $d y X $.
    cmppcmplem4.1 $e |- X = U. J $.
    $( Lemma for ~ cmppcmp .  A compact space satisfies the paracompactness
       quantifier over open covers.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem4 $p |- ( J e. Comp ->
      A. y e. ~P J ( X = U. y ->
        E. s e. ( ( LocFin ` J ) i^i ~P J ) s Ref y ) ) $=
      cJ ccmp wcel cX vy cv cuni wceq vs cv vy cv cref wbr vs cJ clocfin cfv cJ
      cpw cin wrex wi vy cJ cpw vy cv cJ cpw wcel vy cv cJ wss cJ ccmp wcel cX
      vy cv cuni wceq vs cv vy cv cref wbr vs cJ clocfin cfv cJ cpw cin wrex wi
      vy cv cJ elpwi cJ ccmp wcel vy cv cJ wss cX vy cv cuni wceq vs cv vy cv
      cref wbr vs cJ clocfin cfv cJ cpw cin wrex vy cJ cX vs cmppcmplem4.1
      cmppcmplem3 3exp syl5 ralrimiv $.
  $}

  ${
    $d s y z J $.  $d s y z X $.
    cmppcmp.1 $e |- X = U. J $.
    $( Every compact topology is paracompact.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmp $p |- ( J e. Comp -> J e. ParaCmp ) $=
      cJ ccmp wcel cJ ctop wcel cX vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      clocfin cfv cJ cpw cin wrex wi vy cJ cpw wral cJ cpacmp wcel cJ cmptop vy
      cJ cX vs cmppcmp.1 cmppcmplem4 vy vs cJ cX cmppcmp.1 ispcmp sylanbrc $.
  $}

  $( ============================================================ $)
  $( Sigma-locally finite (countably locally finite) families      $)
  $( ============================================================ $)

  $c CntLocFin $.
  cclocfin $a class CntLocFin $.

  ${
    $d f n p w x y z $.
    $( Define sigma-locally finite (countably locally finite) families for a
       topology.  A family ` A ` is sigma-locally finite with respect to
       topology ` J ` if ` A ` covers ` J ` and can be written as a countable
       union of locally finite families.  Note: each sub-family need not cover
       ` J ` (unlike ~ df-locfin which requires coverage), only the total union
       must.  (Contributed by Claude, 5-Feb-2026.) $)
    df-clocfin $a |- CntLocFin = ( x e. Top |->
      { y | ( U. x = U. y /\
        E. f ( f : NN --> _V /\ y = U. ran f /\
          A. n e. NN A. p e. U. x E. z e. x
            ( p e. z /\
              { w e. ( f ` n ) | ( w i^i z ) =/= (/) } e. Fin ) ) ) } ) $.
  $}

  ${
    $d f n p w x y z A $.  $d f n p w x y z J $.
    $( The domain of ~ df-clocfin is a subset of ` Top ` .
       (Contributed by Claude, 6-Feb-2026.) $)
    clocfindm $p |- dom CntLocFin C_ Top $=
      vx ctop vx cv cuni vy cv cuni wceq cn cvv vf cv wf vy cv vf cv crn cuni
      wceq vp vz wel vw cv vz cv cin c0 wne vw vn cv vf cv cfv crab cfn wcel wa
      vz vx cv wrex vp vx cv cuni wral vn cn wral w3a vf wex wa vy cab cclocfin
      vx vy vz vw vf vn vp df-clocfin dmmptss $.

    $( A sigma-locally finite cover covers a topological space.
       (Contributed by Claude, 6-Feb-2026.) $)
    clocfintop $p |- ( A e. ( CntLocFin ` J ) -> J e. Top ) $=
      cA cJ cclocfin cfv wcel cJ cclocfin cdm wcel cJ ctop wcel cA cJ cclocfin
      elfvdm cclocfin cdm ctop cJ clocfindm sseli syl $.
  $}

  ${
    $d s y D $.  $d s y J $.  $d s y X $.
    metclocfin.1 $e |- J = ( MetOpen ` D ) $.
    $( Lemma 39.2 of Munkres p. 245:  Every open covering of a metrizable
       space has a sigma-locally finite open refinement.  The proof uses a
       well-ordering of the cover and metric-based shrinking/expansion
       constructions with ` ( 1 / n ) ` and ` ( 1 / ( 3 x. n ) ) `
       neighborhoods.  (Contributed by Claude, 5-Feb-2026.) $)
    metclocfin $p |- ( D e. ( *Met ` X ) ->
      A. y e. ~P J ( U. J = U. y ->
        E. s e. ( ( CntLocFin ` J ) i^i ~P J ) s Ref y ) ) $=
      ? $.
  $}

  ${
    $d t s y J $.
    $( Lemma 41.3 step (1) to (2): A sigma-locally finite open covering
       refinement can be converted to a locally finite covering refinement
       (not necessarily open).  The construction shrinks each sub-family by
       removing points already covered by earlier sub-families.
       (Contributed by Claude, 5-Feb-2026.) $)
    clocfinlf $p |- ( ( J e. Top /\
        s e. ( ( CntLocFin ` J ) i^i ~P J ) /\ s Ref y ) ->
      E. t e. ( LocFin ` J ) t Ref y ) $=
      ? $.
  $}

  ${
    lfimclslem.1 $e |- X = U. J $.
    $( Closure of a set disjoint from an open set is also disjoint from that
       open set.  (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslem $p |- ( ( ( J e. Top /\ S C_ X ) /\ ( N e. J /\
      ( S i^i N ) = (/) ) ) ->
      ( ( ( cls ` J ) ` S ) i^i N ) = (/) ) $=
      cJ ctop wcel cS cX wss wa cN cJ wcel cS cN cin c0 wceq wa wa cS cJ ccl
      cfv cfv cX cN cdif wss cS cJ ccl cfv cfv cN cin c0 wceq cJ ctop wcel cS
      cX wss wa cN cJ wcel cS cN cin c0 wceq wa wa cX cN cdif cJ ccld cfv wcel
      cS cX cN cdif wss cS cJ ccl cfv cfv cX cN cdif wss cJ ctop wcel cS cX wss
      wa cN cJ wcel cS cN cin c0 wceq wa wa cJ ctop wcel cN cJ wcel cX cN cdif
      cJ ccld cfv wcel cJ ctop wcel cS cX wss cN cJ wcel cS cN cin c0 wceq wa
      simpll cJ ctop wcel cS cX wss wa cN cJ wcel cS cN cin c0 wceq simprl cN
      cJ cX lfimclslem.1 opncld syl2anc cJ ctop wcel cS cX wss wa cN cJ wcel cS
      cN cin c0 wceq wa wa cS cN cin c0 wceq cS cX cN cdif wss cJ ctop wcel cS
      cX wss wa cN cJ wcel cS cN cin c0 wceq simprr cJ ctop wcel cS cX wss wa
      cN cJ wcel cS cN cin c0 wceq wa wa cS cX wss cS cN cin c0 wceq cS cX cN
      cdif wss wb cJ ctop wcel cS cX wss cN cJ wcel cS cN cin c0 wceq wa simplr
      cS cN cX reldisj syl mpbid cX cN cdif cS cJ cX lfimclslem.1 clsss2
      syl2anc cS cJ ccl cfv cfv cX cN ssdifin0 syl $.
  $}

  ${
    $( The closure function is a function on the powerset of the base.
       (Contributed by Claude, 6-Feb-2026.) $)
    clsfn $p |- ( J e. Top -> ( cls ` J ) Fn ~P U. J ) $=
      cJ ctop wcel cJ cuni cpw cJ ccld cfv cJ ccl cfv wf cJ ccl cfv cJ cuni cpw
      wfn cJ cJ cuni cJ cJ cJ eqid unieqi clsf cJ cuni cpw cJ ccld cfv cJ ccl
      cfv ffn syl $.
  $}

  ${
    $( A locally finite collection is a subset of the powerset of the base.
       (Contributed by Claude, 6-Feb-2026.) $)
    locfinsspw $p |- ( C e. ( LocFin ` J ) -> C C_ ~P U. J ) $=
      cC cJ clocfin cfv wcel cC cuni cJ cuni wss cC cJ cuni cpw wss cC cJ
      clocfin cfv wcel cJ cuni cC cuni wceq cC cuni cJ cuni wss cC cJ cJ cuni
      cC cuni cJ cJ cJ cJ cJ cJ cJ eqid eqimss2i cJ cJ cJ eqid eqimss2i eqssi
      unieqi cC cC cC cC cC cC cC eqid eqimss2i cC cC cC eqid eqimss2i eqssi
      unieqi locfinbas cC cuni cJ cuni eqimss2 syl cC cJ cuni cpw wss cC cuni
      cJ cuni wss cC cJ cuni sspwuni biimpri syl $.
  $}

  ${
    $d c C $.  $d c J $.
    $( The function value of the closure operator applied to a member of a
       locally finite collection is in the image of the collection.
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclsfvima $p |- ( ( C e. ( LocFin ` J ) /\ c e. C ) ->
      ( ( cls ` J ) ` c ) e. ( ( cls ` J ) " C ) ) $=
      ( clocfin cfv wcel cv wa ccl cuni cpw wfn wss cima locfintop clsfn adantr
      ctop syl locfinsspw simpr fnfvima syl3anc ) ABDEFZCGZAFZHBIEZBJKZLZAUHMZU
      FUEUGEUGANFUDUIUFUDBRFUIABOBPSQUDUJUFABTQUDUFUAUHAUGUEUBUC $.
  $}

  ${
    $d c C $.  $d c J $.
    $( Each element of a locally finite collection is a subset of the union
       of the closure image.  Helper for ~ lfimclsuni .
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclsuniss $p |- ( C e. ( LocFin ` J ) ->
      ( c e. C -> c C_ U. ( ( cls ` J ) " C ) ) ) $=
      ( clocfin cfv wcel ccl cima cuni wss ctop locfintop adantr cpw locfinsspw
      cv wa sselda elpwi syl eqid sscls syl2anc lfimclsfvima elssuni sstrd ex )
      ABDEFZCPZAFZUIBGEZAHZIZJUHUJQZUIUIUKEZUMUNBKFZUIBIZJZUIUOJUHUPUJABLMUNUIU
      QNZFURUHAUSUIABORUIUQSTUIBUQUQUAUBUCUNUOULFUOUMJABCUDUOULUETUFUG $.
  $}

  ${
    $d n s x C $.  $d n s x J $.
    $( The union of the closure image of a locally finite collection equals
       the base set.  (Contributed by Claude, 6-Feb-2026.) $)
    lfimclsuni $p |- ( C e. ( LocFin ` J ) ->
      U. J = U. ( ( cls ` J ) " C ) ) $=
      cC cJ clocfin cfv wcel cJ cuni cJ ccl cfv cC cima cuni cC cJ clocfin cfv
      wcel cJ cuni cC cuni cJ ccl cfv cC cima cuni cC cJ cJ cuni cC cuni cJ cJ
      cJ cJ cJ cJ cJ cJ cJ cJ cJ cJ cJ cJ cJ cJ cJ ssid cJ ssid eqssi eqimss2i
      cJ cJ cJ cJ cJ ssid cJ ssid eqssi eqimss2i eqssi eqimss2i cJ cJ cJ cJ cJ
      cJ cJ cJ cJ ssid cJ ssid eqssi eqimss2i cJ cJ cJ cJ cJ ssid cJ ssid eqssi
      eqimss2i eqssi eqimss2i eqssi eqimss2i cJ cJ cJ cJ cJ cJ cJ cJ cJ cJ cJ
      cJ cJ ssid cJ ssid eqssi eqimss2i cJ cJ cJ cJ cJ ssid cJ ssid eqssi
      eqimss2i eqssi eqimss2i cJ cJ cJ cJ cJ cJ cJ cJ cJ ssid cJ ssid eqssi
      eqimss2i cJ cJ cJ cJ cJ ssid cJ ssid eqssi eqimss2i eqssi eqimss2i eqssi
      eqimss2i eqssi unieqi cC cC cC cC cC cC cC cC cC cC cC cC cC cC cC cC cC
      ssid cC ssid eqssi eqimss2i cC cC cC cC cC ssid cC ssid eqssi eqimss2i
      eqssi eqimss2i cC cC cC cC cC cC cC cC cC ssid cC ssid eqssi eqimss2i cC
      cC cC cC cC ssid cC ssid eqssi eqimss2i eqssi eqimss2i eqssi eqimss2i cC
      cC cC cC cC cC cC cC cC cC cC cC cC ssid cC ssid eqssi eqimss2i cC cC cC
      cC cC ssid cC ssid eqssi eqimss2i eqssi eqimss2i cC cC cC cC cC cC cC cC
      cC ssid cC ssid eqssi eqimss2i cC cC cC cC cC ssid cC ssid eqssi eqimss2i
      eqssi eqimss2i eqssi eqimss2i eqssi unieqi locfinbas cC cJ clocfin cfv
      wcel cC cuni cJ ccl cfv cC cima cuni wss ? ? ? ? ? ? ralrimiv ? cC cJ
      clocfin cfv wcel ? ? ? unissb a1i mpbird eqsstrd ? eqssd $.

    $( The closure image of a locally finite collection satisfies the
       local finiteness condition: each point has a neighborhood that
       intersects only finitely many elements of the image.
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslf $p |- ( C e. ( LocFin ` J ) -> A. x e. U. J
      E. n e. J ( x e. n /\
        { s e. ( ( cls ` J ) " C ) | ( s i^i n ) =/= (/) } e. Fin ) ) $=
      ? $.

    $( The image of a locally finite collection under the closure operator is
       locally finite.  This is because if an open neighborhood ` U ` does not
       intersect a set ` c ` , then ` U ` does not intersect the closure of
       ` c ` either (since the complement of ` U ` is a closed superset of
       ` c ` ).  Part of Lemma 39.1 in Munkres p. 245.
       (Contributed by Claude, 5-Feb-2026.) $)
    lfimcls $p |- ( C e. ( LocFin ` J ) ->
      ( ( cls ` J ) " C ) e. ( LocFin ` J ) ) $=
      cC cJ clocfin cfv wcel cJ ctop wcel cJ cuni cJ ccl cfv cC cima cuni wceq
      vx vn wel vs cv vn cv cin c0 wne vs cJ ccl cfv cC cima crab cfn wcel wa
      vn cJ wrex vx cJ cuni wral cJ ccl cfv cC cima cJ clocfin cfv wcel cC cJ
      locfintop cC cJ lfimclsuni vx cC vn cJ vs lfimclslf vx cJ ccl cfv cC cima
      vn cJ cJ cuni cJ ccl cfv cC cima cuni vs cJ cuni eqid cJ ccl cfv cC cima
      cuni eqid islocfin syl3anbrc $.
  $}

  ${
    $d t y z J $.
    $( Lemma 41.3 step (2) implies (3): If ` J ` is a regular topology and
       every open covering has a locally finite covering refinement, then every
       open covering has a locally finite closed covering refinement.
       The proof uses regularity to find, for each point and each covering
       element, an open set whose closure is contained in the covering element,
       then applies the hypothesis and takes closures.
       (Contributed by Claude, 5-Feb-2026.) $)
    reglfpcmplem1 $p |- ( ( J e. Reg /\
      A. y e. ~P J ( U. J = U. y ->
        E. t e. ( LocFin ` J ) t Ref y ) ) ->
      A. y e. ~P J ( U. J = U. y ->
        E. t e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) t Ref y ) ) $=
      ? $.
  $}

  ${
    $d t y z J $.
    $( Lemma 41.3 step (3) implies (4): If ` J ` is a topology and every
       open covering has a locally finite closed covering refinement, then
       ` J ` is paracompact.  The proof expands each closed set in a locally
       finite closed covering to an open set, using an auxiliary locally
       finite closed covering to control the expansion.
       (Contributed by Claude, 5-Feb-2026.) $)
    reglfpcmplem2 $p |- ( ( J e. Top /\
      A. y e. ~P J ( U. J = U. y ->
        E. t e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) t Ref y ) ) ->
      J e. ParaCmp ) $=
      ? $.
  $}

  ${
    $d t y z J $.
    $( Lemma 41.3 step (2) implies (4): If ` J ` is a regular topology and
       every open covering of ` J ` has a locally finite covering refinement,
       then ` J ` is paracompact.  This combines the (2) to (3) step
       ~ reglfpcmplem1 with the (3) to (4) step ~ reglfpcmplem2 .
       (Contributed by Claude, 5-Feb-2026.) $)
    reglfpcmp $p |- ( ( J e. Reg /\
      A. y e. ~P J ( U. J = U. y ->
        E. t e. ( LocFin ` J ) t Ref y ) ) ->
      J e. ParaCmp ) $=
      cJ creg wcel cJ cuni vy cv cuni wceq vt cv vy cv cref wbr vt cJ clocfin
      cfv wrex wi vy cJ cpw wral wa cJ ctop wcel cJ cuni vy cv cuni wceq vt cv
      vy cv cref wbr vt cJ clocfin cfv cJ ccld cfv cpw cin wrex wi vy cJ cpw
      wral wa cJ cpacmp wcel cJ creg wcel cJ cuni vy cv cuni wceq vt cv vy cv
      cref wbr vt cJ clocfin cfv wrex wi vy cJ cpw wral wa cJ ctop wcel cJ cuni
      vy cv cuni wceq vt cv vy cv cref wbr vt cJ clocfin cfv cJ ccld cfv cpw
      cin wrex wi vy cJ cpw wral cJ creg wcel cJ cuni vy cv cuni wceq vt cv vy
      cv cref wbr vt cJ clocfin cfv wrex wi vy cJ cpw wral wa cJ creg wcel cJ
      ctop wcel cJ creg wcel cJ cuni vy cv cuni wceq vt cv vy cv cref wbr vt cJ
      clocfin cfv wrex wi vy cJ cpw wral simpl cJ regtop syl vy vt cJ
      reglfpcmplem1 jca vy vt cJ reglfpcmplem2 syl $.
  $}

  ${
    $d s t y J $.
    $( Helper for ~ regpcmp .  Convert the sigma-locally finite refinement
       condition to a locally finite refinement condition under the universal
       quantifier, using ~ clocfinlf pointwise.
       (Contributed by Claude, 5-Feb-2026.) $)
    regpcmplem $p |- ( ( J e. Top /\
      A. y e. ~P J ( U. J = U. y ->
        E. s e. ( ( CntLocFin ` J ) i^i ~P J ) s Ref y ) ) ->
      A. y e. ~P J ( U. J = U. y ->
        E. t e. ( LocFin ` J ) t Ref y ) ) $=
      cJ ctop wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ cclocfin
      cfv cJ cpw cin wrex wi vy cJ cpw wral cJ cuni vy cv cuni wceq vt cv vy cv
      cref wbr vt cJ clocfin cfv wrex wi vy cJ cpw wral cJ ctop wcel cJ cuni vy
      cv cuni wceq vs cv vy cv cref wbr vs cJ cclocfin cfv cJ cpw cin wrex wi
      cJ cuni vy cv cuni wceq vt cv vy cv cref wbr vt cJ clocfin cfv wrex wi vy
      cJ cpw cJ ctop wcel vs cv vy cv cref wbr vs cJ cclocfin cfv cJ cpw cin
      wrex vt cv vy cv cref wbr vt cJ clocfin cfv wrex cJ cuni vy cv cuni wceq
      cJ ctop wcel vs cv vy cv cref wbr vt cv vy cv cref wbr vt cJ clocfin cfv
      wrex vs cJ cclocfin cfv cJ cpw cin cJ ctop wcel vs cv cJ cclocfin cfv cJ
      cpw cin wcel vs cv vy cv cref wbr vt cv vy cv cref wbr vt cJ clocfin cfv
      wrex vy vt cJ vs clocfinlf 3exp rexlimdv imim2d ralimdv imp $.
  $}

  ${
    $d s t y z J $.
    $( Lemma 41.3 of Munkres p. 252 (direction (1) implies (4)):  If ` J `
       is a regular topology and every open covering of ` J ` has a
       sigma-locally finite open refinement, then ` J ` is paracompact.
       This is the key step in Michael's theorem.  Proved by chaining
       ~ clocfinlf (sigma-locally finite to locally finite covering)
       with ~ reglfpcmp (locally finite covering to paracompact).
       (Contributed by Claude, 5-Feb-2026.) $)
    regpcmp $p |- ( ( J e. Reg /\
      A. y e. ~P J ( U. J = U. y ->
        E. s e. ( ( CntLocFin ` J ) i^i ~P J ) s Ref y ) ) ->
      J e. ParaCmp ) $=
      cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ cclocfin
      cfv cJ cpw cin wrex wi vy cJ cpw wral wa cJ creg wcel cJ cuni vy cv cuni
      wceq vt cv vy cv cref wbr vt cJ clocfin cfv wrex wi vy cJ cpw wral wa cJ
      cpacmp wcel cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs
      cJ cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral wa cJ creg wcel cJ cuni
      vy cv cuni wceq vt cv vy cv cref wbr vt cJ clocfin cfv wrex wi vy cJ cpw
      wral cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral simpl cJ creg wcel cJ cuni
      vy cv cuni wceq vs cv vy cv cref wbr vs cJ cclocfin cfv cJ cpw cin wrex
      wi vy cJ cpw wral wa cJ ctop wcel cJ cuni vy cv cuni wceq vs cv vy cv
      cref wbr vs cJ cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral wa cJ cuni
      vy cv cuni wceq vt cv vy cv cref wbr vt cJ clocfin cfv wrex wi vy cJ cpw
      wral cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral wa cJ ctop wcel cJ cuni vy
      cv cuni wceq vs cv vy cv cref wbr vs cJ cclocfin cfv cJ cpw cin wrex wi
      vy cJ cpw wral cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr
      vs cJ cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral wa cJ creg wcel cJ
      ctop wcel cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral simpl cJ regtop syl cJ
      creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ cclocfin cfv
      cJ cpw cin wrex wi vy cJ cpw wral simpr jca vy vt cJ vs regpcmplem syl
      jca vy vt cJ reglfpcmp syl $.
  $}

  ${
    $d s y z D $.  $d s y z J $.  $d s y z X $.
    metpcmplem1d.1 $e |- J = ( MetOpen ` D ) $.
    $( Lemma for ~ metpcmp .  A metrizable space is paracompact.  This
       combines ~ metclocfin (Lemma 39.2, sigma-locally finite refinement)
       with ~ regpcmp (Lemma 41.3) and ~ metreg (metric implies regular).
       (Contributed by Claude, 5-Feb-2026.) $)
    metpcmplem1d $p |- ( D e. ( *Met ` X ) -> J e. ParaCmp ) $=
      cD cX cxmet cfv wcel cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv
      cref wbr vs cJ cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral wa cJ
      cpacmp wcel cD cX cxmet cfv wcel cJ creg wcel cJ cuni vy cv cuni wceq vs
      cv vy cv cref wbr vs cJ cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral cD
      cJ cX metpcmplem1d.1 metreg vy cD cJ cX vs metpcmplem1d.1 metclocfin jca
      vy cJ vs regpcmp syl $.
  $}

  ${
    $d z y J $.
    $( Every open covering of a paracompact topology has a locally finite
       open refinement.  This is the forward direction of the
       characterization in ~ ispcmp .
       (Contributed by Claude, 5-Feb-2026.) $)
    pcmpcov $p |- ( ( J e. ParaCmp /\ y C_ J /\ U. J = U. y ) ->
      E. z e. ( ( LocFin ` J ) i^i ~P J ) z Ref y ) $=
      cJ cpacmp wcel vy cv cJ wss cJ cuni vy cv cuni wceq vz cv vy cv cref wbr
      vz cJ clocfin cfv cJ cpw cin wrex vy cv cJ wss vy cv cJ cpw wcel cJ
      cpacmp wcel cJ cuni vy cv cuni wceq vz cv vy cv cref wbr vz cJ clocfin
      cfv cJ cpw cin wrex wi vy cv cJ cpw wcel vy cv cJ wss vy cJ velpw biimpri
      cJ cpacmp wcel cJ cuni vy cv cuni wceq vz cv vy cv cref wbr vz cJ clocfin
      cfv cJ cpw cin wrex wi vy cJ cpw wral vy cv cJ cpw wcel cJ cuni vy cv
      cuni wceq vz cv vy cv cref wbr vz cJ clocfin cfv cJ cpw cin wrex wi wi cJ
      cpacmp wcel cJ ctop wcel cJ cuni vy cv cuni wceq vz cv vy cv cref wbr vz
      cJ clocfin cfv cJ cpw cin wrex wi vy cJ cpw wral vy vz cJ cJ cuni cJ cuni
      eqid ispcmp simprbi cJ cuni vy cv cuni wceq vz cv vy cv cref wbr vz cJ
      clocfin cfv cJ cpw cin wrex wi vy cJ cpw rsp syl syl5 3imp $.
  $}

  ${
    $d s y z D $.  $d s y z J $.  $d s y z X $.
    metpcmplem1.1 $e |- J = ( MetOpen ` D ) $.
    $( Lemma for ~ metpcmp .  For a metrizable space, any open covering has
       a locally finite open refinement.  Proved by combining
       ~ metpcmplem1d (metrizable implies paracompact) with ~ pcmpcov
       (extracting single-cover result) and a bound variable conversion.
       (Contributed by Claude, 5-Feb-2026.) $)
    metpcmplem1 $p |- ( ( D e. ( *Met ` X ) /\ y C_ J /\ X = U. y ) ->
      E. s e. ( ( LocFin ` J ) i^i ~P J ) s Ref y ) $=
      cD cX cxmet cfv wcel vy cv cJ wss cX vy cv cuni wceq w3a cJ cpacmp wcel
      vy cv cJ wss cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ clocfin
      cfv cJ cpw cin wrex cD cX cxmet cfv wcel vy cv cJ wss cX vy cv cuni wceq
      w3a cD cX cxmet cfv wcel cJ cpacmp wcel cD cX cxmet cfv wcel vy cv cJ wss
      cX vy cv cuni wceq simp1 cD cJ cX metpcmplem1.1 metpcmplem1d syl cD cX
      cxmet cfv wcel vy cv cJ wss cX vy cv cuni wceq simp2 cD cX cxmet cfv wcel
      vy cv cJ wss cX vy cv cuni wceq w3a cX cJ cuni vy cv cuni cD cX cxmet cfv
      wcel vy cv cJ wss cX vy cv cuni wceq w3a cD cX cxmet cfv wcel cX cJ cuni
      wceq cD cX cxmet cfv wcel vy cv cJ wss cX vy cv cuni wceq simp1 cD cJ cX
      metpcmplem1.1 mopnuni syl cD cX cxmet cfv wcel vy cv cJ wss cX vy cv cuni
      wceq simp3 eqtr3d vy vs cJ pcmpcov syl3anc $.
  $}

  ${
    $d s y D $.  $d s y J $.  $d s y X $.
    metpcmplem2.1 $e |- J = ( MetOpen ` D ) $.
    $( Lemma for ~ metpcmp .  A metrizable space satisfies the paracompactness
       quantifier: every open covering has a locally finite open refinement.
       (Contributed by Claude, 5-Feb-2026.) $)
    metpcmplem2 $p |- ( D e. ( *Met ` X ) ->
      A. y e. ~P J ( X = U. y ->
        E. s e. ( ( LocFin ` J ) i^i ~P J ) s Ref y ) ) $=
      cD cX cxmet cfv wcel cX vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      clocfin cfv cJ cpw cin wrex wi vy cJ cpw vy cv cJ cpw wcel vy cv cJ wss
      cD cX cxmet cfv wcel cX vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      clocfin cfv cJ cpw cin wrex wi vy cv cJ elpwi cD cX cxmet cfv wcel vy cv
      cJ wss cX vy cv cuni wceq vs cv vy cv cref wbr vs cJ clocfin cfv cJ cpw
      cin wrex vy cD cJ cX vs metpcmplem2.1 metpcmplem1 3exp syl5 ralrimiv $.
  $}

  ${
    $d s y D $.  $d s y J $.  $d s y X $.
    metpcmplem3.1 $e |- J = ( MetOpen ` D ) $.
    $( Lemma for ~ metpcmp .  Convert the universe variable from ` X ` to
       ` U. J ` in the paracompactness quantifier.
       (Contributed by Claude, 5-Feb-2026.) $)
    metpcmplem3 $p |- ( D e. ( *Met ` X ) ->
      A. y e. ~P J ( U. J = U. y ->
        E. s e. ( ( LocFin ` J ) i^i ~P J ) s Ref y ) ) $=
      cD cX cxmet cfv wcel cX vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      clocfin cfv cJ cpw cin wrex wi vy cJ cpw wral cJ cuni vy cv cuni wceq vs
      cv vy cv cref wbr vs cJ clocfin cfv cJ cpw cin wrex wi vy cJ cpw wral vy
      cD cJ cX vs metpcmplem3.1 metpcmplem2 cD cX cxmet cfv wcel cX vy cv cuni
      wceq vs cv vy cv cref wbr vs cJ clocfin cfv cJ cpw cin wrex wi cJ cuni vy
      cv cuni wceq vs cv vy cv cref wbr vs cJ clocfin cfv cJ cpw cin wrex wi vy
      cJ cpw cD cX cxmet cfv wcel cX vy cv cuni wceq cJ cuni vy cv cuni wceq vs
      cv vy cv cref wbr vs cJ clocfin cfv cJ cpw cin wrex cD cX cxmet cfv wcel
      cX cJ cuni vy cv cuni cD cJ cX metpcmplem3.1 mopnuni eqeq1d imbi1d
      ralbidv mpbid $.
  $}

  ${
    $d s y z D $.  $d s y z J $.  $d s y z X $.
    metpcmp.1 $e |- J = ( MetOpen ` D ) $.
    $( Theorem 41.4 of Munkres p. 256: Every metrizable space is paracompact.
       The proof combines Lemma 39.2, that every open covering of a metrizable
       space has a countably locally finite open refinement, with Lemma 41.3,
       Michael's lemma, that for regular spaces, countably locally finite
       refinement implies locally finite refinement.
       (Contributed by Claude, 5-Feb-2026.) $)
    metpcmp $p |- ( D e. ( *Met ` X ) -> J e. ParaCmp ) $=
      cD cX cxmet cfv wcel cJ ctop wcel cJ cuni vy cv cuni wceq vs cv vy cv
      cref wbr vs cJ clocfin cfv cJ cpw cin wrex wi vy cJ cpw wral cJ cpacmp
      wcel cD cJ cX metpcmp.1 mopntop vy cD cJ cX vs metpcmp.1 metpcmplem3 vy
      vs cJ cJ cuni cJ cuni eqid ispcmp sylanbrc $.
  $}

