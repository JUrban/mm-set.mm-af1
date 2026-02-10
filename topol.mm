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
    lfimclslflem1.1 $e |- X = U. J $.
    $( Contrapositive of ~ lfimclslem : if the closure intersects an open
       neighborhood, then the original set also intersects it.
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslflem1 $p |- ( ( ( J e. Top /\ S C_ X ) /\ N e. J ) ->
      ( ( ( ( cls ` J ) ` S ) i^i N ) =/= (/) ->
        ( S i^i N ) =/= (/) ) ) $=
      ( ctop wcel wss wa cin c0 ccl cfv wceq lfimclslem anassrs ex necon3d ) BF
      GADHIZCBGZIZACJZKABLMMCJZKUAUBKNZUCKNZSTUDUEABCDEOPQR $.
  $}

  ${
    $( The closure function is a function on the powerset of the base.
       (Contributed by Claude, 6-Feb-2026.) $)
    clsfn $p |- ( J e. Top -> ( cls ` J ) Fn ~P U. J ) $=
      cJ ctop wcel cJ cuni cpw cJ ccld cfv cJ ccl cfv wf cJ ccl cfv cJ cuni cpw
      wfn cJ cJ cuni cJ cJ cJ cJ cJ cJ cJ eqid eqimss2i cJ cJ cJ eqid eqimss2i
      eqssi unieqi clsf cJ cuni cpw cJ ccld cfv cJ ccl cfv ffn syl $.
  $}

  ${
    $( A locally finite collection is a subset of the powerset of the base.
       (Contributed by Claude, 6-Feb-2026.) $)
    locfinsspw $p |- ( C e. ( LocFin ` J ) -> C C_ ~P U. J ) $=
      cC cJ clocfin cfv wcel cC cuni cJ cuni wss cC cJ cuni cpw wss cC cJ
      clocfin cfv wcel cJ cuni cC cuni wceq cC cuni cJ cuni wss cC cJ cJ cuni
      cC cuni cJ cJ cJ cJ cJ cJ cJ cJ cJ ssid cJ ssid eqssi eqimss2i cJ cJ cJ
      cJ cJ ssid cJ ssid eqssi eqimss2i eqssi unieqi cC cC cC cC cC cC cC eqid
      eqimss2i cC cC cC eqid eqimss2i eqssi unieqi locfinbas cC cuni cJ cuni
      eqimss2 syl cC cJ cuni cpw wss cC cuni cJ cuni wss cC cJ cuni sspwuni
      biimpri syl $.
  $}

  ${
    $d d s C $.  $d d s J $.  $d d s N $.
    $( Under the hypotheses of ~ lfimclslflem2d , show ` d ` has nonempty
       intersection with ` N ` .  Uses ~ lfimclslflem1 together with the
       equality ` ( ( cls `` J ) `` d ) = s ` and ` ( s i^i N ) =/= (/) ` .
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslflem2e $p |- ( ( ( ( ( C e. ( LocFin ` J ) /\ N e. J ) /\
      s e. ( ( cls ` J ) " C ) /\ ( s i^i N ) =/= (/) ) /\ d e. C ) /\
      ( ( cls ` J ) ` d ) = s ) -> ( d i^i N ) =/= (/) ) $=
      cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv
      cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa vd
      cv cJ ccl cfv cfv cN cin c0 wne vd cv cN cin c0 wne cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa vd cv cJ ccl cfv cfv
      cN cin vs cv cN cin c0 cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl
      cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ ccl
      cfv cfv vs cv wceq wa vd cv cJ ccl cfv cfv vs cv cN cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq simpr ineq1d cC cJ
      clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin
      c0 wne w3a vs cv cN cin c0 wne vd cv cC wcel vd cv cJ ccl cfv cfv vs cv
      wceq cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel
      vs cv cN cin c0 wne simp3 ad2antrr eqnetrd cC cJ clocfin cfv wcel cN cJ
      wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC
      wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa cJ ctop wcel vd cv cJ cuni wss
      wa cN cJ wcel wa vd cv cJ ccl cfv cfv cN cin c0 wne vd cv cN cin c0 wne
      wi cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs
      cv cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa
      cJ ctop wcel vd cv cJ cuni wss wa cN cJ wcel cC cJ clocfin cfv wcel cN cJ
      wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC
      wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa cJ ctop wcel vd cv cJ cuni wss
      cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv
      cN cin c0 wne w3a cJ ctop wcel vd cv cC wcel vd cv cJ ccl cfv cfv vs cv
      wceq cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel
      vs cv cN cin c0 wne w3a cC cJ clocfin cfv wcel cJ ctop wcel cC cJ clocfin
      cfv wcel cN cJ wcel vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne
      simp1l cC cJ locfintop syl ad2antrr cC cJ clocfin cfv wcel cN cJ wcel wa
      vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel wa vd
      cv cJ ccl cfv cfv vs cv wceq wa vd cv cJ cuni cpw wcel vd cv cJ cuni wss
      cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv
      cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa cC
      cJ cuni cpw wss vd cv cC wcel vd cv cJ cuni cpw wcel cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      cC cJ cuni cpw wss vd cv cC wcel vd cv cJ ccl cfv cfv vs cv wceq cC cJ
      clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin
      c0 wne w3a cC cJ clocfin cfv wcel cC cJ cuni cpw wss cC cJ clocfin cfv
      wcel cN cJ wcel vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne simp1l
      cC cJ locfinsspw syl ad2antrr cC cJ clocfin cfv wcel cN cJ wcel wa vs cv
      cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel vd cv cJ
      ccl cfv cfv vs cv wceq simplr cC cJ cuni cpw vd cv ssel2 syl2anc vd cv cJ
      cuni elpwi syl jca cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv
      cC cima wcel vs cv cN cin c0 wne w3a cN cJ wcel vd cv cC wcel vd cv cJ
      ccl cfv cfv vs cv wceq cC cJ clocfin cfv wcel cN cJ wcel vs cv cJ ccl cfv
      cC cima wcel vs cv cN cin c0 wne simp1r ad2antrr jca vd cv cJ cN cJ cuni
      cJ cuni eqid lfimclslflem1 syl mpd $.
  $}

  ${
    $d c d s C $.  $d c d s J $.  $d c d s N $.
    $( Given ` d e. C ` and ` ( ( cls `` J ) `` d ) = s ` with ` ( s i^i N )
       =/= (/) ` , show ` s ` is in the closure image of the subcollection
       intersecting ` N ` .  Core of ~ lfimclslflem2c .
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslflem2d $p |- ( ( ( ( C e. ( LocFin ` J ) /\ N e. J ) /\
      s e. ( ( cls ` J ) " C ) /\ ( s i^i N ) =/= (/) ) /\ d e. C ) ->
      ( ( ( cls ` J ) ` d ) = s ->
        s e. ( ( cls ` J ) " { c e. C | ( c i^i N ) =/= (/) } ) ) ) $=
      cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv
      cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq vs cv
      cJ ccl cfv vc cv cN cin c0 wne vc cC crab cima wcel cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa vd cv cJ ccl cfv cfv
      vs cv cJ ccl cfv vc cv cN cin c0 wne vc cC crab cima cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq simpr cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa cJ ccl cfv cJ cuni
      cpw wfn vc cv cN cin c0 wne vc cC crab cJ cuni cpw wss vd cv vc cv cN cin
      c0 wne vc cC crab wcel vd cv cJ ccl cfv cfv cJ ccl cfv vc cv cN cin c0
      wne vc cC crab cima wcel cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ
      ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ
      ccl cfv cfv vs cv wceq wa cJ ctop wcel cJ ccl cfv cJ cuni cpw wfn cC cJ
      clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin
      c0 wne w3a vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa cC cJ
      clocfin cfv wcel cJ ctop wcel cC cJ clocfin cfv wcel cN cJ wcel wa vs cv
      cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a cC cJ clocfin cfv wcel vd
      cv cC wcel vd cv cJ ccl cfv cfv vs cv wceq cC cJ clocfin cfv wcel cN cJ
      wcel vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne simp1l ad2antrr cC
      cJ locfintop syl cJ clsfn syl cC cJ clocfin cfv wcel cN cJ wcel wa vs cv
      cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ
      ccl cfv cfv vs cv wceq wa vc cv cN cin c0 wne vc cC crab cC cJ cuni cpw
      vc cv cN cin c0 wne vc cC ssrab2 cC cJ clocfin cfv wcel cN cJ wcel wa vs
      cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel wa vd cv
      cJ ccl cfv cfv vs cv wceq wa cC cJ clocfin cfv wcel cC cJ cuni cpw wss cC
      cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN
      cin c0 wne w3a cC cJ clocfin cfv wcel vd cv cC wcel vd cv cJ ccl cfv cfv
      vs cv wceq cC cJ clocfin cfv wcel cN cJ wcel vs cv cJ ccl cfv cC cima
      wcel vs cv cN cin c0 wne simp1l ad2antrr cC cJ locfinsspw syl sstrid cC
      cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN
      cin c0 wne w3a vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa vd cv
      vc cv cN cin c0 wne vc cC crab wcel vd cv cC wcel vd cv cN cin c0 wne cC
      cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN
      cin c0 wne w3a vd cv cC wcel vd cv cJ ccl cfv cfv vs cv wceq simplr cC cJ
      cN vs vd lfimclslflem2e vd cv vc cv cN cin c0 wne vc cC crab wcel vd cv
      cC wcel vd cv cN cin c0 wne wa wb cC cJ clocfin cfv wcel cN cJ wcel wa vs
      cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel wa vd cv
      cJ ccl cfv cfv vs cv wceq wa vc cv cN cin c0 wne vd cv cN cin c0 wne vc
      vd cv cC vc vd weq vc cv cN cin vd cv cN cin c0 vc cv vd cv cN ineq1
      neeq1d elrab a1i mpbir2and cJ cuni cpw vc cv cN cin c0 wne vc cC crab cJ
      ccl cfv vd cv fnfvima syl3anc eqeltrrd ex $.
  $}

  ${
    $d c d s C $.  $d c d s J $.  $d c d s N $.
    $( Core argument for ~ lfimclslflem2a : if ` s ` is in the closure image
       of ` C ` and intersects ` N ` , then ` s ` is in the closure image of
       the subcollection intersecting ` N ` .
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslflem2c $p |- ( ( ( C e. ( LocFin ` J ) /\ N e. J ) /\
      s e. ( ( cls ` J ) " C ) /\ ( s i^i N ) =/= (/) ) ->
      s e. ( ( cls ` J ) " { c e. C | ( c i^i N ) =/= (/) } ) ) $=
      cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv
      cN cin c0 wne w3a vs cv cJ ccl cfv cC cima wcel vs cv cJ ccl cfv vc cv cN
      cin c0 wne vc cC crab cima wcel cC cJ clocfin cfv wcel cN cJ wcel wa vs
      cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne simp2 cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vs cv cJ ccl cfv cC cima wcel vd cv cJ ccl cfv cfv vs cv wceq vd cC wrex
      vs cv cJ ccl cfv vc cv cN cin c0 wne vc cC crab cima wcel cC cJ clocfin
      cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne
      w3a vs cv cJ ccl cfv cC cima wcel vd cv cJ ccl cfv cfv vs cv wceq vd cC
      wrex cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel
      vs cv cN cin c0 wne w3a vd cJ cuni cpw cC vs cv cJ ccl cfv cC cJ clocfin
      cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne
      w3a cJ ctop wcel cJ ccl cfv cJ cuni cpw wfn cC cJ clocfin cfv wcel cN cJ
      wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a cC cJ
      clocfin cfv wcel cJ ctop wcel cC cJ clocfin cfv wcel cN cJ wcel vs cv cJ
      ccl cfv cC cima wcel vs cv cN cin c0 wne simp1l cC cJ locfintop syl cJ
      clsfn syl cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima
      wcel vs cv cN cin c0 wne w3a cC cJ clocfin cfv wcel cC cJ cuni cpw wss cC
      cJ clocfin cfv wcel cN cJ wcel vs cv cJ ccl cfv cC cima wcel vs cv cN cin
      c0 wne simp1l cC cJ locfinsspw syl fvelimabd biimpd cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vd cv cJ ccl cfv cfv vs cv wceq vs cv cJ ccl cfv vc cv cN cin c0 wne vc
      cC crab cima wcel vd cC cC cJ cN vs vc vd lfimclslflem2d rexlimdva syld
      mpd $.
  $}

  ${
    $d c s C $.  $d c s J $.  $d c s N $.
    $( Subset inclusion: elements of the closure image intersecting ` N ` are
       in the image of the subcollection intersecting ` N ` .  Helper for
       ~ lfimclslflem2 .  (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslflem2a $p |- ( ( C e. ( LocFin ` J ) /\ N e. J ) ->
      { s e. ( ( cls ` J ) " C ) | ( s i^i N ) =/= (/) } C_
        ( ( cls ` J ) " { c e. C | ( c i^i N ) =/= (/) } ) ) $=
      cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cN cin c0 wne vs cJ ccl cfv cC
      cima cJ ccl cfv vc cv cN cin c0 wne vc cC crab cima cC cJ cN vs vc
      lfimclslflem2c rabssdv $.
  $}

  ${
    $d c s C $.  $d c s J $.  $d c s N $.
    $( Finiteness transfer: if the set of elements of ` C ` that intersect
       ` N ` is finite, then so is the set of elements of ` ( ( cls `` J )
       " C ) ` that intersect ` N ` .  Helper for ~ lfimclslf .
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslflem2 $p |- ( ( C e. ( LocFin ` J ) /\ N e. J /\
      { c e. C | ( c i^i N ) =/= (/) } e. Fin ) ->
      { s e. ( ( cls ` J ) " C ) | ( s i^i N ) =/= (/) } e. Fin ) $=
      ( clocfin cfv wcel cv cin c0 wne crab cfn w3a ccl cima wss syl syl2anc
      wfun cuni cpw ctop simp1 locfintop clsfn fnfun simp3 imafi lfimclslflem2a
      wfn simp2 ssfi ) ABFGHZCBHZEICJKLEAMZNHZOZBPGZUQQZNHZDICJKLDUTAQMZVARZVCN
      HUSUTUAZURVBUSUTBUBUCZULZVEUSBUDHZVGUSUOVHUOUPURUEZABUFSBUGSVFUTUHSUOUPUR
      UIUTUQUJTUSUOUPVDVIUOUPURUMABCDEUKTVAVCUNT $.
  $}

  ${
    $d c C $.  $d c J $.
    $( Each element of a locally finite collection is a subset of the union
       of the closure image.  Helper for ~ lfimclsuni .
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclsuniss $p |- ( C e. ( LocFin ` J ) ->
      ( c e. C -> c C_ U. ( ( cls ` J ) " C ) ) ) $=
      cC cJ clocfin cfv wcel vc cv cC wcel vc cv cJ ccl cfv cC cima cuni wss cC
      cJ clocfin cfv wcel vc cv cC wcel wa vc cv vc cv cJ ccl cfv cfv cJ ccl
      cfv cC cima cuni cC cJ clocfin cfv wcel vc cv cC wcel wa cJ ctop wcel vc
      cv cJ cuni wss vc cv vc cv cJ ccl cfv cfv wss cC cJ clocfin cfv wcel cJ
      ctop wcel vc cv cC wcel cC cJ locfintop adantr cC cJ clocfin cfv wcel vc
      cv cC wcel wa vc cv cC cuni cJ cuni vc cv cC wcel vc cv cC cuni wss cC cJ
      clocfin cfv wcel vc cv cC elssuni adantl cC cJ clocfin cfv wcel cC cuni
      cJ cuni wceq vc cv cC wcel cC cJ clocfin cfv wcel cJ cuni cC cuni cC cJ
      cJ cuni cC cuni cJ cuni eqid cC cC cC cC cC cC cC cC cC ssid cC ssid
      eqssi eqimss2i cC cC cC cC cC ssid cC ssid eqssi eqimss2i eqssi unieqi
      locfinbas eqcomd adantr sseqtrd vc cv cJ cJ cuni cJ cuni eqid sscls
      syl2anc cC cJ clocfin cfv wcel vc cv cC wcel wa vc cv cJ ccl cfv cfv cJ
      ccl cfv cC cima wcel vc cv cJ ccl cfv cfv cJ ccl cfv cC cima cuni wss cC
      cJ clocfin cfv wcel vc cv cC wcel wa cJ ccl cfv cJ cuni cpw wfn cC cJ
      cuni cpw wss vc cv cC wcel vc cv cJ ccl cfv cfv cJ ccl cfv cC cima wcel
      cC cJ clocfin cfv wcel cJ ccl cfv cJ cuni cpw wfn vc cv cC wcel cC cJ
      clocfin cfv wcel cJ ctop wcel cJ ccl cfv cJ cuni cpw wfn cC cJ locfintop
      cJ clsfn syl adantr cC cJ clocfin cfv wcel cC cJ cuni cpw wss vc cv cC
      wcel cC cJ locfinsspw adantr cC cJ clocfin cfv wcel vc cv cC wcel simpr
      cJ cuni cpw cC cJ ccl cfv vc cv fnfvima syl3anc vc cv cJ ccl cfv cfv cJ
      ccl cfv cC cima elssuni syl sstrd ex $.
  $}

  ${
    $d c n s x C $.  $d c n s x J $.
    $( The union of the closure image of a locally finite collection equals
       the base set.  (Contributed by Claude, 6-Feb-2026.) $)
    lfimclsuni $p |- ( C e. ( LocFin ` J ) ->
      U. J = U. ( ( cls ` J ) " C ) ) $=
      cC cJ clocfin cfv wcel cJ cuni cJ ccl cfv cC cima cuni cC cJ clocfin cfv
      wcel cJ cuni cC cuni cJ ccl cfv cC cima cuni cC cJ cJ cuni cC cuni cJ cJ
      cJ eqid unieqi cC cC cC eqid unieqi locfinbas cC cJ clocfin cfv wcel vs
      cv cJ ccl cfv cC cima cuni wss vs cC wral cC cuni cJ ccl cfv cC cima cuni
      wss cC cJ clocfin cfv wcel vs cv cJ ccl cfv cC cima cuni wss vs cC cC cJ
      vs lfimclsuniss ralrimiv vs cC cJ ccl cfv cC cima cuni unissb sylibr
      eqsstrd cC cJ clocfin cfv wcel cJ ccl cfv cC cima cJ cuni cpw wss cJ ccl
      cfv cC cima cuni cJ cuni wss cC cJ clocfin cfv wcel cJ ccl cfv cC cima cJ
      ccld cfv cJ cuni cpw cC cJ clocfin cfv wcel cJ cuni cpw cJ ccld cfv cJ
      ccl cfv wf cJ ccl cfv cC cima cJ ccld cfv wss cC cJ clocfin cfv wcel cJ
      ctop wcel cJ cuni cpw cJ ccld cfv cJ ccl cfv wf cC cJ locfintop cJ cJ
      cuni cJ cJ cJ eqid unieqi clsf syl cJ cuni cpw cJ ccld cfv cJ ccl cfv cC
      fimass syl cJ ccld cfv cJ cuni cpw wss cC cJ clocfin cfv wcel cJ cJ cuni
      cJ cJ cJ eqid unieqi cldss2 a1i sstrd cJ ccl cfv cC cima cJ cuni sspwuni
      sylib eqssd $.

    ${
      $d c s C $.  $d c s J $.  $d c s N $.
      $( If ` C ` is locally finite and ` N e. J ` , then finiteness of the
         subcollection of ` C ` intersecting ` N ` implies finiteness of
         the closure image subcollection intersecting ` N ` .
         (Contributed by Claude, 6-Feb-2026.) $)
      lfimclslflem3 $p |- ( ( C e. ( LocFin ` J ) /\ N e. J ) ->
        ( { c e. C | ( c i^i N ) =/= (/) } e. Fin ->
          { s e. ( ( cls ` J ) " C ) | ( s i^i N ) =/= (/) } e. Fin ) ) $=
        cC cJ clocfin cfv wcel cN cJ wcel vc cv cN cin c0 wne vc cC crab cfn
        wcel vs cv cN cin c0 wne vs cJ ccl cfv cC cima crab cfn wcel cC cJ cN
        vs vc lfimclslflem2 3expia $.
    $}

    $( The closure image of a locally finite collection satisfies the
       local finiteness condition: each point has a neighborhood that
       intersects only finitely many elements of the image.
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslf $p |- ( C e. ( LocFin ` J ) -> A. x e. U. J
      E. n e. J ( x e. n /\
        { s e. ( ( cls ` J ) " C ) | ( s i^i n ) =/= (/) } e. Fin ) ) $=
      cC cJ clocfin cfv wcel vx vn wel vs cv vn cv cin c0 wne vs cJ ccl cfv cC
      cima crab cfn wcel wa vn cJ wrex vx cJ cuni cC cJ clocfin cfv wcel vx cv
      cJ cuni wcel wa vx vn wel vc cv vn cv cin c0 wne vc cC crab cfn wcel wa
      vn cJ wrex vx vn wel vs cv vn cv cin c0 wne vs cJ ccl cfv cC cima crab
      cfn wcel wa vn cJ wrex cC vx cv vn cJ cJ cuni vc cJ cuni eqid locfinnei
      cC cJ clocfin cfv wcel vx cv cJ cuni wcel wa vx vn wel vc cv vn cv cin
      c0 wne vc cC crab cfn wcel wa vx vn wel vs cv vn cv cin c0 wne vs cJ ccl
      cfv cC cima crab cfn wcel wa vn cJ cC cJ clocfin cfv wcel vx cv cJ cuni
      wcel wa vn cv cJ wcel wa vc cv vn cv cin c0 wne vc cC crab cfn wcel vs
      cv vn cv cin c0 wne vs cJ ccl cfv cC cima crab cfn wcel vx vn wel cC cJ
      clocfin cfv wcel vx cv cJ cuni wcel wa vn cv cJ wcel wa cC cJ clocfin
      cfv wcel vn cv cJ wcel vc cv vn cv cin c0 wne vc cC crab cfn wcel vs cv
      vn cv cin c0 wne vs cJ ccl cfv cC cima crab cfn wcel wi cC cJ clocfin
      cfv wcel vx cv cJ cuni wcel wa cC cJ clocfin cfv wcel vn cv cJ wcel cC
      cJ clocfin cfv wcel vx cv cJ cuni wcel simpl adantr cC cJ clocfin cfv
      wcel vx cv cJ cuni wcel wa vn cv cJ wcel simpr cC cJ vn cv vs vc
      lfimclslflem3 syl2anc anim2d reximdva mpd ralrimiva $.

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
    $d p t $.  $d s t N $.  $d s t S $.
    $( A point in ` ( N \ U. { s e. S | ( s i^i N ) =/= (/) } ) ` is not
       an element of ` U. S ` .  If ` p ` were in ` U. S ` then ` p ` would
       be in some ` c e. S ` , and since ` p e. N ` this ` c ` would satisfy
       ` ( c i^i N ) =/= (/) ` , putting ` p ` into the subtracted set.
       (Contributed by Claude, 10-Feb-2026.) $)
    lfcldunicldlem $p |- ( p e. ( N \ U. { s e. S |
        ( s i^i N ) =/= (/) } ) -> -. p e. U. S ) $=
      ( vt cv cin c0 wne crab cuni cdif wcel eldifn wi eldifi wel wrex syl2anc
      wa eluni2 biimpi simplr simpll simpr inelcm weq ineq1 neeq1d elrab elunii
      sylanbrc exp31 rexlimiv com12 syl5 syl mtod ) DFZBCFZBGZHIZCAJZKZLMZUSAKM
      ZUSVDMZUSBVDNVEUSBMZVFVGOUSBVDPVFDEQZEARZVHVGVFVJEUSAUAUBVJVHVGVIVHVGOEAE
      FZAMZVIVHVGVLVITZVHTZVIVKVCMZVGVLVIVHUCZVNVLVKBGZHIZVOVLVIVHUDVNVIVHVRVPV
      MVHUEUSVKBUFSVBVRCVKACEUGVAVQHUTVKBUHUIUJULUSVKVCUKSUMUNUOUPUQUR $.
  $}

  ${
    $d p s n S $.
    $( The set ` U. S ` is disjoint from
       ` ( n \ U. { s e. S | ( s i^i n ) =/= (/) } ) ` .  Follows from
       ~ lfcldunicldlem by contraposition and generalization.
       (Contributed by Claude, 10-Feb-2026.) $)
    lfcldunicldlem3 $p |- ( U. S i^i ( n \ U. { s e. S |
        ( s i^i n ) =/= (/) } ) ) = (/) $=
      ( vp cuni cv cin c0 crab cdif wceq wcel wn wi lfcldunicldlem con2i ax-gen
      wne wal disj1 mpbir ) AEZBFZCFUCGHRCAIEJZGHKDFZUBLZUEUDLZMNZDSUHDUGUFAUCC
      DOPQDUBUDTUA $.
  $}

  ${
    $d n p s C $.  $d n p s J $.  $d n p s S $.  $d n p s X $.
    lfcldunicldlem2.1 $e |- X = U. J $.
    $( Helper for ~ lfcldunicld .  Given a neighborhood ` n ` of ` p ` meeting
       only finitely many members of ` C ` , if ` p ` is in the closure of
       ` U. S ` then ` p e. U. S ` .  We form the finite subcollection
       ` { s e. S | ( s i^i n ) =/= (/) } ` , show its union is closed via
       ~ unicld , form the open set ` ( n \ U. { ... } ) ` , use
       ~ lfcldunicldlem to show it is disjoint from ` U. S ` , then
       ~ lfimclslem to show it is disjoint from ` ( ( cls `` J ) `` U. S ) ` .
       Since ` p e. n ` , it must lie in the finite union, which is contained
       in ` U. S ` .  (Contributed by Claude, 10-Feb-2026.) $)
    lfcldunicldlem2 $p |- ( ( ( J e. Top /\ C C_ ( Clsd ` J ) /\ S C_ C )
        /\ ( n e. J /\ p e. n
          /\ { s e. C | ( s i^i n ) =/= (/) } e. Fin )
        /\ p e. ( ( cls ` J ) ` U. S ) ) -> p e. U. S ) $=
      ( wcel cfv wss w3a cv cin c0 crab cfn a1i sstrd syl2anc ctop ccld wel wne
      cuni ccl ssrab2 unissi cdif wn simp22 simp11 simp13 simp12 cldss2 sspwuni
      cpw biimpi syl simp21 simp23 rabss2 unicld syl3anc difopn lfcldunicldlem3
      wceq ssfi lfimclslem syl22anc simp3 disjel neldif sselid ) DUAIZADUBJZKZB
      AKZLZCMZDIZGCUCZFMVTNOUDZFAPZQIZLZGMZBUEZDUFJJZIZLZWCFBPZUEZWHWGWLBWCFBUG
      ZUHWKWBWGVTWMUIZIUJZWGWMIVSWAWBWEWJUKWKWIWONOVGZWJWPWKVOWHEKZWODIZWHWONOV
      GZWQVOVQVRWFWJULZWKBEUQZKZWRWKBAXBVOVQVRWFWJUMZWKAVPXBVOVQVRWFWJUNZVPXBKW
      KDEHUORSSXCWRBEUPURUSWKWAWMVPIZWSVSWAWBWEWJUTWKVOWLQIZWLVPKXFXAWKWEWLWDKZ
      XGVSWAWBWEWJVAWKVRXHXDWCFBAVBUSWDWLVHTWKWLAVPWKWLBAWLBKWKWNRXDSXESWLDEHVC
      VDVTWMDEHVETWTWKBCFVFRWHDWOEHVIVJVSWFWJVKWIWOWGVLTWGVTWMVMTVN $.
  $}

  ${
    $d n p s C $.  $d n p s J $.  $d n p s S $.  $d n p s X $.
    lfcldunicldlem4.1 $e |- X = U. J $.
    $( Helper for ~ lfcldunicld .  Reduce the closure-subset step to pointwise
       membership via ~ ssrdv , existential elimination via ~ rexlimdva on
       ~ locfinnei , and the core argument ~ lfcldunicldlem2 .
       (Contributed by Claude, 10-Feb-2026.) $)
    lfcldunicldlem4 $p |- ( ( C e. ( LocFin ` J ) /\ C C_ ( Clsd ` J )
        /\ S C_ C ) -> ( ( cls ` J ) ` U. S ) C_ U. S ) $=
      ( vp vn vs clocfin cfv wcel ccld wss w3a cuni cv wa syl sstrd syl2anc ccl
      wel cin wne crab cfn wrex simpl1 ctop locfintop cpw simpl3 simpl2 sspwuni
      cldss2 a1i biimpi clsss3 simpr sseldd locfinnei simpll simp1 simp2 simprl
      c0 simp3 simprrl simprrr simplr lfcldunicldlem2 syl331anc rexlimddv ssrdv
      ex ) ACIJKZACLJZMZBAMZNZFBOZCUAJJZWAVTFPZWBKZWCWAKZVTWDQZFGUBZHPGPZUCVFUD
      HAUEUFKZQZWEGCWFVPWCDKWJGCUGVPVRVSWDUHZWFWBDWCWFCUIKZWADMZWBDMWFVPWLWKACU
      JZRWFBDUKZMZWMWFBVQWOWFBAVQVPVRVSWDULVPVRVSWDUMSVQWOMWFCDEUOUPSWPWMBDUNUQ
      RWACDEURTVTWDUSUTAWCGCDHEVATWFWHCKZWJQZQZWLVRVSWQWGWIWDWEWSVTWLVTWDWRVBZV
      TVPWLVPVRVSVCWNRRWSVTVRWTVPVRVSVDRWSVTVSWTVPVRVSVGRWFWQWJVEWFWQWGWIVHWFWQ
      WGWIVIVTWDWRVJABGCDHFEVKVLVMVOVN $.
  $}

  ${
    $d n p s C $.  $d n p s J $.  $d n p s S $.  $d n p s X $.
    lfcldunicld.1 $e |- X = U. J $.
    $( The union of a subcollection of a locally finite collection of closed
       sets is closed.  If ` P ` is in the closure of ` U. S ` , then by
       ~ locfinnei there is a neighborhood ` N ` of ` P ` meeting only
       finitely many elements of ` C ` .  The finite subcollection
       ` { s e. S | ( s i^i N ) =/= (/) } ` is closed, so its union is
       closed by ~ unicld .  The open set ` ( N \ U. { ... } ) ` is
       disjoint from ` U. S ` , so by ~ lfimclslem , ` P ` must already
       lie in ` U. S ` .  Consequence of Lemma 39.1 of Munkres p. 245.
       (Contributed by Claude, 10-Feb-2026.) $)
    lfcldunicld $p |- ( ( C e. ( LocFin ` J ) /\ C C_ ( Clsd ` J )
        /\ S C_ C ) -> U. S e. ( Clsd ` J ) ) $=
      ( clocfin cfv wcel ccld wss w3a cuni lfcldunicldlem4 ctop simp1 locfintop
      ccl wb syl sstrd cpw simp3 simp2 cldss2 a1i sspwuni biimpi iscld4 syl2anc
      mpbird ) ACFGHZACIGZJZBAJZKZBLZULHZUPCQGGUPJZABCDEMUOCNHZUPDJZUQURRUOUKUS
      UKUMUNOACPSUOBDUAZJZUTUOBAVAUKUMUNUBUOAULVAUKUMUNUCULVAJUOCDEUDUETTVBUTBD
      UFUGSUPCDEUHUIUJ $.
  $}

  ${
    $d a w y z J $.
    $( Helper for ~ regsepcover : apply regularity separation to get
       an open set whose closure is contained in a covering element.
       (Contributed by Claude, 6-Feb-2026.) $)
    regsepcover2a $p |- ( ( ( J e. Reg /\ y C_ J ) /\ ( w e. y /\ z e. w ) )
      -> E. a e. J ( z e. a /\ ( ( cls ` J ) ` a ) C_ w ) ) $=
      cJ creg wcel vy cv cJ wss wa vw vy wel vz vw wel wa wa cJ creg wcel vw cv
      cJ wcel vz vw wel vz va wel va cv cJ ccl cfv cfv vw cv wss wa va cJ wrex
      cJ creg wcel vy cv cJ wss vw vy wel vz vw wel wa simpll cJ creg wcel vy
      cv cJ wss wa vw vy wel vz vw wel wa wa vy cv cJ vw cv cJ creg wcel vy cv
      cJ wss wa vw vy wel vz vw wel wa wa vy cv cJ wss wi wtru cJ creg wcel vy
      cv cJ wss wa vw vy wel vz vw wel wa vy cv cJ wss wtru cJ creg wcel vy cv
      cJ wss vw vy wel vz vw wel wa simp2r 3expib mptru cJ creg wcel vy cv cJ
      wss wa vw vy wel vz vw wel wa wa vw vy wel wi wtru cJ creg wcel vy cv cJ
      wss wa vw vy wel vz vw wel wa vw vy wel wtru cJ creg wcel vy cv cJ wss wa
      vw vy wel vz vw wel simp3l 3expib mptru sseldd cJ creg wcel vy cv cJ wss
      wa vw vy wel vz vw wel simprr va vz cv vw cv cJ regsep syl3anc $.
  $}

  ${
    $d a u v w y z J $.
    $( Helper for ~ regsepcover : given ` w e. y ` , ` a e. J ` ,
       ` z e. a ` , and ` ( ( cls `` J ) `` a ) C_ w ` , conclude
       ` z e. U. { v e. J | E. u e. y ( ( cls `` J ) `` v ) C_ u } ` .
       (Contributed by Claude, 6-Feb-2026.) $)
    regsepcover2b $p |- ( ( ( w e. y /\ a e. J ) /\
      ( z e. a /\ ( ( cls ` J ) ` a ) C_ w ) ) ->
      z e. U. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } ) $=
      vw vy wel va cv cJ wcel wa vz va wel va cv cJ ccl cfv cfv vw cv wss wa wa
      vz va wel va cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab
      wcel vz cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cuni
      wcel vw vy wel va cv cJ wcel wa vz va wel va cv cJ ccl cfv cfv vw cv wss
      simprl vw vy wel va cv cJ wcel wa vz va wel va cv cJ ccl cfv cfv vw cv
      wss wa wa va cv cJ wcel va cv cJ ccl cfv cfv vu cv wss vu vy cv wrex va
      cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab wcel vw vy wel
      va cv cJ wcel vz va wel va cv cJ ccl cfv cfv vw cv wss wa simplr vw vy
      wel va cv cJ wcel wa vz va wel va cv cJ ccl cfv cfv vw cv wss wa wa vw vy
      wel va cv cJ ccl cfv cfv vw cv wss va cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vw vy wel va cv cJ wcel vz va wel va cv cJ ccl cfv cfv vw cv wss
      wa simpll vw vy wel va cv cJ wcel wa vz va wel va cv cJ ccl cfv cfv vw cv
      wss wa wa va cv cJ ccl cfv cfv vw cv vw vy wel va cv cJ ccl cfv cfv vw cv
      wss va cv cJ ccl cfv cfv vw cv cpw wcel va cv cJ wcel vz va wel vw vy wel
      va cv cJ ccl cfv cfv vw cv cpw wcel va cv cJ ccl cfv cfv vw cv wss va cv
      cJ ccl cfv cfv vw cv vy cv elpw2g biimpar ad2ant2rl elpwid va cv cJ ccl
      cfv cfv vu cv wss va cv cJ ccl cfv cfv vw cv wss vu vw cv vy cv vu vw weq
      va cv cJ ccl cfv cfv va cv cJ ccl cfv cfv vu cv vw cv vu vw weq va cv va
      cv cJ ccl cfv cJ ccl cfv vu vw weq cJ cJ ccl ccl vu vw weq ccl eqidd vu
      vw weq cJ eqidd fveq12d vu vw weq va cv va cv vu vw weq va cv ssidd vu vw
      weq va cv ssidd eqssd fveq12d vu vw weq vu cv vw cv vu cv vw cv csn wcel
      vu vw weq vu vw cv velsn biimpri elsnd sseq12d rspcev syl2anc vv cv cJ
      ccl cfv cfv vu cv wss vu vy cv wrex va cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vv va cv cJ vv va weq vv cv cJ ccl cfv cfv vu cv wss va cv cJ ccl
      cfv cfv vu cv wss vu vy cv vv va weq vv cv cJ ccl cfv cfv va cv cJ ccl
      cfv cfv vu cv vu cv vv va weq vv cv va cv cJ ccl cfv cJ ccl cfv vv va weq
      cJ cJ ccl ccl vv va weq ccl eqidd vv va weq cJ eqidd fveq12d vv va weq vv
      cv va cv vv cv va cv eqimss va cv vv cv eqimss2 eqssd fveq12d vv va weq
      vu cv vu cv vu cv vu cv csn wcel vv va weq vu vsnid a1i elsnd sseq12d
      rexbidv elrab sylanbrc vz cv va cv vv cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vv cJ crab elunii syl2anc $.
  $}

  ${
    $d a u v w y z J $.
    $( Helper for ~ regsepcover : in a regular space, if ` w ` is in an open
       covering ` y ` (which is a subset of ` J ` ) and ` z e. w ` , then
       ` z ` is in the union of the regularity-refined covering.
       (Contributed by Claude, 6-Feb-2026.) $)
    regsepcover2 $p |- ( ( ( J e. Reg /\ y C_ J ) /\ ( w e. y /\ z e. w ) )
      -> z e. U. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } ) $=
      cJ creg wcel vy cv cJ wss wa vw vy wel vz vw wel wa wa vz va wel va cv cJ
      ccl cfv cfv vw cv wss wa vz cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vv cJ crab cuni wcel va cJ vy vz vw cJ va regsepcover2a cJ creg wcel
      vy cv cJ wss wa vw vy wel vz vw wel wa wa va cv cJ wcel vz va wel va cv
      cJ ccl cfv cfv vw cv wss wa wa wa vw vy wel va cv cJ wcel wa vz va wel va
      cv cJ ccl cfv cfv vw cv wss wa vz cv vv cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vv cJ crab cuni wcel cJ creg wcel vy cv cJ wss wa vw vy wel vz vw
      wel wa wa va cv cJ wcel vz va wel va cv cJ ccl cfv cfv vw cv wss wa wa wa
      vw vy wel va cv cJ wcel cJ creg wcel vy cv cJ wss wa vw vy wel vz vw wel
      wa wa vw vy wel va cv cJ wcel vz va wel va cv cJ ccl cfv cfv vw cv wss wa
      wa cJ creg wcel vy cv cJ wss wa vw vy wel vz vw wel simprl adantr cJ creg
      wcel vy cv cJ wss wa vw vy wel vz vw wel wa wa va cv cJ wcel vz va wel va
      cv cJ ccl cfv cfv vw cv wss wa simprl jca cJ creg wcel vy cv cJ wss wa vw
      vy wel vz vw wel wa wa va cv cJ wcel vz va wel va cv cJ ccl cfv cfv vw cv
      wss wa simprr vy vz vw vv vu cJ va regsepcover2b syl2anc rexlimddv $.
  $}

  ${
    $d u v w y z J $.
    $( In a regular space, if ` w ` is in the open covering ` y ` (a subset
       of ` J ` ), then ` w ` is a subset of the union of the
       regularity-refined covering.  Helper for ~ regsepcover1 .
       (Contributed by Claude, 6-Feb-2026.) $)
    regsepcover1a $p |- ( ( ( J e. Reg /\ y C_ J ) /\ w e. y ) ->
      w C_ U. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } ) $=
      cJ creg wcel vy cv cJ wss wa vw vy wel wa vz vw cv vv cv cJ ccl cfv cfv
      vu cv wss vu vy cv wrex vv cJ crab cuni cJ creg wcel vy cv cJ wss wa vw
      vy wel wa vz vw wel vz cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv
      cJ crab cuni wcel cJ creg wcel vy cv cJ wss wa vw vy wel vz vw wel vz cv
      vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cuni wcel vy vz
      vw vv vu cJ regsepcover2 anassrs ex ssrdv $.
  $}

  ${
    $d u v w y z J $.
    $( In a regular space, every element of the union of an open covering
       ` y ` is in the union of the regularity-refined covering.  Helper for
       ~ regsepcover .  (Contributed by Claude, 6-Feb-2026.) $)
    regsepcover1 $p |- ( ( J e. Reg /\ y C_ J ) ->
      U. y C_ U. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } ) $=
      cJ creg wcel vy cv cJ wss wa vw cv vv cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vv cJ crab cuni wss vw vy cv wral vy cv cuni vv cv cJ ccl cfv cfv
      vu cv wss vu vy cv wrex vv cJ crab cuni wss cJ creg wcel vy cv cJ wss wa
      vw cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cuni wss vw
      vy cv vy vw vv vu cJ regsepcover1a ralrimiva vw vy cv vv cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vv cJ crab cuni unissb sylibr $.
  $}

  ${
    $d u v w y z J $.
    $( Regularity covering: in a regular space, if ` y ` is an open covering
       of ` J ` , then the collection of open sets whose closure is in some
       element of ` y ` also covers ` J ` .
       (Contributed by Claude, 6-Feb-2026.) $)
    regsepcover $p |- ( ( J e. Reg /\ y C_ J /\ U. J = U. y ) ->
      U. J = U. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } ) $=
      cJ creg wcel vy cv cJ wss cJ cuni vy cv cuni wceq w3a cJ cuni vv cv cJ
      ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cuni cJ creg wcel vy cv cJ
      wss cJ cuni vy cv cuni wceq w3a cJ cuni vy cv cuni vv cv cJ ccl cfv cfv
      vu cv wss vu vy cv wrex vv cJ crab cuni cJ creg wcel vy cv cJ wss cJ cuni
      vy cv cuni wceq simp3 cJ creg wcel vy cv cJ wss vy cv cuni vv cv cJ ccl
      cfv cfv vu cv wss vu vy cv wrex vv cJ crab cuni wss cJ cuni vy cv cuni
      wceq vy vv vu cJ regsepcover1 3adant3 eqsstrd vv cv cJ ccl cfv cfv vu cv
      wss vu vy cv wrex vv cJ crab cuni cJ cuni wss cJ creg wcel vy cv cJ wss
      cJ cuni vy cv cuni wceq w3a vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex
      vv cJ crab cJ vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ ssrab2
      unissi a1i eqssd $.
  $}

  ${
    $d u w y z J $.
    $( In a topology, if ` w ` is an open set and ` z C_ w ` , then
       the existential condition on the closure of ` w ` transfers to
       the closure of ` z ` .  Helper for ~ clsreflem .
       (Contributed by Claude, 6-Feb-2026.) $)
    clsreflema $p |- ( ( J e. Top /\ w e. J /\ z C_ w ) ->
      ( E. u e. y ( ( cls ` J ) ` w ) C_ u ->
        E. u e. y ( ( cls ` J ) ` z ) C_ u ) ) $=
      cJ ctop wcel vw cv cJ wcel vz cv vw cv wss w3a vw cv cJ ccl cfv cfv vu cv
      wss vz cv cJ ccl cfv cfv vu cv wss vu vy cv cJ ctop wcel vw cv cJ wcel vz
      cv vw cv wss w3a vz cv cJ ccl cfv cfv vw cv cJ ccl cfv cfv wss vw cv cJ
      ccl cfv cfv vu cv wss vz cv cJ ccl cfv cfv vu cv wss wi vw cv cJ wcel cJ
      ctop wcel vw cv cJ cuni wss vz cv vw cv wss vz cv cJ ccl cfv cfv vw cv cJ
      ccl cfv cfv wss vw cv cJ elssuni vw cv vz cv cJ cJ cuni cJ cuni eqid
      clsss syl3an2 vz cv cJ ccl cfv cfv vw cv cJ ccl cfv cfv vu cv sstr2 syl
      reximdv $.
  $}

  ${
    $d u v w y J $.
    $( Extract the existential condition from membership in the
       regularity-refined covering.  If ` w ` is in
       ` { v e. J | E. u e. y ( ( cls `` J ) `` v ) C_ u } ` , then
       the closure of ` w ` is contained in some element of ` y ` .
       Helper for ~ clsreflemb .
       (Contributed by Claude, 6-Feb-2026.) $)
    clsreflemc $p |- (
      w e. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } ->
      E. u e. y ( ( cls ` J ) ` w ) C_ u ) $=
      vw cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab wcel vw cv
      cJ wcel vw cv cJ ccl cfv cfv vu cv wss vu vy cv wrex wa vw cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vw cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vv cJ crab wcel vw cv cJ wcel vw cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex wa vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vw cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vv vw cv cJ vv cv cJ ccl cfv cfv vu cv wss vu
      vy cv wrex vw cv cJ ccl cfv cfv vu cv wss vu vy cv wrex wb vv vw vv cv cJ
      ccl cfv cfv vu cv wss vu vy cv wrex vw cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex wb vv vw vv vw weq vv cv cJ ccl cfv cfv vu cv wss vw cv cJ ccl
      cfv cfv vu cv wss vu vy cv vy cv vu vv cv vw cv vu vw cv nfcv nfeq2 vu vy
      cv nfcv vu vy cv nfcv vv vw weq vy cv vy cv vy cv vy cv csn wcel vv vw
      weq vy vsnid a1i elsnd vv vw weq vv cv cJ ccl cfv cfv vw cv cJ ccl cfv
      cfv vu cv vu cv vv vw weq vv cv vw cv cJ ccl cfv cJ ccl cfv vv vw weq cJ
      ccl cfv eqidd vv vw weq id fveq12d vv vw weq vu cv vu cv vv vw weq vu cv
      ssidd vv vw weq vu cv ssidd eqssd sseq12d rexeqbid cdeqi cdeqri elrab
      biimpi vw cv cJ wcel vw cv cJ ccl cfv cfv vu cv wss vu vy cv wrex simpr
      syl $.
  $}

  ${
    $d u v w y z J $.
    $( If ` w ` is in the regularity-refined covering
       ` { v e. J | E. u e. y ( ( cls `` J ) `` v ) C_ u } ` and
       ` z C_ w ` , then the closure of ` z ` is contained in some element
       of ` y ` .  Helper for ~ clsreflem .
       (Contributed by Claude, 6-Feb-2026.) $)
    clsreflemb $p |- ( ( J e. Top /\
      w e. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } /\
      z C_ w ) ->
      E. u e. y ( ( cls ` J ) ` z ) C_ u ) $=
      cJ ctop wcel vw cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ
      crab wcel vz cv vw cv wss w3a vw cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vz cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vw cv vv cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vv cJ crab wcel cJ ctop wcel vw cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vz cv vw cv wss vy vw vv vu cJ clsreflemc
      3ad2ant2 vw cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab
      wcel cJ ctop wcel vw cv cJ wcel vz cv vw cv wss vw cv cJ ccl cfv cfv vu
      cv wss vu vy cv wrex vz cv cJ ccl cfv cfv vu cv wss vu vy cv wrex wi vv
      cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv vw cv cJ elrabi vy vz vw vu
      cJ clsreflema syl3an2 mpd $.
  $}

  ${
    $d t u v w y z J $.
    $( If ` t ` refines the regularity-refined covering
       ` { v e. J | E. u e. y ( ( cls `` J ) `` v ) C_ u } ` and
       ` z e. t ` , then the closure of ` z ` is contained in some element
       of ` y ` .  Helper for ~ reglfpcmplem1 .
       (Contributed by Claude, 6-Feb-2026.) $)
    clsreflem $p |- ( ( J e. Top /\
      t Ref { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } /\
      z e. t ) ->
      E. u e. y ( ( cls ` J ) ` z ) C_ u ) $=
      cJ ctop wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ
      crab cref wbr vz vt wel w3a vz cv vw cv wss vw vv cv cJ ccl cfv cfv vu cv
      wss vu vy cv wrex vv cJ crab wrex vz cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref
      wbr vz vt wel vz cv vw cv wss vw vv cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vv cJ crab wrex cJ ctop wcel vw vt cv vv cv cJ ccl cfv cfv vu cv wss
      vu vy cv wrex vv cJ crab vz cv refssex 3adant1 cJ ctop wcel vt cv vv cv
      cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref wbr vz cv vw cv
      wss vw vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab wrex vz cv
      cJ ccl cfv cfv vu cv wss vu vy cv wrex wi vz vt wel cJ ctop wcel vz cv vw
      cv wss vz cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vw vv cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vv cJ crab vy vz vw vv vu cJ clsreflemb
      rexlimdv3a 3ad2ant1 mpd $.
  $}

  ${
    $d C J $.
    $( The closure-image of any collection is contained in the closed sets.
       (Contributed by Claude, 6-Feb-2026.) $)
    clsimcld $p |- ( J e. Top ->
      ( ( cls ` J ) " C ) C_ ( Clsd ` J ) ) $=
      cJ ctop wcel cJ cuni cpw cJ ccld cfv cJ ccl cfv wf cJ ccl cfv cC cima cJ
      ccld cfv wss cJ cJ cuni cJ cuni eqid clsf cJ cuni cpw cJ ccld cfv cJ ccl
      cfv cC fimass syl $.
  $}

  ${
    $d t J $.
    $( The closure image of a locally finite collection is locally finite and
       consists of closed sets.
       (Contributed by Claude, 6-Feb-2026.) $)
    clslfc $p |- ( t e. ( LocFin ` J ) ->
      ( ( cls ` J ) " t ) e.
        ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) ) $=
      vt cv cJ clocfin cfv wcel cJ clocfin cfv cJ ccld cfv cpw cJ ccl cfv vt cv
      cima vt cv cJ lfimcls vt cv cJ clocfin cfv wcel cJ ccl cfv vt cv cima cJ
      ccld cfv cvv cJ ccld cfv cvv wcel vt cv cJ clocfin cfv wcel cJ ccld fvex
      a1i vt cv cJ clocfin cfv wcel cJ ctop wcel cJ ccl cfv vt cv cima cJ ccld
      cfv wss vt cv cJ locfintop vt cv cJ clsimcld syl sselpwd elind $.
  $}

  ${
    $d t u v w y z J $.
    $( If ` t ` refines the regularity-refined covering of ` y ` in ` J ` and
       ` z ` is an element of the closure image of ` t ` , then ` z ` is
       contained in some element of ` y ` .  Helper for ~ clsrefimg .
       (Contributed by Claude, 6-Feb-2026.) $)
    clsrefimg1 $p |- ( ( J e. Top /\
      t Ref { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } /\
      z e. ( ( cls ` J ) " t ) ) ->
      E. u e. y z C_ u ) $=
      cJ ctop wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ
      crab cref wbr vz cv cJ ccl cfv vt cv cima wcel w3a vw cv cJ ccl cfv cfv
      vz cv wceq vw vt cv wrex vz cv vu cv wss vu vy cv wrex cJ ctop wcel vz cv
      cJ ccl cfv vt cv cima wcel vw cv cJ ccl cfv cfv vz cv wceq vw vt cv wrex
      vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref wbr cJ
      ctop wcel cJ ccl cfv wfun vz cv cJ ccl cfv vt cv cima wcel vw cv cJ ccl
      cfv cfv vz cv wceq vw vt cv wrex cJ ctop wcel cJ ccl cfv cJ cuni cpw wfn
      cJ ccl cfv wfun cJ clsfn cJ cuni cpw cJ ccl cfv fnfun syl vw vz cv vt cv
      cJ ccl cfv fvelima sylan 3adant2 cJ ctop wcel vt cv vv cv cJ ccl cfv cfv
      vu cv wss vu vy cv wrex vv cJ crab cref wbr vw cv cJ ccl cfv cfv vz cv
      wceq vw vt cv wrex vz cv vu cv wss vu vy cv wrex wi vz cv cJ ccl cfv vt
      cv cima wcel cJ ctop wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vv cJ crab cref wbr wa vw cv cJ ccl cfv cfv vz cv wceq vz cv vu cv
      wss vu vy cv wrex vw vt cv cJ ctop wcel vt cv vv cv cJ ccl cfv cfv vu cv
      wss vu vy cv wrex vv cJ crab cref wbr vw vt wel vw cv cJ ccl cfv cfv vz
      cv wceq vz cv vu cv wss vu vy cv wrex wi cJ ctop wcel vt cv vv cv cJ ccl
      cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref wbr vw vt wel w3a vw cv
      cJ ccl cfv cfv vu cv wss vu vy cv wrex vw cv cJ ccl cfv cfv vz cv wceq vz
      cv vu cv wss vu vy cv wrex vy vw vv vu vt cJ clsreflem vw cv cJ ccl cfv
      cfv vz cv wceq vw cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vz cv vu cv
      wss vu vy cv wrex vw cv cJ ccl cfv cfv vz cv wceq vw cv cJ ccl cfv cfv vu
      cv wss vz cv vu cv wss vu vy cv vw cv cJ ccl cfv cfv vz cv vu cv sseq1
      rexbidv biimpd syl5com 3expia rexlimdv 3adant3 mpd $.
  $}

  ${
    $d t u v w y z J $.
    $( If ` t ` is a locally finite refinement of the regularity-refined
       covering and ` U. J = U. y ` , then the closure image of ` t `
       refines ` y ` .  Helper for ~ reglfpcmplem1 .
       (Contributed by Claude, 6-Feb-2026.) $)
    clsrefimg $p |- ( ( t e. ( LocFin ` J ) /\
      t Ref { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } /\
      U. J = U. y ) ->
      ( ( cls ` J ) " t ) Ref y ) $=
      vt cv cJ clocfin cfv wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vv cJ crab cref wbr cJ cuni vy cv cuni wceq w3a cJ ccl cfv vt cv
      cima vy cv cref wbr vy cv cuni cJ ccl cfv vt cv cima cuni wceq vz cv vu
      cv wss vu vy cv wrex vz cJ ccl cfv vt cv cima wral vt cv cJ clocfin cfv
      wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref
      wbr cJ cuni vy cv cuni wceq w3a vy cv cuni cJ cuni cJ ccl cfv vt cv cima
      cuni vt cv cJ clocfin cfv wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vv cJ crab cref wbr cJ cuni vy cv cuni wceq w3a cJ cuni vy cv
      cuni vt cv cJ clocfin cfv wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vv cJ crab cref wbr cJ cuni vy cv cuni wceq simp3 eqcomd vt cv cJ
      clocfin cfv wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ
      crab cref wbr cJ cuni vy cv cuni wceq w3a vt cv cJ clocfin cfv wcel cJ
      cuni cJ ccl cfv vt cv cima cuni wceq vt cv cJ clocfin cfv wcel vt cv vv
      cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref wbr cJ cuni vy
      cv cuni wceq simp1 vt cv cJ lfimclsuni syl eqtrd vt cv cJ clocfin cfv
      wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref
      wbr cJ cuni vy cv cuni wceq w3a vz cv vu cv wss vu vy cv wrex vz cJ ccl
      cfv vt cv cima vt cv cJ clocfin cfv wcel vt cv vv cv cJ ccl cfv cfv vu cv
      wss vu vy cv wrex vv cJ crab cref wbr cJ cuni vy cv cuni wceq w3a vz cv
      cJ ccl cfv vt cv cima wcel wa cJ ctop wcel vt cv vv cv cJ ccl cfv cfv vu
      cv wss vu vy cv wrex vv cJ crab cref wbr vz cv cJ ccl cfv vt cv cima wcel
      w3a vz cv vu cv wss vu vy cv wrex vt cv cJ clocfin cfv wcel vt cv vv cv
      cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref wbr cJ cuni vy cv
      cuni wceq w3a vz cv cJ ccl cfv vt cv cima wcel wa cJ ctop wcel vt cv vv
      cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref wbr vz cv cJ
      ccl cfv vt cv cima wcel vt cv cJ clocfin cfv wcel vt cv vv cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vv cJ crab cref wbr cJ cuni vy cv cuni wceq
      w3a vz cv cJ ccl cfv vt cv cima wcel wa vt cv cJ clocfin cfv wcel cJ ctop
      wcel vt cv cJ clocfin cfv wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vv cJ crab cref wbr cJ cuni vy cv cuni wceq w3a vt cv cJ clocfin
      cfv wcel vz cv cJ ccl cfv vt cv cima wcel vt cv cJ clocfin cfv wcel vt cv
      vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref wbr cJ cuni
      vy cv cuni wceq simp1 adantr vt cv cJ locfintop syl vt cv cJ clocfin cfv
      wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref
      wbr cJ cuni vy cv cuni wceq w3a vt cv vv cv cJ ccl cfv cfv vu cv wss vu
      vy cv wrex vv cJ crab cref wbr vz cv cJ ccl cfv vt cv cima wcel vt cv cJ
      clocfin cfv wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ
      crab cref wbr cJ cuni vy cv cuni wceq simp2 adantr vt cv cJ clocfin cfv
      wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref
      wbr cJ cuni vy cv cuni wceq w3a vz cv cJ ccl cfv vt cv cima wcel simpr
      3jca vy vz vv vu vt cJ clsrefimg1 syl ralrimiva vt cv cJ clocfin cfv wcel
      vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref wbr cJ
      cuni vy cv cuni wceq w3a cJ ccl cfv vt cv cima cJ clocfin cfv wcel cJ ccl
      cfv vt cv cima vy cv cref wbr vy cv cuni cJ ccl cfv vt cv cima cuni wceq
      vz cv vu cv wss vu vy cv wrex vz cJ ccl cfv vt cv cima wral wa wb vt cv
      cJ clocfin cfv wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv
      cJ crab cref wbr cJ cuni vy cv cuni wceq w3a vt cv cJ clocfin cfv wcel cJ
      ccl cfv vt cv cima cJ clocfin cfv wcel vt cv cJ clocfin cfv wcel vt cv vv
      cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref wbr cJ cuni vy
      cv cuni wceq simp1 vt cv cJ lfimcls syl vz vu cJ ccl cfv vt cv cima vy cv
      cJ clocfin cfv cJ ccl cfv vt cv cima cuni vy cv cuni cJ ccl cfv vt cv
      cima cuni eqid vy cv cuni eqid isref syl mpbir2and $.
  $}

  ${
    $d t u v y z J $.
    $( Witness construction for ~ reglfpcmplem1 : if ` t ` is a locally finite
       refinement of the regularity-refined covering ` B ` , then the closure
       image ` ( ( cls `` J ) " t ) ` is in ` ( LocFin `` J ) i^i ~P ( Clsd
       `` J ) ` and refines ` y ` .  Existentially pack the witness using ` z `
       to avoid variable capture with ` t ` .
       (Contributed by Claude, 6-Feb-2026.) $)
    reglfpcmplem1a $p |- ( ( t e. ( LocFin ` J ) /\
      t Ref { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } /\
      U. J = U. y ) ->
      E. z e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) z Ref y ) $=
      vt cv cJ clocfin cfv wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vv cJ crab cref wbr cJ cuni vy cv cuni wceq w3a cJ ccl cfv vt cv
      cima cJ clocfin cfv cJ ccld cfv cpw cin wcel cJ ccl cfv vt cv cima vy cv
      cref wbr vz cv vy cv cref wbr vz cJ clocfin cfv cJ ccld cfv cpw cin wrex
      vt cv cJ clocfin cfv wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vv cJ crab cref wbr cJ cuni vy cv cuni wceq w3a vt cv cJ clocfin cfv
      wcel cJ ccl cfv vt cv cima cJ clocfin cfv cJ ccld cfv cpw cin wcel vt cv
      cJ clocfin cfv wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv
      cJ crab cref wbr cJ cuni vy cv cuni wceq simp1 vt cJ clslfc syl vy vv vu
      vt cJ clsrefimg vz cv vy cv cref wbr cJ ccl cfv vt cv cima vy cv cref wbr
      vz cJ ccl cfv vt cv cima cJ clocfin cfv cJ ccld cfv cpw cin vz cv cJ ccl
      cfv vt cv cima vy cv cref breq1 rspcev syl2anc $.
  $}

  ${
    $d t u v y z J $.
    $( Per-covering step for ~ reglfpcmplem1 : given ` J ` is regular,
       ` y C_ J ` , ` U. J = U. y ` , and every covering of ` J ` has a
       locally finite refinement (quantified over ` z ` to avoid capture),
       then ` y ` has a locally finite closed covering refinement.
       (Contributed by Claude, 6-Feb-2026.) $)
    reglfpcmplem1b $p |- ( ( ( J e. Reg /\ y C_ J /\ U. J = U. y ) /\
      A. z e. ~P J ( U. J = U. z ->
        E. t e. ( LocFin ` J ) t Ref z ) ) ->
      E. z e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) z Ref y ) $=
      ( vv vu creg wcel cv wss cuni wceq cref wbr cfv wrex wi cpw syl mpd simp3
      w3a clocfin wral wa ccld cin adantr ccl simpl regsepcover simpr cvv simp1
      crab ssrab2 a1i sselpwd unieq eqeq2d breq2 rexbidv imbi12d reglfpcmplem1a
      elex rspcv 3exp rexlimiv ) DGHZAIZDJZDKZVJKLZUBZVLBIZKZLZCIZVOMNZCDUCOZPZ
      QZBDRZUDZUEZVMVOVJMNBVTDUFORUGPZVNVMWDVIVKVMUAUHWEVREIDUIOOFIJFVJPZEDUOZM
      NZCVTPZVMWFQZWEVLWHKZLZWJWEVNWMVNWDUJZAEFDUKSWEWDWMWJQZVNWDULWEWHWCHWDWOQ
      WEWHDUMWEVIDUMHWEVNVIWNVIVKVMUNSDGVESWHDJWEWGEDUPUQURWBWOBWHWCVOWHLZVQWMW
      AWJWPVPWLVLVOWHUSUTWPVSWICVTVOWHVRMVAVBVCVFSTTWIWKCVTVRVTHWIVMWFABEFCDVDV
      GVHST $.
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
      ( vz wcel cuni cv wceq cref wbr cfv wrex wi cpw wa simpl simpr syl adantr
      wral creg clocfin ccld cin weq unieq eqeq2d breq2 rexbidv cbvralvw biimpi
      imbi12d jca wss w3a elpwi 3jca reglfpcmplem1b breq1 cbvrexvw ex ralrimiva
      ) CUAEZCFZAGZFZHZBGZVEIJZBCUBKZLZMZACNZTZOZVCVDDGZFZHZVHVPIJZBVJLZMZDVMTZ
      OZVGVIBVJCUCKNUDZLZMZAVMTVOVCWBVCVNPVOVNWBVCVNQVNWBVLWAADVMADUEZVGVRVKVTW
      GVFVQVDVEVPUFUGWGVIVSBVJVEVPVHIUHUIULUJUKRUMWCWFAVMWCVEVMEZOZVGWEWIVGOZVC
      VECUNZVGUOZWBOZWEWJWLWBWJVCWKVGWIVCVGWCVCWHVCWBPSSWJWHWKWIWHVGWCWHQSVECUP
      RWIVGQUQWIWBVGWCWBWHVCWBQSSUMWMVPVEIJZDWDLZWEADBCURWOWEWNVIDBWDVPVHVEIUSU
      TUKRRVAVBR $.
  $}

  ${
    $d b c C $.  $d b c J $.  $d b c X $.
    reglfpcmplem2a.1 $e |- X = U. J $.
    $( The expansion set ` ( X \ U. { c e. C | c C_ ( X \ b ) } ) ` is
       open when ` C ` is a locally finite collection of closed sets.
       Uses ~ lfcldunicld and ~ cldopn .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2a $p |- ( ( C e. ( LocFin ` J ) /\ C C_ ( Clsd ` J ) )
        -> ( X \ U. { c e. C | c C_ ( X \ b ) } ) e. J ) $=
      ( clocfin cfv wcel ccld wss wa cv cdif crab cuni simpl simpr ssrab2 a1i
      lfcldunicld syl3anc cldopn syl ) ABGHIZABJHZKZLZEMCDMNKZEAOZPZUFIZCUKNBIU
      HUEUGUJAKZULUEUGQUEUGRUMUHUIEASTAUJBCFUAUBUKBCFUCUD $.
  $}

  ${
    $d b c C $.  $d c X $.
    $( A closed set ` b ` is contained in the expansion set
       ` ( X \ U. { c e. C | c C_ ( X \ b ) } ) ` whenever ` b C_ X ` .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2b $p |- ( b C_ X ->
        b C_ ( X \ U. { c e. C | c C_ ( X \ b ) } ) ) $=
      ( cv wss cdif crab cuni wceq dfss4 biimpi eqimss2 syl cpw wcel wral velpw
      wi a1i biimpri rgen rabss mpbir sspwuni mpbi sscon ax-mp sstrd ) CEZBFZUJ
      BBUJGZGZBDEZULFZDAHZIZGZUKUMUJJZUJUMFUKUSUJBKLUJUMMNUMURFZUKUQULFZUTUPULO
      ZFZVAVCUOUNVBPZSZDAQVEDAVEUNAPVDUODULRUATUBUODAVBUCUDUPULUEUFUQULBUGUHTUI
      $.
  $}

  ${
    $d b n p u B $.  $d b n p u J $.  $d n p u X $.
    reglfpcmplem2c.1 $e |- X = U. J $.
    $( The "finite-meeting" open cover has the same union as ` J ` .  For
       each ` p e. X ` , ~ locfinnei gives a neighborhood meeting finitely
       many elements of ` B ` , which lands in the restricted class.
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2c $p |- ( B e. ( LocFin ` J ) ->
      U. { u e. J | { b e. B | ( b i^i u ) =/= (/) } e. Fin } = X ) $=
      ( vp vn clocfin cfv wcel cv cin c0 wne crab cfn cuni a1i wa ssrab2 unissi
      wss eqcomi sseqtri wceq wel locfinnei simprrl simprl simprrr ineq2 neeq1d
      eqid rabbidv eleq1d elrab sylanbrc elunii syl2anc rexlimddv ssrdv eqsstrd
      weq ex eqssd ) BCIJKZELZALZMZNOZEBPZQKZACPZRZDVODUCVGVOCRZDVNCVMACUAUBDVP
      FUDUESVGDVPVODVPUFVGFSVGGVPVOVGGLZVPKZVQVOKZVGVRTZGHUGZVHHLZMZNOZEBPZQKZT
      ZVSHCBVQHCVPEVPUNUHVTWBCKZWGTTZWAWBVNKZVSVTWHWAWFUIWIWHWFWJVTWHWGUJVTWHWA
      WFUKVMWFAWBCAHVDZVLWEQWKVKWDEBWKVJWCNVIWBVHULUMUOUPUQURVQWBVNUSUTVAVEVBVC
      VF $.
  $}

  ${
    $d b c t u B $.  $d c t u C $.  $d b t u J $.
    $( Each element of a refinement of the finite-meeting cover meets only
       finitely many elements of ` B ` .  Uses the refinement property to
       get a containing open set in the finite-meeting cover, then subset
       finiteness.
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2d $p |- ( ( C Ref
        { u e. J | { b e. B | ( b i^i u ) =/= (/) } e. Fin } /\
        c e. C ) ->
      { b e. B | ( b i^i c ) =/= (/) } e. Fin ) $=
      ( vt cv cin c0 wne crab cfn wcel cref wbr wa wss refssex syl simprl ineq2
      weq neeq1d rabbidv eleq1d elrab biimpi simprd simprr simpl sslin ss2rabdv
      wi ssn0 ex ssfi syl2anc rexlimddv ) CEHZAHZIZJKZEBLZMNZADLZOPFHZCNQZVGGHZ
      RZUTVGIZJKZEBLZMNZGVFGCVFVGSVHVIVFNZVJQQZUTVIIZJKZEBLZMNZVMVSRZVNVPVOVTVH
      VOVJUAVOVIDNZVTVOWBVTQVEVTAVIDAGUCZVDVSMWCVCVREBWCVBVQJVAVIUTUBUDUEUFUGUH
      UITVPVJWAVHVOVJUJVJVLVREBVJUTBNZQZVKVQRZVLVRUNWEVJWFVJWDUKVGVIUTULTWFVLVR
      VKVQUOUPTUMTVSVMUQURUS $.
  $}

  ${
    $d b c d C X $.
    $( If ` c e. C ` , ` c C_ X ` , and ` c ` meets the expansion set
       ` ( X \ U. { d e. C | d C_ ( X \ b ) } ) ` , then ` c ` meets ` b ` .
       The contrapositive: if ` c C_ ( X \ b ) ` then ` c ` is absorbed
       by the union, making intersection with the expansion empty.
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2e $p |- ( ( c e. C /\ c C_ X /\
      ( c i^i ( X \ U. { d e. C | d C_ ( X \ b ) } ) ) =/= (/) ) ->
      ( c i^i b ) =/= (/) ) $=
      ( cv wcel wss cdif crab cuni cin c0 wne wa wceq simpll simpr wb syl mpbid
      reldisj sseq1 elrab sylanbrc elssuni ssrin disjdif sseq0 mpan2 ex necon3d
      simplr 3impia ) DFZAGZUOBHZUOBEFZBCFZIZHZEAJZKZIZLZMNUOUSLZMNUPUQOZVFMVEM
      VGVFMPZVEMPZVGVHOZUOVBGZVIVJUPUOUTHZVKUPUQVHQVJVHVLVGVHRVJUQVHVLSUPUQVHUM
      UOUSBUBTUAVAVLEUOAURUOUTUCUDUEVKUOVCHZVIUOVBUFVMVEVCVDLZHZVIUOVCVDUGVOVNM
      PVIVCBUHVEVNUIUJTTTUKULUN $.
  $}

  ${
    $d b c d n t C X $.
    $( If the expansion set ` ( X \ U. { d e. C | d C_ ( X \ b ) } ) ` meets
       ` n ` , then there exists ` c e. C ` that meets both ` n ` and ` b ` .
       The argument: take an element of the intersection; it lies in
       ` X = U. C ` , giving ` c e. C ` ; then ` c ` meets ` n ` (sharing the
       element) and ` c ` meets ` b ` (by ~ reglfpcmplem2e ).
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2f $p |- ( ( U. C = X /\ C C_ ~P X /\
      ( ( X \ U. { d e. C | d C_ ( X \ b ) } ) i^i n ) =/= (/) ) ->
      E. c e. C ( ( c i^i n ) =/= (/) /\ ( c i^i b ) =/= (/) ) ) $=
      ( vt cuni wss cv cdif cin c0 wne wa wcel simpr syl adantr jca wceq cpw n0
      crab wrex wex biimpi adantl elinel1 eldifi eleqtrrd eluni2 elinel2 inelcm
      wel simpl simplr sseldd elpwi id syl3anc reglfpcmplem2e reximdva exlimddv
      w3a ex mpd 3impia ) AHZCUAZACUBZIZCFJCDJZKIFAUDHZKZBJZLZMNZEJZVPLMNZVSVML
      MNZOZEAUEZVJVLOZVRWCWDVROZGJZVQPZWCGVRWGGUFZWDVRWHGVQUCUGUHWEWGOZGEUOZEAU
      EZWCWIWFVIPZWKWIWFCVIWIWFVOPZWFCPWIWGWMWEWGQZWFVOVPUIRZWFCVNUJRWEVJWGWDVJ
      VRVJVLUPSSUKWLWKEWFAULUGRWIWJWBEAWIVSAPZOZWJWBWQWJOZVTWAWRWJGBUOZOVTWRWJW
      SWQWJQZWQWSWJWIWSWPWIWGWSWNWFVOVPUMRSSTWFVSVPUNRWRWPVSCIZVSVOLMNZVEZWAWRW
      PXAXBXCWIWPWJUQZWRVSVKPXAWRAVKVSWQVLWJWIVLWPWEVLWGWDVLVRVJVLQSSSSXDURVSCU
      SRWRWJWMOXBWRWJWMWTWQWMWJWIWMWPWOSSTWFVSVOUNRXCUTVAACDEFVBRTVFVCVGVDVFVH
      $.
  $}

  ${
    $d b c d n s t B C X $.
    $( Helper for local finiteness of the expansion collection.  If ` C `
       covers ` X ` , ` C C_ ~P X ` , each element of ` C ` meets finitely
       many elements of ` B ` , and only finitely many elements of ` C ` meet
       ` n ` , then only finitely many expansion sets
       ` ( X \ U. { d e. C | d C_ ( X \ b ) } ) ` meet ` n ` .
       Uses ~ reglfpcmplem2f , ~ iunfi , and ~ ssfi .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2g $p |- ( ( ( U. C = X /\ C C_ ~P X ) /\
      ( A. c e. C { b e. B | ( b i^i c ) =/= (/) } e. Fin /\
        { c e. C | ( c i^i n ) =/= (/) } e. Fin ) ) ->
      { b e. B |
        ( ( X \ U. { d e. C | d C_ ( X \ b ) } ) i^i n ) =/= (/) }
        e. Fin ) $=
      ( vs vt wss wa cv cin c0 wne crab cfn wcel neeq1d syl cuni wceq wral ciun
      cpw cdif simprr simprl id ineq2d rabbidv eleq1d cbvralvw biimpi wi ssrab2
      ssralv ax-mp iunfi syl2anc wrex simpl simpll simplr difeq2d sseq2d unieqd
      simpr ineq1d elrab reglfpcmplem2f syl3anc anbi12d cbvrexvw sylib sylanbrc
      weq simprd a1i incom eqnetrrid idd sselid biimpri syl6 syl5 a1d impd jcad
      jctild reximdv2 mpd eliun sylibr ex ssrdv ssfi ) BUADUBZBDUEJZKZELZFLZMZN
      OZEAPZQRZFBUCZXBCLZMZNOZFBPZQRZKZKZHXKXAHLZMZNOZEAPZUDZQRZDGLZDXAUFZJZGBP
      ZUAZUFZXHMZNOZEAPZXSJYIQRXNXLXRQRZHXKUCZXTWTXGXLUGXNYJHBUCZYKXNXGYLWTXGXL
      UHXGYLXFYJFHBFHVQZXEXRQYMXDXQEAYMXCXPNYMXBXOXAYMUIZUJSUKULUMUNTXKBJYLYKUO
      XJFBUPYJHXKBUQURTHXKXRUSUTXNIYIXSXNILZYIRZYOXSRZXNYPKZYOXRRZHXKVAZYQYRXOX
      HMZNOZXOYOMZNOZKZHBVAZYTYRXJXBYOMZNOZKZFBVAZUUFYRWRWSDYADYOUFZJZGBPZUAZUF
      ZXHMZNOZUUJYRXNWRXNYPVBZWRWSXMVCTYRXNWSUURWRWSXMVDTYRYPUUQXNYPVHZYPYOARZU
      UQYPUUTUUQKYHUUQEYOAEIVQZYGUUPNUVAYFUUOXHUVAYEUUNDUVAYDUUMUVAYCUULGBUVAYB
      UUKYAUVAXAYODUVAUIZVEVFUKVGVEVISVJUNVRTBCDIFGVKVLUUIUUEFHBYMXJUUBUUHUUDYM
      XIUUANYMXBXOXHYNVISZYMUUGUUCNYMXBXOYOYNVISVMVNVOYRUUEYSHBXKYRXOBRZUUEKZXO
      XKRZYSUVEUVFUOYRUVEUVDUUBUVFUVDUUEVBUVDUUBUUDUHXJUUBFXOBUVCVJVPVSYRUVDUUE
      YSYRUUEYSUOUVDUUEYOXOMZNOZYRYSUUEUVGUUCNXOYOVTUUBUUDVHWAYRUVHUUTUVHKZYSYR
      UVHUVHUUTYRUVHWBYRYIAYOYHEAUPUUSWCWJYSUVIXQUVHEYOAUVAXPUVGNUVAXAYOXOUVBVI
      SVJWDWEWFWGWHWIWKWLHYOXKXRWMWNWOWPXSYIWQUT $.
  $}

  ${
    $d b c d n p s t u B C J X $.
    reglfpcmplem2h.1 $e |- X = U. J $.
    $( For each point ` p ` of ` X ` , there is a neighborhood ` n ` in ` J `
       meeting finitely many expansion sets.  This combines ~ locfinnei
       (applied to the locally finite closed cover ` C ` ) with
       ~ reglfpcmplem2g .  (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2h $p |- ( ( ( J e. Top /\ B e. ( LocFin ` J ) /\
        B C_ ( Clsd ` J ) ) /\ ( C e. ( LocFin ` J ) /\ C C_ ( Clsd ` J ) /\
        C Ref { u e. J | { b e. B | ( b i^i u ) =/= (/) } e. Fin } ) /\
      p e. X ) -> E. n e. J ( p e. n /\
        { b e. B | ( ( X \ U. { d e. C | d C_ ( X \ b ) } ) i^i n )
          =/= (/) } e. Fin ) ) $=
      ( vs wcel wss cv cin c0 wne crab cfn wa ctop clocfin cfv ccld w3a wbr wel
      cref wrex cdif cuni simp21 locfinnei syl2anc wceq cpw wral eqid locfinbas
      simp3 syl eqcomd simp22 cldss2 a1i sstrd jca adantr simp23 reglfpcmplem2d
      simpl simpr ralrimiva reglfpcmplem2g ex anim2d reximdv mpd ) EUALBEUBUCZL
      BEUDUCZMUEZCVSLZCVTMZCHNZANOPQHBRSLAERUHUFZUEZGNZFLZUEZGDUGZKNZDNZOPQKCRS
      LZTZDEUIZWJFINFWDUJMICRUKUJWLOPQHBRSLZTZDEUIWIWBWHWOWAWBWCWEWHULZWAWFWHUT
      CWGDEFKJUMUNWIWNWQDEWIWMWPWJWIWMWPWIWMTZCUKZFUOZCFUPZMZTZWDWKOPQHBRSLZKCU
      QZWMTWPWIXDWMWIXAXCWIFWTWIWBFWTUOWRCEFWTJWTURUSVAVBWICVTXBWAWBWCWEWHVCVTX
      BMWIEFJVDVEVFVGVHWSXFWMWIXFWMWIXEKCWIWKCLZTZWEXGXEXHWIWEWIXGVKWAWBWCWEWHV
      IVAWIXGVLABCEHKVJUNVMVHWIWMVLVGBCDFHKIVNUNVOVPVQVR $.
  $}

  ${
    $d b d f n s t w z P C X $.  $d D b n s t w z $.
    reglfpcmplem2j.1 $e |- D = ran ( t e. P |->
      ( ( X \ U. { d e. C | d C_ ( X \ t ) } ) i^i ( f ` t ) ) ) $.
    $( Finiteness transfer for the locally finite bound: if the set of
       ` b e. P ` whose expansion set meets ` n ` is finite, then the set of
       elements of ` D ` that meet ` n ` is also finite.  This holds because
       each element of ` D ` is ` ( E ( t ) i^i ( f `` t ) ) C_ E ( t ) ` for
       some ` t e. P ` , so meeting ` n ` forces ` E ( t ) ` to also meet
       ` n ` .  (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2j $p |- (
      { b e. P | ( ( X \ U. { d e. C | d C_ ( X \ b ) } ) i^i n )
        =/= (/) } e. Fin
      -> { s e. D | ( s i^i n ) =/= (/) } e. Fin ) $=
      ( vw vz cv cdif wss crab cin c0 wcel cuni wne cfn cfv wceq cab abrexfi wa
      wrex weq ineq1 neeq1d elrab cmpt crn eleq2i cvv wb vex eqid elrnmpt ax-mp
      biimpi sylbi adantr simprl simprr ineq1d inss1 a1i eqsstrd simplr syl2anc
      ssrin id difeq2d sseq2d rabbidv unieqd sylanbrc jca ex reximdv2 mpd eqeq1
      ssn0 rexbidv elab2 biimpri syl ssriv ssfi mpan2 ) GJNZGINZOZPZJBQZUAZOZFN
      ZRZSUBZIDQZUCTLNZGWNGANZOZPZJBQZUAZOZXFENUDZRZUEZAXDUIZLUFZUCTZHNZXARZSUB
      ZHCQZUCTZALXDXMUGXQYAXPPYBMYAXPMNZYATYCCTZYCXARZSUBZUHZYCXPTZXTYFHYCCHMUJ
      XSYESXRYCXAUKULUMYGYCXMUEZAXDUIZYHYGYIADUIZYJYDYKYFYDYCADXMUNZUOZTZYKCYMY
      CKUPYNYKYCUQTYNYKURMUSZADXMYCYLUQYLUTVAVBVCVDVEYGYIYIADXDYGXFDTZYIUHZXFXD
      TZYIUHYGYQUHZYRYIYSYPXKXARZSUBZYRYGYPYIVFYSYEYTPYFUUAYSYEXMXARZYTYSYCXMXA
      YGYPYIVGZVHUUBYTPZYSXMXKPUUDXKXLVIXMXKXAVNVBVJVKYDYFYQVLYEYTWFVMXCUUAIXFD
      IAUJZXBYTSUUEWTXKXAUUEWSXJGUUEWRXIUUEWQXHJBUUEWPXGWNUUEWOXFGUUEVOVPVQVRVS
      VPVHULUMVTUUCWAWBWCWDYHYJXOYJLYCXPYOLMUJXNYIAXDXEYCXMWEWGXPUTWHWIWJVDWKXP
      YAWLWMWJ $.
  $}

  ${
    $d b d f h n r s t w z P C X $.  $d D b n r s w z $.
    reglfpcmplem2j3.1 $e |- D = ran ( t e. P |->
      ( ( X \ U. { d e. C | d C_ ( X \ t ) } ) i^i ( f ` t ) ) ) $.
    $( Wrapper for ~ reglfpcmplem2j avoiding the ` $d D t ` constraint
       by renaming the map-to variable ` t ` to ` r ` via ~ cbvmptv .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2j3 $p |- (
      { b e. P | ( ( X \ U. { d e. C | d C_ ( X \ b ) } ) i^i n )
        =/= (/) } e. Fin
      -> { s e. D | ( s i^i n ) =/= (/) } e. Fin ) $=
      ( vr cv cdif wss crab cuni cfv cin cmpt crn weq id difeq2d sseq2d rabbidv
      unieqd fveq2 ineq12d cbvmptv rneqi eqtri reglfpcmplem2j ) LBCDEFGHIJCADGJ
      MZGAMZNZOZJBPZQZNZUOEMZRZSZTZUALDGUNGLMZNZOZJBPZQZNZVEVARZSZTZUAKVDVMALDV
      CVLALUBZUTVJVBVKVNUSVIGVNURVHVNUQVGJBVNUPVFUNVNUOVEGVNUCUDUEUFUGUDUOVEVAU
      HUIUJUKULUM $.
  $}

  ${
    $d b d p t B C J X f $.  $d D b p $.
    reglfpcmplem2k.1 $e |- X = U. J $.
    reglfpcmplem2k.2 $e |- D = ran ( t e. B |->
      ( ( X \ U. { d e. C | d C_ ( X \ t ) } ) i^i ( f ` t ) ) ) $.
    $( The collection ` D ` covers ` X ` : every point of ` X ` belongs to
       some element of ` D ` .  For ` p e. X ` , ~ locfinbas gives
       ` p e. U. B ` , so there is ` t e. B ` with ` p e. t ` .  Then
       ` p e. E ( t ) ` by ~ reglfpcmplem2b and ` p e. ( f `` t ) ` by
       ` t C_ ( f `` t ) ` , so ` p e. ( E ( t ) i^i ( f `` t ) ) e. D ` .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2k $p |- ( ( B e. ( LocFin ` J ) /\ B C_ ( Clsd ` J )
        /\ A. b e. B b C_ ( f ` b ) )
      -> X C_ U. D ) $=
      ( vp cfv wcel wss cv wral cuni syl cdif clocfin ccld wceq simp1 locfinbas
      w3a eqid wa crab cin simp2 adantr simpr sseldd cldss reglfpcmplem2b simp3
      weq id fveq2 sseq12d rspcva syl2anc ssind cmpt crn cvv fvex inex2 difeq2d
      a1i sseq2d rabbidv unieqd fveq2d ineq12d eqcomd elrnmptdv eleqtrd elssuni
      eqcomi sstrd ralrimiva unissb sylibr eqsstrd ) BFUAMNZBFUBMZOZHPZWJEPZMZO
      ZHBQZUFZGBRZDRZWOWGGWPUCWGWIWNUDBFGWPJWPUGUESWOLPZWQOZLBQWPWQOWOWSLBWOWRB
      NZUHZWRGIPZGWRTZOZICUIZRZTZWRWKMZUJZWQXAWRXGXHXAWRGOZWRXGOXAWRWHNXJXABWHW
      RWOWIWTWGWIWNUKULWOWTUMZUNWRFGJUOSCGLIUPSXAWTWNWRXHOZXKWOWNWTWGWIWNUQULWM
      XLHWRBHLURZWJWRWLXHXMUSWJWRWKUTVAVBVCVDXAXIDNXIWQOXAXIABGXBGAPZTZOZICUIZR
      ZTZXNWKMZUJZVEZVFZDXAABYAWRXIYBVGYBUGXKXIVGNXAXHXGWRWKVHVIVKXAALURZUHZYAX
      IYEXSXGXTXHYEXRXFGYEXQXEYEXPXDICYEXOXCXBYEXNWRGXAYDUMZVJVLVMVNVJYEXNWRWKY
      FVOVPVQVRYCDUCXADYCKWAVKVSXIDVTSWBWCLBWQWDWEWF $.
  $}

  ${
    $d d t B C J X f y $.
    reglfpcmplem2l.1 $e |- X = U. J $.
    reglfpcmplem2l.2 $e |- D = ran ( t e. B |->
      ( ( X \ U. { d e. C | d C_ ( X \ t ) } ) i^i ( f ` t ) ) ) $.
    $( Every element of ` D ` is open in ` J ` .  Each
       ` ( E ( t ) i^i ( f `` t ) ) ` is the intersection of ` E ( t ) ` (open
       by ~ reglfpcmplem2a ) and ` ( f `` t ) e. y C_ J ` (open because ` f `
       maps into ` y ` ), so it is in ` J ` by ~ inopn .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2l $p |- ( ( J e. Top
        /\ ( C e. ( LocFin ` J ) /\ C C_ ( Clsd ` J ) )
        /\ ( f : B --> y /\ y C_ J ) )
      -> D C_ J ) $=
      ( wcel cfv wss wa cv cdif adantr syl simpr ctop clocfin ccld wf crab cuni
      w3a cin cmpt crn wceq a1i simp1 simp2 reglfpcmplem2a simp3 simpl ffvelcdm
      wral syl2anc sseldd inopn syl3anc ralrimiva eqid rnmptss eqsstrd ) GUALZD
      GUBMLDGUCMNOZCAPZFPZUDZVJGNZOZUGZEBCHIPHBPZQNIDUEUFQZVPVKMZUHZUIZUJZGEWAU
      KVOKULVOVSGLZBCUSWAGNVOWBBCVOVPCLZOZVHVQGLZVRGLWBVOVHWCVHVIVNUMRWDVIWEVOV
      IWCVHVIVNUNRDGHBIJUOSWDVJGVRVOVMWCVOVNVMVHVIVNUPZVLVMTSRWDVLWCVRVJLVOVLWC
      VOVNVLWFVLVMUQSRVOWCTCVJVPVKURUTVAVQVRGVBVCVDBCVSGVTVTVEVFSVG $.
  $}

  ${
    $d b d n p s t u B C J X f $.  $d D b n p s u $.
    reglfpcmplem2m.1 $e |- X = U. J $.
    reglfpcmplem2m.2 $e |- D = ran ( t e. B |->
      ( ( X \ U. { d e. C | d C_ ( X \ t ) } ) i^i ( f ` t ) ) ) $.
    $( The collection ` D ` is locally finite: each point has a neighborhood
       meeting only finitely many elements of ` D ` .  This combines the
       locally finite neighborhood property ~ reglfpcmplem2h of the expansion
       sets with the finiteness transfer ~ reglfpcmplem2j .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2m $p |- ( ( ( J e. Top /\ B e. ( LocFin ` J )
        /\ B C_ ( Clsd ` J ) )
      /\ ( C e. ( LocFin ` J ) /\ C C_ ( Clsd ` J )
        /\ C Ref { u e. J | { b e. B | ( b i^i u ) =/= (/) } e. Fin } ) )
      -> A. p e. X E. n e. J ( p e. n
        /\ { s e. D | ( s i^i n ) =/= (/) } e. Fin ) ) $=
      ( wcel wss cv crab wa ctop clocfin cfv ccld w3a cin wne cfn cref wbr wrex
      c0 wel cdif df-3an biimpri reglfpcmplem2h reglfpcmplem2j3 anim2i ralrimiva
      cuni syl reximi ) HUAPCHUBUCZPCHUDUCZQUEZDVDPDVEQDLRZARUFULUGLCSUHPAHSUIU
      JUEZTZKGUMZJRGRZUFULUGJESUHPZTZGHUKZKIVIKRIPZTZVJIMRIVGUNQMDSVAUNVKUFULUG
      LCSUHPZTZGHUKZVNVPVFVHVOUEZVSVTVPVFVHVOUOUPACDGHIKLMNUQVBVRVMGHVQVLVJBDEC
      FGIJLMOURUSVCVBUT $.
  $}

  ${
    $d d t w z B C X f y $.  $d D t w z $.
    reglfpcmplem2n.1 $e |- D = ran ( t e. B |->
      ( ( X \ U. { d e. C | d C_ ( X \ t ) } ) i^i ( f ` t ) ) ) $.
    $( Each element of ` D ` is a subset of some element of ` y ` .  Since
       each ` D ` -element has the form ` ( E ( t ) i^i ( f `` t ) ) ` and
       ` ( f `` t ) e. y ` , the inclusion ` ( E ( t ) i^i ( f `` t ) ) C_
       ( f `` t ) ` by ~ inss2 provides the witness.
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2n $p |- ( f : B --> y
      -> A. z e. D E. w e. y z C_ w ) $=
      ( cv wf wss wrex wcel wa cdif cvv syl2anc crab cuni cfv cin wceq cmpt crn
      simpr eleq2i wb vex elrnmpt ax-mp biimpi sylbi syl simpll simprl ffvelcdm
      eqid simprr inss2 a1i eqsstrd sseq2 rspcev rexlimddv ralrimiva ) EALZHLZM
      ZBLZCLZNZCVIOZBGVKVLGPZQZVLIJLIDLZRNJFUAUBRZVRVJUCZUDZUEZVODEVQVPWBDEOZVK
      VPUHVPVLDEWAUFZUGZPZWCGWEVLKUIWFWCVLSPWFWCUJBUKDEWAVLWDSWDUTULUMUNUOUPVQV
      REPZWBQZQZVTVIPZVLVTNZVOWIVKWGWJVKVPWHUQVQWGWBUREVIVRVJUSTWIVLWAVTVQWGWBV
      AWAVTNWIVSVTVBVCVDVNWKCVTVIVMVTVLVEVFTVGVH $.
  $}

  ${
    $d d h r t w z B C X f y $.  $d D r w z $.
    reglfpcmplem2n3.1 $e |- D = ran ( t e. B |->
      ( ( X \ U. { d e. C | d C_ ( X \ t ) } ) i^i ( f ` t ) ) ) $.
    $( Wrapper for ~ reglfpcmplem2n avoiding the ` $d D t ` constraint
       by renaming the map-to variable ` t ` to ` r ` via ~ cbvmptv .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2n3 $p |- ( f : B --> y
      -> A. z e. D E. w e. y z C_ w ) $=
      ( vr cv cdif wss crab cuni cfv cin cmpt crn weq id difeq2d sseq2d rabbidv
      unieqd fveq2 ineq12d cbvmptv rneqi eqtri reglfpcmplem2n ) ABCLEFGHIJGDEIJ
      MZIDMZNZOZJFPZQZNZUOHMZRZSZTZUALEIUNILMZNZOZJFPZQZNZVEVARZSZTZUAKVDVMDLEV
      CVLDLUBZUTVJVBVKVNUSVIIVNURVHVNUQVGJFVNUPVFUNVNUOVEIVNUCUDUEUFUGUDUOVEVAU
      HUIUJUKULUM $.
  $}

  ${
    $d b c d f n p s t u w z B C J X y $.  $d D b c n p s u w z $.
    reglfpcmplem2i.1 $e |- X = U. J $.
    reglfpcmplem2i.2 $e |- D = ran ( t e. B |->
      ( ( X \ U. { d e. C | d C_ ( X \ t ) } ) i^i ( f ` t ) ) ) $.
    $( The collection ` D ` of open sets ` ( E ( b ) i^i ( f `` b ) ) ` is a
       locally finite open refinement of ` y ` .  Here ` B ` is a locally
       finite closed refinement of ` y ` , ` C ` is an auxiliary locally finite
       closed refinement of the finite-meeting open cover, ` f : B --> y `
       chooses a cover element for each ` b e. B ` , and ` D ` collects the
       intersections of expansion sets with the chosen cover elements.  This is
       the core construction for ~ reglfpcmplem2 .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2i $p |- ( ( ( ( J e. Top /\ y C_ J /\ X = U. y )
        /\ ( B e. ( LocFin ` J ) /\ B C_ ( Clsd ` J ) /\ B Ref y ) )
      /\ ( ( C e. ( LocFin ` J ) /\ C C_ ( Clsd ` J )
        /\ C Ref { u e. J | { b e. B | ( b i^i u ) =/= (/) } e. Fin } )
      /\ ( f : B --> y /\ A. b e. B b C_ ( f ` b ) ) ) )
      -> ( D e. ( ( LocFin ` J ) i^i ~P J ) /\ D Ref y ) ) $=
      ( vp vn wcel cv wss w3a wa vs vz ctop cuni wceq clocfin cfv ccld cref wbr
      vw cin c0 wne crab cfn wf wral cpw simpll1 simplr1 simplr2 reglfpcmplem2k
      wel wrex simprrr syl3anc simprl1 simprl2 simprrl reglfpcmplem2l syl122anc
      simpll2 unissd sseqtrrdi eqssd 3jca simprl jca reglfpcmplem2m syl wb eqid
      a1i mpbir3and sselpwd elind simpll3 eqtr3d reglfpcmplem2n3 isref mpbir2and
      islocfin ) HUCPZAQZHRZIWOUDZUEZSZDHUFUGZPZDHUHUGZRZDWOUIUJZSZTZEWTPZEXBRZ
      EJQZBQULUMUNJDUOUPPBHUOUIUJZSZDWOGQZUQZXIXIXLUGRJDURZTZTZTZFWTHUSZULPFWOU
      IUJZXQWTXRFXQFWTPZWNIFUDZUEZNOVDUAQOQULUMUNUAFUOUPPTOHVENIURZWNWPWRXEXPUT
      ZXQIYAXQXAXCXNIYARXAXCXDWSXPVAZXAXCXDWSXPVBZXFXKXMXNVFCDEFGHIJKLMVCVGXQYA
      HUDIXQFHXQWNXGXHXMWPFHRYDXGXHXJXOXFVHXGXHXJXOXFVIXFXKXMXNVJZWNWPWRXEXPVMA
      CDEFGHIKLMVKVLZVNLVOVPZXQWNXAXCSZXKTYCXQYJXKXQWNXAXCYDYEYFVQXFXKXOVRVSBCD
      EFGOHIUANJKLMVTWAXTWNYBYCSWBXQNFOHIYAUALYAWCZWMWDWEXQFHUCYDYHWFZWGXQXSWQY
      AUEZUBQUKQRUKWOVEUBFURZXQIWQYAWNWPWRXEXPWHYIWIXQXMYNYGAUBUKCDEFGIKMWJWAXQ
      FXRPXSYMYNTWBYLUBUKFWOXRYAWQYKWQWCWKWAWLVS $.
  $}

  ${
    $d b f w B V y $.
    $( Axiom of Choice extraction from a refinement: if ` B ` refines ` y `
       then there exists a choice function ` f : B --> y ` with each element
       of ` B ` mapped to a superset in ` y ` .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2o $p |- ( ( B e. V /\ B Ref y ) ->
      E. f ( f : B --> y /\ A. b e. B b C_ ( f ` b ) ) ) $=
      cB cV wcel cB vy cv cref wbr wa cB cV wcel vb cv vw cv wss vw vy cv
      wrex vb cB wral cB vy cv vf cv wf vb cv vb cv vf cv cfv wss vb cB wral
      wa vf wex cB cV wcel cB vy cv cref wbr simpl cB vy cv cref wbr vb cv
      vw cv wss vw vy cv wrex vb cB wral cB cV wcel cB vy cv cref wbr vb cv
      vw cv wss vw vy cv wrex vb cB cB vy cv cref wbr vb cv cB wcel vb cv vw
      cv wss vw vy cv wrex vw cB vy cv vb cv refssex ex ralrimiv adantl cB cV
      wcel vb cv vw cv wss vw vy cv wrex vb cB wral cB vy cv vf cv wf vb cv
      vb cv vf cv cfv wss vb cB wral wa vf wex vb cv vw cv wss vb cv vb cv
      vf cv cfv wss vb vw cB vy cv vf cV vw cv vb cv vf cv cfv vb cv sseq2
      ac6sg imp syl2anc $.
  $}

  ${
    $d b s u B $.
    $( Bound variable change for the intersection-nonemptiness restricted
       class abstraction: convert bound variable ` s ` to ` b ` .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2pa $p |- { s e. B | ( s i^i u ) =/= (/) } =
      { b e. B | ( b i^i u ) =/= (/) } $=
      ( cv cin c0 wne weq wceq wb ineq1 neeq1 syl cbvrabv ) CEZAEZFZGHZDEZQFZGH
      ZCDBCDIRUAJSUBKPTQLRUAGMNO $.
  $}

  ${
    $d b n u B J $.
    $( Backward direction of ~ elrab for the locally finite cover set: if
       ` n ` is in ` J ` and ` { b e. B | ( b i^i n ) =/= (/) } ` is finite,
       then ` n ` is in the restricted abstraction.
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2pb $p |- ( ( n e. J /\ { b e. B | ( b i^i n ) =/= (/) }
      e. Fin ) -> n e. { u e. J | { b e. B | ( b i^i u ) =/= (/) }
      e. Fin } ) $=
      ( cv wcel cin c0 wne crab cfn wa simpl simpr weq wceq wb ineq2 neeq1 syl
      rabbidv eleq1d elrab sylanbrc ) CFZDGZEFZUFHZIJZEBKZLGZMUGULUFUHAFZHZIJZE
      BKZLGZADKGUGULNUGULOUQULAUFDACPZUPUKLURUOUJEBURUNUIQUOUJRUMUFUHSUNUIITUAU
      BUCUDUE $.
  $}

  ${
    $d b n p s u B J X $.
    reglfpcmplem2p.1 $e |- X = U. J $.
    $( The locally finite cover
       ` { u e. J | { b e. B | ( b i^i u ) =/= (/) } e. Fin } ` has the
       same union as ` J ` when ` B ` is locally finite in ` J ` .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2p $p |- ( B e. ( LocFin ` J ) ->
      X = U. { u e. J | { b e. B | ( b i^i u ) =/= (/) } e. Fin } ) $=
      cB cJ clocfin cfv wcel cX vb cv vu cv cin c0 wne vb cB crab cfn
      wcel vu cJ crab cuni cB cJ clocfin cfv wcel vp cX vb cv vu cv cin
      c0 wne vb cB crab cfn wcel vu cJ crab cuni cB cJ clocfin cfv wcel
      vp cv cX wcel vp cv vb cv vu cv cin c0 wne vb cB crab cfn wcel vu
      cJ crab cuni wcel cB cJ clocfin cfv wcel vp cv cX wcel wa vp cv
      vn cv wcel vs cv vn cv cin c0 wne vs cB crab cfn wcel wa vp cv vb
      cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ crab cuni wcel vn
      cJ cB vp cv vn cJ cX vs reglfpcmplem2p.1 locfinnei vn cv cJ wcel
      vp cv vn cv wcel vs cv vn cv cin c0 wne vs cB crab cfn wcel wa wa
      vp cv vb cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ crab cuni
      wcel cB cJ clocfin cfv wcel vp cv cX wcel wa vn cv cJ wcel vp cv
      vn cv wcel vs cv vn cv cin c0 wne vs cB crab cfn wcel wa wa vp cv
      vn cv wcel vn cv vb cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ
      crab wcel vp cv vb cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ
      crab cuni wcel vn cv cJ wcel vp cv vn cv wcel vs cv vn cv cin c0
      wne vs cB crab cfn wcel simprl vn cv cJ wcel vp cv vn cv wcel vs
      cv vn cv cin c0 wne vs cB crab cfn wcel wa wa vn cv cJ wcel vb cv
      vn cv cin c0 wne vb cB crab cfn wcel vn cv vb cv vu cv cin c0 wne
      vb cB crab cfn wcel vu cJ crab wcel vn cv cJ wcel vp cv vn cv
      wcel vs cv vn cv cin c0 wne vs cB crab cfn wcel wa simpl vn cv cJ
      wcel vp cv vn cv wcel vs cv vn cv cin c0 wne vs cB crab cfn wcel
      wa wa vs cv vn cv cin c0 wne vs cB crab vb cv vn cv cin c0 wne vb
      cB crab cfn vs cv vn cv cin c0 wne vs cB crab vb cv vn cv cin c0
      wne vb cB crab wceq vn cv cJ wcel vp cv vn cv wcel vs cv vn cv
      cin c0 wne vs cB crab cfn wcel wa wa vn cB vs vb reglfpcmplem2pa
      a1i vn cv cJ wcel vp cv vn cv wcel vs cv vn cv cin c0 wne vs cB
      crab cfn wcel simprr eqeltrrd vu cB vn cJ vb reglfpcmplem2pb
      syl2anc vp cv vn cv vb cv vu cv cin c0 wne vb cB crab cfn wcel vu
      cJ crab elunii syl2anc adantl rexlimddv ex ssrdv vb cv vu cv cin
      c0 wne vb cB crab cfn wcel vu cJ crab cuni cX wss cB cJ clocfin
      cfv wcel vb cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ crab
      cuni cJ cuni cX vb cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ
      crab cJ vb cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ ssrab2
      unissi reglfpcmplem2p.1 sseqtrri a1i eqssd $.
  $}

  ${
    $d b d f t u z B C J X y $.
    reglfpcmplem2q.1 $e |- X = U. J $.
    $( Assembly lemma for ~ reglfpcmplem2 : given a locally finite closed
       refinement ` B ` of ` y ` and a locally finite closed refinement ` C `
       of the locally finite cover derived from ` B ` , there exists a
       locally finite refinement of ` y ` that is a subset of ` J ` .
       Uses Axiom of Choice to extract a choice function from ` B Ref y ` .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2q $p |- ( ( ( J e. Top /\ y C_ J /\ X = U. y )
      /\ ( B e. ( LocFin ` J ) /\ B C_ ( Clsd ` J ) /\ B Ref y )
      /\ ( C e. ( LocFin ` J ) /\ C C_ ( Clsd ` J )
        /\ C Ref { u e. J | { b e. B | ( b i^i u ) =/= (/) } e. Fin } ) )
      -> E. z e. ( ( LocFin ` J ) i^i ~P J ) z Ref y ) $=
      cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a cB cJ clocfin cfv wcel
      cB cJ ccld cfv wss cB vy cv cref wbr w3a cC cJ clocfin cfv wcel cC cJ
      ccld cfv wss cC vb cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ crab
      cref wbr w3a vz cv vy cv cref wbr vz cJ clocfin cfv cJ cpw cin wrex cJ
      ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a cB cJ clocfin cfv wcel cB
      cJ ccld cfv wss cB vy cv cref wbr w3a wa cC cJ clocfin cfv wcel cC cJ
      ccld cfv wss cC vb cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ crab
      cref wbr w3a wa cB vy cv vf cv wf vb cv vb cv vf cv cfv wss vb cB wral wa
      vz cv vy cv cref wbr vz cJ clocfin cfv cJ cpw cin wrex vf cJ ctop wcel vy
      cv cJ wss cX vy cv cuni wceq w3a cB cJ clocfin cfv wcel cB cJ ccld cfv
      wss cB vy cv cref wbr w3a wa cC cJ clocfin cfv wcel cC cJ ccld cfv wss cC
      vb cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ crab cref wbr w3a wa cB
      cJ clocfin cfv wcel cB vy cv cref wbr cB vy cv vf cv wf vb cv vb cv vf cv
      cfv wss vb cB wral wa vf wex cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq
      w3a cB cJ clocfin cfv wcel cB cJ ccld cfv wss cB vy cv cref wbr w3a wa cC
      cJ clocfin cfv wcel cC cJ ccld cfv wss cC vb cv vu cv cin c0 wne vb cB
      crab cfn wcel vu cJ crab cref wbr w3a wa cB cJ clocfin cfv wcel cB cJ
      ccld cfv wss cB vy cv cref wbr w3a cB cJ clocfin cfv wcel cJ ctop wcel vy
      cv cJ wss cX vy cv cuni wceq w3a cB cJ clocfin cfv wcel cB cJ ccld cfv
      wss cB vy cv cref wbr w3a cC cJ clocfin cfv wcel cC cJ ccld cfv wss cC vb
      cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ crab cref wbr w3a simplr cB
      cJ clocfin cfv wcel cB cJ ccld cfv wss cB vy cv cref wbr simp1 syl cJ
      ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a cB cJ clocfin cfv wcel cB
      cJ ccld cfv wss cB vy cv cref wbr w3a wa cC cJ clocfin cfv wcel cC cJ
      ccld cfv wss cC vb cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ crab
      cref wbr w3a wa cB cJ clocfin cfv wcel cB cJ ccld cfv wss cB vy cv cref
      wbr w3a cB vy cv cref wbr cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq
      w3a cB cJ clocfin cfv wcel cB cJ ccld cfv wss cB vy cv cref wbr w3a cC cJ
      clocfin cfv wcel cC cJ ccld cfv wss cC vb cv vu cv cin c0 wne vb cB crab
      cfn wcel vu cJ crab cref wbr w3a simplr cB cJ clocfin cfv wcel cB cJ ccld
      cfv wss cB vy cv cref wbr simp3 syl vy cB vf cJ clocfin cfv vb
      reglfpcmplem2o syl2anc cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a
      cB cJ clocfin cfv wcel cB cJ ccld cfv wss cB vy cv cref wbr w3a wa cC cJ
      clocfin cfv wcel cC cJ ccld cfv wss cC vb cv vu cv cin c0 wne vb cB crab
      cfn wcel vu cJ crab cref wbr w3a cB vy cv vf cv wf vb cv vb cv vf cv cfv
      wss vb cB wral wa vz cv vy cv cref wbr vz cJ clocfin cfv cJ cpw cin wrex
      cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a cB cJ clocfin cfv wcel
      cB cJ ccld cfv wss cB vy cv cref wbr w3a wa cC cJ clocfin cfv wcel cC cJ
      ccld cfv wss cC vb cv vu cv cin c0 wne vb cB crab cfn wcel vu cJ crab
      cref wbr w3a cB vy cv vf cv wf vb cv vb cv vf cv cfv wss vb cB wral wa wa
      wa vt cB cX vd cv cX vt cv cdif wss vd cC crab cuni cdif vt cv vf cv cfv
      cin cmpt crn cJ clocfin cfv cJ cpw cin wcel vt cB cX vd cv cX vt cv cdif
      wss vd cC crab cuni cdif vt cv vf cv cfv cin cmpt crn vy cv cref wbr wa
      vz cv vy cv cref wbr vz cJ clocfin cfv cJ cpw cin wrex vy vu vt cB cC vt
      cB cX vd cv cX vt cv cdif wss vd cC crab cuni cdif vt cv vf cv cfv cin
      cmpt crn vf cJ cX vb vd reglfpcmplem2q.1 vt cB cX vd cv cX vt cv cdif wss
      vd cC crab cuni cdif vt cv vf cv cfv cin cmpt crn eqid reglfpcmplem2i vz
      cv vy cv cref wbr vt cB cX vd cv cX vt cv cdif wss vd cC crab cuni cdif
      vt cv vf cv cfv cin cmpt crn vy cv cref wbr vz vt cB cX vd cv cX vt cv
      cdif wss vd cC crab cuni cdif vt cv vf cv cfv cin cmpt crn cJ clocfin cfv
      cJ cpw cin vz cv vt cB cX vd cv cX vt cv cdif wss vd cC crab cuni cdif vt
      cv vf cv cfv cin cmpt crn vy cv cref breq1 rspcev syl anassrs exlimddv
      3impa $.
  $}

  ${
    $d u b z s w J y $.
    $( Innermost step for ~ reglfpcmplem2 : apply ~ reglfpcmplem2q with
       ` B = s ` , ` C = w ` , ` X = U. J ` .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2r $p |- ( ( ( J e. Top /\ y C_ J /\ U. J = U. y )
      /\ ( s e. ( LocFin ` J ) /\ s C_ ( Clsd ` J ) /\ s Ref y )
      /\ ( w e. ( LocFin ` J ) /\ w C_ ( Clsd ` J )
        /\ w Ref { u e. J | { b e. s | ( b i^i u ) =/= (/) }
          e. Fin } ) )
      -> E. z e. ( ( LocFin ` J ) i^i ~P J ) z Ref y ) $=
      ( eqid reglfpcmplem2q ) ?????????HI $.
  $}

  ${
    $d u b n p s B J $.
    $( Corollary of ~ reglfpcmplem2p without the ` X ` parameter:
       ` B e. ( LocFin `` J ) ` implies
       ` U. J = U. { u e. J | { b e. B | ( b i^i u ) =/= (/) } e. Fin } ` .
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2pc $p |- ( B e. ( LocFin ` J ) ->
      U. J = U. { u e. J | { b e. B | ( b i^i u ) =/= (/) } e. Fin } ) $=
      ( vp vn vs clocfin cfv wcel cuni cv cin c0 wne crab cfn wa a1i syl2anc ex
      eqid locfinnei simprl simpl wceq reglfpcmplem2pa eqeltrrd reglfpcmplem2pb
      wel simprr elunii adantl rexlimddv ssrdv wss ssrab2 unissi eqssd ) BCHIJZ
      CKZDLZALMNODBPQJZACPZKZUTEVAVEUTELZVAJZVFVEJZUTVGRZEFUJZGLFLZMNOGBPZQJZRZ
      VHFCBVFFCVAGVAUBUCVKCJZVNRZVHVIVPVJVKVDJZVHVOVJVMUDVPVOVBVKMNODBPZQJVQVOV
      NUEVPVLVRQVLVRUFVPFBGDUGSVOVJVMUKUHABFCDUITVFVKVDULTUMUNUAUOVEVAUPUTVDCVC
      ACUQURSUS $.
  $}

  ${
    $d s t u b y J $.
    $( Helper for ~ reglfpcmplem2s : instantiate the refinement hypothesis
       ` H_A ` at the restricted cover
       ` R = { u e. J | { b e. s | ( b i^i u ) =/= (/) } e. Fin } ` to
       obtain ` E. t e. A t Ref R ` .  Uses ~ rspcv with ~ reglfpcmplem2pc
       for the ` U. J = U. R ` premise.
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2t $p |- ( ( ( ( J e. Top /\ A. y e. ~P J ( U. J = U. y
        -> E. t e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) t Ref y ) )
      /\ ( y C_ J /\ U. J = U. y ) )
      /\ ( s e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) /\ s Ref y ) )
      -> E. t e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) t Ref
        { u e. J | { b e. s | ( b i^i u ) =/= (/) } e. Fin } ) $=
      ( ctop wcel cuni cv wceq cref wbr cfv cpw cin wrex wi wa syl clocfin ccld
      wral wss c0 wne crab cfn simprl elinel1 reglfpcmplem2pc simpll ssrab2 a1i
      simpl sselpwd simplr unieq eqeq2d breq2 rexbidv imbi12d rspcv imp syl2anc
      mpd ) DGHZDIZAJZIZKZCJZVILMZCDUANZDUBNOZPZQZRZADOZUCZSVIDUDVKSZSZEJZVPHZW
      CVILMZSZSZVHFJBJPUEUFFWCUGUHHZBDUGZIZKZVLWILMZCVPQZWGWCVNHZWKWGWDWNWBWDWE
      UIWCVNVOUJTBWCDFUKTWGWIVSHZVTWKWMRZWGWIDGWGWBVGWBWFUOZVGVTWAULTWIDUDWGWHB
      DUMUNUPWGWBVTWQVGVTWAUQTWOVTWPVRWPAWIVSVIWIKZVKWKVQWMWRVJWJVHVIWIURUSWRVM
      WLCVPVIWIVLLUTVAVBVCVDVEVF $.
  $}

  ${
    $d s t w u b y z J $.
    $( Second existential elimination for ~ reglfpcmplem2 : given a locally
       finite closed refinement ` s ` of an open cover ` y ` , use the
       hypothesis to obtain a second locally finite closed refinement and
       apply ~ reglfpcmplem2r .  (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2s $p |- ( ( ( ( J e. Top /\ A. y e. ~P J ( U. J = U. y
        -> E. t e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) t Ref y ) )
      /\ ( y C_ J /\ U. J = U. y ) )
      /\ ( s e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) /\ s Ref y ) )
      -> E. z e. ( ( LocFin ` J ) i^i ~P J ) z Ref y ) $=
      ( vw vb vu wcel cuni cv cref wbr cin wrex wa wss w3a syl 3jca clocfin cfv
      ctop wceq ccld cpw wi wral c0 wne crab cfn reglfpcmplem2t wb cbvrexvw a1i
      breq1 simp-4l simpll simprl simprr simplrl elinel1 elinel2 reglfpcmplem2r
      mpbid elpwi simplrr rexlimddv ) DUCIZDJAKZJUDZCKZVKLMCDUAUBZDUEUBZUFZNZOU
      GADUFZUHZPZVKDQZVLPZPZEKZVQIZWDVKLMZPZPZFKZGKHKNUIUJGWDUKULIHDUKZLMZBKVKL
      MBVNVRNOZFVQWHVMWJLMZCVQOZWKFVQOZAHCDEGUMWNWOUNWHWMWKCFVQVMWIWJLUQUOUPVFW
      HWIVQIZWKPZPZVJWAVLRZWDVNIZWDVOQZWFRZWIVNIZWIVOQZWKRZRWLWRWSXBXEWRVJWAVLV
      JVSWBWGWQURWRWCWAWCWGWQUSZVTWAVLUTSWRWCVLXFVTWAVLVASTWRWTXAWFWRWEWTWCWEWF
      WQVBZWDVNVPVCSWRWDVPIZXAWRWEXHXGWDVNVPVDSWDVOVGSWCWEWFWQVHTWRXCXDWKWRWPXC
      WHWPWKUTZWIVNVPVCSWRWIVPIZXDWRWPXJXIWIVNVPVDSWIVOVGSWHWPWKVATTABFHDEGVESV
      I $.
  $}

  ${
    $d s t u b y z J $.
    $( First existential elimination for ~ reglfpcmplem2 : given the covering
       refinement hypothesis and an open cover ` y ` with ` y C_ J ` and
       ` U. J = U. y ` , produce a locally finite open refinement.
       (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2u $p |- ( ( ( J e. Top /\ A. y e. ~P J ( U. J = U. y
        -> E. t e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) t Ref y ) )
      /\ ( y C_ J /\ U. J = U. y ) )
      -> E. z e. ( ( LocFin ` J ) i^i ~P J ) z Ref y ) $=
      ( vs ctop wcel cuni cv wceq cref wbr clocfin cfv cpw cin wrex wi wa mpd
      ccld wral wss simprr simpll simprl sselpwd simplr rsp syl wb cbvrexvw a1i
      breq1 mpbid reglfpcmplem2s rexlimddv ) DFGZDHAIZHJZCIZUSKLZCDMNZDUANOPZQZ
      RZADOZUBZSZUSDUCZUTSZSZEIZUSKLZBIUSKLBVCVGPQEVDVLVEVNEVDQZVLUTVEVIVJUTUDV
      LUSVGGZVFVLUSDFURVHVKUEVIVJUTUFUGVLVHVPVFRURVHVKUHVFAVGUIUJTTVEVOUKVLVBVN
      CEVDVAVMUSKUNULUMUOABCDEUPUQ $.
  $}

  ${
    $d w y t z J $.
    $( Helper for ~ reglfpcmplem2 using ` w ` instead of ` y ` as the bound
       variable in the hypothesis to avoid ` $d ` issues with
       ~ ralrimiva .  (Contributed by Claude, 10-Feb-2026.) $)
    reglfpcmplem2a2 $p |- ( ( J e. Top /\
      A. w e. ~P J ( U. J = U. w ->
        E. t e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) t Ref w ) ) ->
      J e. ParaCmp ) $=
      ( vy vz wcel cuni cv wceq cref wbr cfv cpw cin wrex wi wral wa syl simpr
      ctop clocfin ccld cpacmp simpl wss simpll weq unieq breq2 rexbidv imbi12d
      eqeq2d cbvralvw biimpi simplr elpwi reglfpcmplem2u syl2anc ralrimiva eqid
      jca ex ispcmp sylanbrc ) CUAFZCGZAHZGZIZBHZVHJKZBCUBLZCUCLMNZOZPZACMZQZRZ
      VFVGDHZGZIZEHVTJKEVMVQNOZPZDVQQCUDFVFVRUEZVSWDDVQVSVTVQFZRZWBWCWGWBRZVFWB
      VKVTJKZBVNOZPZDVQQZRVTCUFZWBRWCWHVFWLWHVSVFVSWFWBUGZWESWHVRWLWHVSVRWNVFVR
      TSVRWLVPWKADVQADUHZVJWBVOWJWOVIWAVGVHVTUIUMWOVLWIBVNVHVTVKJUJUKULUNUOSVBW
      HWMWBWHWFWMVSWFWBUPVTCUQSWGWBTVBDEBCURUSVCUTDECVGVGVAVDVE $.
  $}

  ${
    $d s t w y z J $.
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
      ( vw ctop wcel cuni cv wceq cref wbr clocfin cfv ccld cpw wrex wi wral wa
      cin cpacmp weq unieq eqeq2d breq2 rexbidv cbvralvw biimpi reglfpcmplem2a2
      imbi12d anim2i syl ) CEFZCGZAHZGZIZBHZUOJKZBCLMCNMOTZPZQZACOZRZSUMUNDHZGZ
      IZURVEJKZBUTPZQZDVCRZSCUAFVDVKUMVDVKVBVJADVCADUBZUQVGVAVIVLUPVFUNUOVEUCUD
      VLUSVHBUTUOVEURJUEUFUJUGUHUKDBCUIUL $.
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

