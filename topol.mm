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

  $( Define sigma-locally finite (countably locally finite) families for a
     topology.  A family ` A ` is sigma-locally finite with respect to
     topology ` J ` if ` A ` can be written as a countable union of locally
     finite families.  (Contributed by Claude, 5-Feb-2026.) $)
  df-clocfin $a |- CntLocFin = ( x e. Top |->
    { y | E. f ( f : NN --> ( LocFin ` x ) /\ y = U. ran f ) } ) $.

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
    $d s y z J $.
    $( Lemma 41.3 of Munkres p. 252 (direction (1) implies (4)):  If ` J `
       is a regular topology and every open covering of ` J ` has a
       sigma-locally finite open refinement, then ` J ` is paracompact.
       This is the key step in Michael's theorem.
       (Contributed by Claude, 5-Feb-2026.) $)
    regpcmp $p |- ( ( J e. Reg /\
      A. y e. ~P J ( U. J = U. y ->
        E. s e. ( ( CntLocFin ` J ) i^i ~P J ) s Ref y ) ) ->
      J e. ParaCmp ) $=
      ? $.
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
    $d s y J $.
    $( Every open covering of a paracompact topology has a locally finite
       open refinement.  This is the forward direction of the
       characterization in ~ ispcmp .
       (Contributed by Claude, 5-Feb-2026.) $)
    pcmpcov $p |- ( ( J e. ParaCmp /\ y C_ J /\ U. J = U. y ) ->
      E. s e. ( ( LocFin ` J ) i^i ~P J ) s Ref y ) $=
      ? ? ? ? ? mpd $.
  $}

  ${
    $d s y D $.  $d s y J $.  $d s y X $.
    metpcmplem1.1 $e |- J = ( MetOpen ` D ) $.
    $( Lemma for ~ metpcmp .  For a metrizable space, any open covering has
       a locally finite open refinement.  Proved by combining
       ~ metpcmplem1d (metrizable implies paracompact) with ~ pcmpcov
       (extracting single-cover result).
       (Contributed by Claude, 5-Feb-2026.) $)
    metpcmplem1 $p |- ( ( D e. ( *Met ` X ) /\ y C_ J /\ X = U. y ) ->
      E. s e. ( ( LocFin ` J ) i^i ~P J ) s Ref y ) $=
      ? $.
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

