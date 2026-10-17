import AllCharacteristics.OriginalGlobalHilbertChapterFiveIntegration
import AllCharacteristics.ManuscriptVerification.Audit
set_option pp.deepTerms true in
#check @AllCharacteristics.chapterFiveLiftFor_viaGlobalHilbert001
#print axioms AllCharacteristics.chapterFiveLiftFor_viaGlobalHilbert001
set_option pp.deepTerms true in
#check @AllCharacteristics.chapterFiveLiftStatement_viaGlobalHilbert001
#print axioms AllCharacteristics.chapterFiveLiftStatement_viaGlobalHilbert001
set_option pp.deepTerms true in
#check @AllCharacteristics.twoProofs_chapterFive_smooth_by_selected_closedPoint_viaGlobalHilbert_internalCoray001
#print axioms AllCharacteristics.twoProofs_chapterFive_smooth_by_selected_closedPoint_viaGlobalHilbert_internalCoray001
open Lean Elab Command

private def forbiddenChapterThreeResults : Array Name := #[
  `AllCharacteristics.twoProofs_degree_five_has_point,
  `AllCharacteristics.twoProofs_pfaffian_cubic_has_point,
  `AllCharacteristics.twoProofs_incidence_finite_etale_degree_two_open,
  `AllCharacteristics.twoProofs_reduced_length_five_subscheme_pfaffian,
  `AllCharacteristics.twoProofs_non_coplanar_quintic_has_point,
  `AllCharacteristics.twoProofs_non_coplanar_quintic_has_point_of_not_ground_plane,
  `PfaffianDescent.projective_pfaffian_to_point,
  `PfaffianDescent.reduced_length_five_subscheme_pfaffian,
  `PfaffianDescent.incidence_finite_etale_degree_two_open,
  `PfaffianDescent.quintic_geometric_pfaffian_presentation,
  `PfaffianDescent.pfaffian_to_point,
  `PfaffianDescent.cubic_degree_five_descent,
  `PfaffianDescent.cubic_descent_of_quintic_surjective,
  `PfaffianDescent.cubic_descent_of_independent_quintic_point,
  `PfaffianDescent.canonical_quintic_tensor_descent,
  `PfaffianDescent.projective_cubic_degree_five_descent,
  `PfaffianDescent.projective_cubic_effective_degree_five_to_point]


private def forbiddenEarlierFamilyRoutes : Array Name := #[
  `AllCharacteristics.lift_smooth_finite_closed_point,
  `AllCharacteristics.exists_finite_flat_closed_subscheme_of_smooth_finite_point,
  `AllCharacteristics.exists_finite_flat_subscheme_of_reduced_closedPoint,
  `AllCharacteristics.exists_smooth_lift_with_closed_subscheme,
  `AllCharacteristics.exists_prime_uniformizer_smooth_cubic_lift_with_original_closed_subscheme,
  `AllCharacteristics.twoProofs_chapterFive_lift_of_completeCharZeroDVR,
  `AllCharacteristics.twoProofs_chapterFive_lift,
  `AllCharacteristics.chapterFiveLiftFor_of_completeCharZeroDVR,
  `AllCharacteristics.exists_smooth_lift_with_closed_subscheme_viaLocalHilbert317,
  `AllCharacteristics.exists_prime_uniformizer_smooth_cubic_lift_with_original_closed_subscheme_viaLocalHilbert317,
  `AllCharacteristics.exists_smooth_charZero_cubic_lift_with_original_closed_subscheme_viaLocalHilbert317,
  `PfaffianDescent.originalClosedPoint_hilbertProjectiveLift_completeAlgebra317,
  `PfaffianDescent.originalClosedPoint_hilbertProjectiveLift317,
  `PfaffianDescent.originalClosedPoint_hilbertFiniteFlatClosedSubscheme317,
  `PfaffianDescent.originalHilbertCoefficientSmoothPoint_projectiveLift317
]

private def packetRoots : Array Name := #[
  `AllCharacteristics.chapterFiveLiftFor_viaGlobalHilbert001,
  `AllCharacteristics.chapterFiveLiftStatement_viaGlobalHilbert001,
  `AllCharacteristics.twoProofs_chapterFive_smooth_by_selected_closedPoint_viaGlobalHilbert_internalCoray001
]

private def actualKernelDependencies (ci : ConstantInfo) : Array Name :=
  ci.getUsedConstantsAsSet.toArray

private def inspectPacket (env : Environment) : IO Unit := do
  let standard : NameHashSet := #[`propext, `Classical.choice, `Quot.sound].foldl (fun s n => s.insert n) {}
  let forbidden : NameHashSet := forbiddenChapterThreeResults.foldl (fun s n => s.insert n) {}
  let legacy : NameHashSet := forbiddenEarlierFamilyRoutes.foldl (fun s n => s.insert n) {}
  for n in packetRoots do
    if (env.checked.get.find? n).isNone then
      throw (IO.userError s!"Missing audit declaration: {n}")
  let mut cache : NameMap (Array Name) := {}
  for root in packetRoots do
    let mut queue := #[root]
    let mut next := 0
    let mut seen : NameHashSet := ({} : NameHashSet).insert root
    let mut parent : NameMap Name := {}
    let mut hits : Array Name := #[]
    let mut oldFamily : Array Name := #[]
    let mut missing : Array Name := #[]
    let mut nonstandard : Array Name := #[]
    let mut axioms : NameHashSet := {}
    while next < queue.size do
      let n := queue[next]!
      next := next + 1
      if forbidden.contains n then hits := hits.push n
      if legacy.contains n then oldFamily := oldFamily.push n
      match env.checked.get.find? n with
      | some (.axiomInfo _) =>
        axioms := axioms.insert n
        if !standard.contains n then nonstandard := nonstandard.push n
      | _ => pure ()
      let ds ← match cache.find? n with
        | some ds => pure ds
        | none =>
          match env.checked.get.find? n with
          | none =>
            missing := missing.push n
            pure #[]
          | some ci =>
            let ds := actualKernelDependencies ci
            cache := cache.insert n ds
            pure ds
      for d in ds do
        if !seen.contains d then
          seen := seen.insert d
          parent := parent.insert d n
          queue := queue.push d
    let terminal := root == `AllCharacteristics.twoProofs_chapterFive_smooth_by_selected_closedPoint_viaGlobalHilbert_internalCoray001
    IO.println s!"SCOPE {root}: {if terminal then "TERMINAL_MANUSCRIPT_FULL17_REPORT" else "STRICT_ZERO17_GLOBAL_HILBERT_LIFT"}"
    IO.println s!"ROOT {root}: SCOPED TYPE+VALUE17 constants={queue.size}, forbidden={hits.size}, earlier_family_hits={oldFamily.size}, missing={missing.size}, nonstandard_axioms={nonstandard.size}, axioms={axioms.toArray}"
    for hit in hits ++ oldFamily do
      let mut path := #[hit]
      let mut current := hit
      while current != root do
        match parent.find? current with
        | none => throw (IO.userError "Broken dependency path")
        | some p =>
          path := path.push p
          current := p
      IO.println ("PATH " ++ String.intercalate " -> " (path.toList.reverse.map toString))
    if !terminal && !hits.isEmpty then
      throw (IO.userError s!"SCOPED strict-zero17 global Hilbert lifting dependence: {root}")
    if !oldFamily.isEmpty then
      throw (IO.userError s!"Forbidden earlier/local family lifting route: {root}")
    if !nonstandard.isEmpty then
      throw (IO.userError s!"Nonstandard axioms for {root}: {nonstandard}")
    if !missing.isEmpty then
      throw (IO.userError s!"Incomplete closure for {root}: {missing}")
    for required in #[`PfaffianDescent.originalClosedPoint_globalHilbertFiniteFlatClosedSubscheme001,
        `PfaffianDescent.relativeOpenChartParameterGlobalUniversalFamilyPullback001] do
      if !seen.contains required then
        throw (IO.userError s!"Missing genuine GLOBAL universal-family producer dependency for {root}: {required}")
    IO.println s!"GLOBAL FAMILY ROUTE VERIFIED {root}: actualGroundProducer + literal197GlobalUniversalPullback"
  IO.println s!"AUDIT COMPLETE: {packetRoots.size} original global-Hilbert outer/ChapterFive roots"

run_cmd do
  let env ← getEnv
  liftIO (inspectPacket (env.setExporting false))
