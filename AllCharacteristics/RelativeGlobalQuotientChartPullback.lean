import AllCharacteristics.RelativeCommonOpenGlobalQuotientMap
import AllCharacteristics.RelativeQuotientGluedIntersections

/-!
# Actual chart pullbacks of the global unordered-tuple quotient

Each original ordered common-affine-open chart is exactly the inverse image
of its glued invariant-spectrum chart. The resulting square is Cartesian,
so chartwise finiteness can be used for the actual global quotient morphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] (n : ℕ) [hSep : X.IsSeparated]

/-- The original ordered charts are open immersions in their actual glued locus. -/
instance isOpenImmersion_orderedCommonOpenGluedChart (U : X.affineOpens) :
    IsOpenImmersion (orderedCommonOpenGluedChart f n U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (orderedCommonOpenDiagram f n) U))

omit [IsAffine S] in
/-- Membership in an ordered chart of the glued locus means membership of
the original ordered-power point in the corresponding common open. -/
theorem mem_range_orderedCommonOpenGluedChart_iff (U : X.affineOpens)
    (x : orderedCommonOpenGlued f n) :
    x ∈ Set.range (orderedCommonOpenGluedChart f n U) ↔
      orderedCommonOpenGluedToPower f n x ∈ orderedFamilyCommonOpen f U.val n := by
  have he (p : (orderedFamilyCommonOpen f U.val n).toScheme) :
      orderedCommonOpenGluedToPower f n (orderedCommonOpenGluedChart f n U p) = p.val :=
    congrArg (fun m : (orderedFamilyCommonOpen f U.val n).toScheme ⟶
      (orderedFamilyPowerOver f n).left ↦ m p) (orderedCommonOpenGluedChart_toPower f n U)
  constructor
  · rintro ⟨p, rfl⟩
    exact Eq.mpr (congrArg (fun z : (orderedFamilyPowerOver f n).left ↦
      z ∈ orderedFamilyCommonOpen f U.val n) (he p)) p.property
  · intro hx
    refine ⟨⟨orderedCommonOpenGluedToPower f n x, hx⟩,
      orderedCommonOpenGluedToPower_injective f n ?_⟩
    exact he ⟨orderedCommonOpenGluedToPower f n x, hx⟩

/-- The full inverse image of an actual glued quotient chart is its original ordered chart. -/
theorem orderedCommonOpenGlobalQuotientMap_preimage_chart (U : X.affineOpens) :
    (orderedCommonOpenGlobalQuotientMap f n) ⁻¹'
      Set.range (commonOpenTupleQuotientGluedChart f n U) =
        Set.range (orderedCommonOpenGluedChart f n U) := by
  ext x
  constructor
  · intro hx
    obtain ⟨V, p, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (orderedCommonOpenDiagram f n) x
    obtain ⟨z, hz⟩ := hx
    have hm : orderedCommonOpenGlobalQuotientMap f n (colimit.ι (orderedCommonOpenDiagram f n) V p) =
        commonOpenTupleQuotientGluedChart f n V (commonOpenTupleQuotientMap f V.val n V.property p) :=
      congrArg (fun m : (orderedFamilyCommonOpen f V.val n).toScheme ⟶
        commonOpenTupleQuotientGlued f n ↦ m p) (orderedCommonOpenGlobalQuotientMap_chart f n V)
    obtain ⟨w, _, hw⟩ := (commonOpenTupleQuotientGluedChart_eq_iff f n U V z
      (commonOpenTupleQuotientMap f V.val n V.property p)).mp (hz.trans hm)
    have hI : IsAffineOpen (U.val ⊓ V.val) := U.property.inf V.property
    have hp : p ∈ Set.range ((orderedFamilyPowerOver f n).left.homOfLE
        (orderedFamilyCommonOpen_mono f n (show U.val ⊓ V.val ≤ V.val from inf_le_right))) :=
      (Set.ext_iff.mp (commonOpenTupleQuotientInclusion_preimage_range f
        (show U.val ⊓ V.val ≤ V.val from inf_le_right) n hI V.property) p).mp ⟨w, hw⟩
    have hpI := (mem_range_homOfLE_iff _ p).mp hp
    have hpU : p.val ∈ orderedFamilyCommonOpen f U.val n :=
      orderedFamilyCommonOpen_mono f n (show U.val ⊓ V.val ≤ U.val from inf_le_left) hpI
    apply (mem_range_orderedCommonOpenGluedChart_iff f n U _).mpr
    have he : orderedCommonOpenGluedToPower f n (colimit.ι (orderedCommonOpenDiagram f n) V p) = p.val :=
      congrArg (fun m : (orderedFamilyCommonOpen f V.val n).toScheme ⟶
        (orderedFamilyPowerOver f n).left ↦ m p) (orderedCommonOpenGluedChart_toPower f n V)
    exact Eq.mpr (congrArg (fun z : (orderedFamilyPowerOver f n).left ↦
      z ∈ orderedFamilyCommonOpen f U.val n) he) hpU
  · rintro ⟨p, rfl⟩
    refine ⟨commonOpenTupleQuotientMap f U.val n U.property p, ?_⟩
    exact (congrArg (fun m : (orderedFamilyCommonOpen f U.val n).toScheme ⟶
      commonOpenTupleQuotientGlued f n ↦ m p) (orderedCommonOpenGlobalQuotientMap_chart f n U)).symm

/-- Every original affine ordered chart is the actual base change of its
invariant-spectrum chart along the global quotient morphism. -/
theorem isPullback_orderedCommonOpenGlobalQuotientMap_chart (U : X.affineOpens) :
    IsPullback (orderedCommonOpenGluedChart f n U) (commonOpenTupleQuotientMap f U.val n U.property)
      (orderedCommonOpenGlobalQuotientMap f n) (commonOpenTupleQuotientGluedChart f n U) := by
  apply (IsOpenImmersion.isPullback (commonOpenTupleQuotientMap f U.val n U.property)
    (orderedCommonOpenGluedChart f n U) (commonOpenTupleQuotientGluedChart f n U)
    (orderedCommonOpenGlobalQuotientMap f n) (orderedCommonOpenGlobalQuotientMap_chart f n U) ?_).flip
  apply SetLike.coe_injective
  exact orderedCommonOpenGlobalQuotientMap_preimage_chart f n U

end AllCharacteristics
