import AllCharacteristics.RelativeCommonOpenQuotientGeometry
import AllCharacteristics.OpenInclusionRange
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Exact intersections of actual affine unordered-tuple quotient charts

Two quotient-chart points with the same image in a common chart lift to
one point of the quotient of their actual intersection. The proof uses the
Cartesian quotient squares and the proved intersection of ordered charts.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] (n : ℕ)

/-- Equal quotient points on two affine common-open charts come from their
actual intersection chart. -/
theorem exists_commonOpenTupleQuotient_intersection
    {U V W : X.Opens} (hUW : U ≤ W) (hVW : V ≤ W)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hUV : IsAffineOpen (U ⊓ V))
    (x : commonOpenTupleQuotient f U n) (y : commonOpenTupleQuotient f V n)
    (hxy : commonOpenTupleQuotientInclusion f hUW n x =
      commonOpenTupleQuotientInclusion f hVW n y) :
    ∃ z : commonOpenTupleQuotient f (U ⊓ V) n,
      commonOpenTupleQuotientInclusion f (show U ⊓ V ≤ U from inf_le_left) n z = x ∧
      commonOpenTupleQuotientInclusion f (show U ⊓ V ≤ V from inf_le_right) n z = y := by
  obtain ⟨p, hp⟩ := (commonOpenTupleQuotientMap f W n hW).surjective
    (commonOpenTupleQuotientInclusion f hUW n x)
  have hpU : p ∈ Set.range ((orderedFamilyPowerOver f n).left.homOfLE
      (orderedFamilyCommonOpen_mono f n hUW)) :=
    (Set.ext_iff.mp (commonOpenTupleQuotientInclusion_preimage_range f hUW n hU hW) p).mp
      ⟨x, hp.symm⟩
  have hpV : p ∈ Set.range ((orderedFamilyPowerOver f n).left.homOfLE
      (orderedFamilyCommonOpen_mono f n hVW)) :=
    (Set.ext_iff.mp (commonOpenTupleQuotientInclusion_preimage_range f hVW n hV hW) p).mp
      ⟨y, hxy.symm.trans hp.symm⟩
  have hpUV : p.val ∈ orderedFamilyCommonOpen f (U ⊓ V) n := by
    rw [orderedFamilyCommonOpen_inf]
    exact ⟨(mem_range_homOfLE_iff _ p).mp hpU, (mem_range_homOfLE_iff _ p).mp hpV⟩
  let pUV : (orderedFamilyCommonOpen f (U ⊓ V) n).toScheme := ⟨p.val, hpUV⟩
  let z := commonOpenTupleQuotientMap f (U ⊓ V) n hUV pUV
  have hz : commonOpenTupleQuotientInclusion f (inf_le_left.trans hUW) n z =
      commonOpenTupleQuotientMap f W n hW p := by
    have he := congrArg (fun m : (orderedFamilyCommonOpen f (U ⊓ V) n).toScheme ⟶
        commonOpenTupleQuotient f W n ↦ m pUV)
      (commonOpenTupleQuotientInclusion_square f (inf_le_left.trans hUW) n hUV hW)
    have hi : (orderedFamilyPowerOver f n).left.homOfLE
        (orderedFamilyCommonOpen_mono f n (inf_le_left.trans hUW)) pUV = p := by
      apply Subtype.ext
      exact Scheme.homOfLE_apply _ _
    exact he.trans (congrArg (commonOpenTupleQuotientMap f W n hW) hi)
  have hUi := isOpenImmersion_commonOpenTupleQuotientInclusion f hUW n hU hW
  have hVi := isOpenImmersion_commonOpenTupleQuotientInclusion f hVW n hV hW
  refine ⟨z, ?_, ?_⟩
  · apply (commonOpenTupleQuotientInclusion f hUW n).isOpenEmbedding.injective
    have he := congrArg (fun m : commonOpenTupleQuotient f (U ⊓ V) n ⟶
        commonOpenTupleQuotient f W n ↦ m z)
      (commonOpenTupleQuotientInclusion_comp f n inf_le_left hUW hUV hU hW)
    exact he.trans (hz.trans hp)
  · apply (commonOpenTupleQuotientInclusion f hVW n).isOpenEmbedding.injective
    have he := congrArg (fun m : commonOpenTupleQuotient f (U ⊓ V) n ⟶
        commonOpenTupleQuotient f W n ↦ m z)
      (commonOpenTupleQuotientInclusion_comp f n inf_le_right hVW hUV hV hW)
    exact he.trans (hz.trans (hp.trans hxy))

end AllCharacteristics
