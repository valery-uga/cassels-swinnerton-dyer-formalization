import AllCharacteristics.ProperSmoothBase
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The proper smooth base under open base change

The smooth parameter open of a proper family commutes with restriction to an
open subscheme of its base. The proof compares stalk maps in the Cartesian
square and uses the surjectivity of the map to the topological fiber product.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {W X V Y : Scheme.{u}}
variable {i : W ⟶ X} {q : W ⟶ V} {f : X ⟶ Y} {j : V ⟶ Y}
variable (h : IsPullback i q f j) [IsOpenImmersion j]
variable [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation q]
include h

/-- An open change of base preserves and reflects membership in the smooth locus. -/
theorem mem_smoothLocus_iff_of_open_baseChange (x : W) :
    x ∈ q.smoothLocus ↔ i x ∈ f.smoothLocus :=
  (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (Scheme.stalkMapIsoOfIsPullback h x)).symm

/-- A point belongs to the proper smooth base after open base change exactly
when its image belongs to the original proper smooth base. -/
theorem mem_properSmoothBase_iff_of_open_baseChange
    [UniversallyClosed f] [UniversallyClosed q] (y : V) :
    y ∈ properSmoothBase q ↔ j y ∈ properSmoothBase f := by
  rw [mem_properSmoothBase_iff, mem_properSmoothBase_iff]
  constructor
  · intro hy x hx
    obtain ⟨w, hw, hq⟩ := Scheme.exists_preimage_of_isPullback h x y hx
    have hs := (mem_smoothLocus_iff_of_open_baseChange h w).mp (hy w hq)
    rwa [hw] at hs
  · intro hy w hw
    apply (mem_smoothLocus_iff_of_open_baseChange h w).mpr
    apply hy
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply, hw]

/-- The proper smooth parameter open commutes with open base change. -/
theorem properSmoothBase_preimage_of_open_baseChange
    [UniversallyClosed f] [UniversallyClosed q] :
    j ⁻¹ᵁ properSmoothBase f = properSmoothBase q := by
  ext y
  exact (mem_properSmoothBase_iff_of_open_baseChange h y).symm

end AllCharacteristics
