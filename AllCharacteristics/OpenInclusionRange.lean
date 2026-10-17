import Mathlib.AlgebraicGeometry.Restrict

/-! # Pointwise ranges of the actual open-subscheme inclusions -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- Membership in the image of an actual open inclusion is membership of the
underlying point in the smaller open. -/
theorem mem_range_homOfLE_iff {X : Scheme.{u}} {U V : X.Opens}
    (hUV : U ≤ V) (x : V.toScheme) :
    x ∈ Set.range (X.homOfLE hUV) ↔ x.val ∈ U := by
  constructor
  · rintro ⟨y, rfl⟩
    have he : (X.homOfLE hUV y).val = y.val := Scheme.homOfLE_apply hUV y
    exact Eq.mpr (congrArg (fun z : X ↦ z ∈ U) he) y.property
  · intro hx
    refine ⟨⟨x.val, hx⟩, ?_⟩
    apply Subtype.ext
    exact Scheme.homOfLE_apply hUV _

end AllCharacteristics
