import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOpenMarkedFibreSeed
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFiniteSubopen
import Mathlib.AlgebraicGeometry.Morphisms.Separated

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_finiteFibre_threeMarkedSeed
    {Z Y : Scheme.{u}} [IsLocallyNoetherian Z]
    (g : Z ⟶ Y) [IsProper g] [LocallyOfFinitePresentation g]
    (j : Fin 3 → (Y ⟶ Z)) (hj : ∀ n, j n ≫ g = 𝟙 Y)
    (y : Y) (hy : IsClosed {y}) [Finite (g.fiber y)]
    (hf : ∀ z : g.fiber y, IsField ((g.fiber y).presheaf.stalk z)) :
    y ∈ cubicClosedPointSerreFiniteZeroResidual_threeMarkedSectionOpen g j := by
  have hfinite : (g ⁻¹' {y}).Finite := (g.fiberHomeo y).finite_iff.mp inferInstance
  have hgood := cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre g y hfinite
  obtain ⟨U, hU, hyU, hUG⟩ := exists_isAffineOpen_mem_and_subset hgood
  letI : IsAffine (U : Scheme) := hU
  let gU := g.resLE U (g ⁻¹ᵁ U) le_rfl
  letI : IsFinite gU := by
    dsimp [gU]
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact cubicClosedPointSerreFiniteZeroResidual_finite_subopen g U hUG
  have hsource : IsAffineOpen (g ⁻¹ᵁ U) := isAffine_of_isAffineHom gU
  let i0 := Y.fromSpecResidueField y
  letI : IsClosedImmersion i0 := isClosed_singleton_iff_isClosedImmersion.mp hy
  let i : Spec (Y.residueField y) ⟶ (U : Scheme) :=
    IsOpenImmersion.lift U.ι i0 (by
      dsimp [i0]
      rw [Scheme.range_fromSpecResidueField]
      intro z hz
      have he : z = y := hz
      subst z
      exact ⟨⟨y, hyU⟩, rfl⟩)
  have hi : i ≫ U.ι = i0 := IsOpenImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (i ≫ U.ι) := by rw [hi]; infer_instance
  letI : IsClosedImmersion i := IsClosedImmersion.of_comp i U.ι
  have hfields : ∀ z : (pullback g (i ≫ U.ι) : Scheme),
      IsField ((pullback g (i ≫ U.ι)).presheaf.stalk z) := by
    rw [hi]
    exact hf
  have hmarked := cubicClosedPointSerreFiniteZeroResidual_openThreeMarkedFibreSeed
    g j hj ⟨U, hU⟩ hsource i hfields (IsLocalRing.closedPoint (Y.residueField y))
  have hp : U.ι (i (IsLocalRing.closedPoint (Y.residueField y))) = y := by
    change (i ≫ U.ι) _ = y
    rw [hi]
    exact Y.fromSpecResidueField_apply y _
  exact hp ▸ hmarked

end PfaffianDescent
