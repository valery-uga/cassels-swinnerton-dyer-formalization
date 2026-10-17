import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualChartMarkedFieldSeed
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOpenMarkedSections
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Noetherian

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_openThreeMarkedSeed
    {K : Type u} [Field K] {Z Y : Scheme.{u}} [IsLocallyNoetherian Z]
    (g : Z ⟶ Y) [IsAffineHom g] [LocallyOfFinitePresentation g]
    (j : Fin 3 → (Y ⟶ Z)) (hj : ∀ n, j n ≫ g = 𝟙 Y)
    (U : Y.affineOpens) (i : Spec (.of K) ⟶ U) [IsClosedImmersion i]
    (hf : ∀ z : (pullback (g.resLE U.1 (g ⁻¹ᵁ U.1) le_rfl) i : Scheme),
      IsField ((pullback (g.resLE U.1 (g ⁻¹ᵁ U.1) le_rfl) i).presheaf.stalk z))
    (c : Spec (.of K)) :
    U.1.ι (i c) ∈ cubicClosedPointSerreFiniteZeroResidual_threeMarkedSectionOpen g j := by
  letI : IsAffine (g ⁻¹ᵁ U.1) := U.property.preimage g
  exact cubicClosedPointSerreFiniteZeroResidual_chartThreeMarkedSeed_of_field_stalks
    g j (g ⁻¹ᵁ U.1).ι U.1.ι (g.resLE U.1 (g ⁻¹ᵁ U.1) le_rfl)
    (fun n => cubicClosedPointSerreFiniteZeroResidual_openMarkedSection g (j n) (hj n) U.1)
    (fun n => cubicClosedPointSerreFiniteZeroResidual_openMarkedSection_section g (j n) (hj n) U.1)
    (Scheme.Hom.resLE_comp_ι g le_rfl).symm
    (fun n => cubicClosedPointSerreFiniteZeroResidual_openMarkedSection_comp_source g (j n) (hj n) U.1)
    i hf c

end PfaffianDescent
