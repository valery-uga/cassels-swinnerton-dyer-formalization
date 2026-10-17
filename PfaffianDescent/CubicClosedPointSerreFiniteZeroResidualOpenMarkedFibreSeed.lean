import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOpenMarkedSeed
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOpenFibreIso

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_openThreeMarkedFibreSeed
    {K : Type u} [Field K] {Z Y : Scheme.{u}} [IsLocallyNoetherian Z]
    (g : Z ⟶ Y) [LocallyOfFinitePresentation g]
    (j : Fin 3 → (Y ⟶ Z)) (hj : ∀ n, j n ≫ g = 𝟙 Y)
    (U : Y.affineOpens) (hU : IsAffineOpen (g ⁻¹ᵁ U.1))
    (i : Spec (.of K) ⟶ U) [IsClosedImmersion i]
    (hf : ∀ z : (pullback g (i ≫ U.1.ι) : Scheme),
      IsField ((pullback g (i ≫ U.1.ι)).presheaf.stalk z)) (c : Spec (.of K)) :
    U.1.ι (i c) ∈ cubicClosedPointSerreFiniteZeroResidual_threeMarkedSectionOpen g j := by
  letI : IsAffine (g ⁻¹ᵁ U.1) := hU
  exact cubicClosedPointSerreFiniteZeroResidual_chartThreeMarkedSeed_of_field_stalks
    g j (g ⁻¹ᵁ U.1).ι U.1.ι (g.resLE U.1 (g ⁻¹ᵁ U.1) le_rfl)
    (fun n => cubicClosedPointSerreFiniteZeroResidual_openMarkedSection g (j n) (hj n) U.1)
    (fun n => cubicClosedPointSerreFiniteZeroResidual_openMarkedSection_section g (j n) (hj n) U.1)
    (Scheme.Hom.resLE_comp_ι g le_rfl).symm
    (fun n => cubicClosedPointSerreFiniteZeroResidual_openMarkedSection_comp_source g (j n) (hj n) U.1)
    i (cubicClosedPointSerreFiniteZeroResidual_openFibre_stalks_isField g U.1 i hf) c

end PfaffianDescent
