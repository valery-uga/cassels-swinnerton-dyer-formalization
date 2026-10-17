import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualProjectiveLineParameter
import Mathlib.RingTheory.Localization.Ideal

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_principalIdealRing_localization
    {R A : Type*} [CommRing R] [IsPrincipalIdealRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A] : IsPrincipalIdealRing A := by
  constructor
  intro I
  obtain ⟨t, ht⟩ := (inferInstance : (I.under R).IsPrincipal)
  have he : Ideal.map (algebraMap R A) (I.under R) = I := IsLocalization.map_under M A I
  rw [ht, Ideal.map_span, Set.image_singleton] at he
  exact ⟨algebraMap R A t, he.symm⟩

instance cubicClosedPointSerreFiniteZeroResidual_projectiveLine_chart_localization_principal
    (K : Type u) [Field K] (b : (lineProjOpenCover K).I₀)
    (r : Γ((lineProjOpenCover K).X b, ⊤)) :
    IsPrincipalIdealRing (Localization.Away r) :=
  cubicClosedPointSerreFiniteZeroResidual_principalIdealRing_localization (Submonoid.powers r)

end PfaffianDescent
