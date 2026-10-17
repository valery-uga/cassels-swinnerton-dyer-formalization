import PfaffianDescent.CubicClosedPointSerreExtension
import PfaffianDescent.CubicClosedPointSerreLocalFree

/-! # An actual degree-eleven Serre extension with free original-point stalk

This joins the actual global Ext lift and sequence realization to the
proved local rank-two calculation. Freeness on a neighborhood is a further
geometric conclusion handled separately.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreLocalFree_exists_sequence
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (hL : Module.finrank K L = 11) :
    letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
    letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
    ∃ e : SerreExtensionSequenceData (hypersurface p hp)
        (closedImmersionIdealTwist i
          (positiveSheafOfModules (grading (equationIdeal p hp)) 3)),
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp)
          (closedImmersionIdealTwist i
            (positiveSheafOfModules (grading (equationIdeal p hp)) 3)) e hExt)
        (show 1 + 1 = 2 by omega) ≠ 0 ∧
      (letI : Module ((hypersurface p hp).presheaf.stalk (i default))
          ((show (hypersurface p hp).Modules from e.E).presheaf.stalk (i default)) :=
        schemeModuleStalkModule (show (hypersurface p hp).Modules from e.E) (i default)
      Nonempty (((show (hypersurface p hp).Modules from e.E).presheaf.stalk (i default)) ≃ₗ[
        (hypersurface p hp).presheaf.stalk (i default)]
        ((hypersurface p hp).presheaf.stalk (i default)) ×
          ((hypersurface p hp).presheaf.stalk (i default)))) := by
  letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
  letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
  obtain ⟨e, hconnecting⟩ :=
    cubicClosedPointSerreExtension_exists_sequence_of_smooth K p hp hp0 i hi hL
  exact ⟨e, hconnecting, cubicClosedPointSerreLocalFree_stalk_rank_two K p hp hp0 i e hconnecting⟩

end PfaffianDescent.ProjectiveNegativeTwist
