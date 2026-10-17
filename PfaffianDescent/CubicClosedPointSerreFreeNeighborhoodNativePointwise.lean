import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodNativeAtPoint
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodNativeAway
import PfaffianDescent.CubicClosedDegreeElevenPointSerreExtension

/-! # Actual rank-two affine neighborhoods at every point of the cubic -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every point has a constructed actual affine rank-two trivialization.
Native Ext existence and local Ext existence are proved internally. -/
theorem cubicClosedPointSerreFreeNeighborhood_native_exists_pointwise
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (e : SerreExtensionSequenceData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (hne :
      letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
      letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
      letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e
          (schemeModules_hasExt _)) (show 1 + 1 = 2 by omega) ≠ 0) :
    ∀ (x : hypersurface p hp), ∃ (U : (hypersurface p hp).Opens),
      x ∈ U ∧ IsAffineOpen U ∧
        Nonempty (SheafOfModules.free (R := (hypersurface p hp).ringCatSheaf.over U)
          (ULift.{u} (Fin 2)) ≅ e.E.over U) := by
  classical
  letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
  letI : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default))) :=
    moduleCatStalk_hasExt _
  intro x
  by_cases hx : x = i default
  · subst x
    exact cubicClosedPointSerreFreeNeighborhood_native_exists_at_point K p hp hp0 i e hne
  · exact cubicClosedPointSerreFreeNeighborhood_native_exists_away K p hp i e x hx

end PfaffianDescent.ProjectiveNegativeTwist
