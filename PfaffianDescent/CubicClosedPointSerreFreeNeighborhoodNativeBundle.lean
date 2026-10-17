import PfaffianDescent.SerreConnectingProductNonzero

/-! Opaque existence of the native rank-two Serre bundle and its cover,
retaining the exact original extension sequence. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFreeNeighborhood_native_exists_bundle_cover
    (F : Type u) [Field F]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i]
    (e₀ : SerreExtensionSequenceData (hypersurface P hP)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal P hP)) 3)))
    (hne :
      letI : HasExt.{u} (hypersurface P hP).Modules := schemeModules_hasExt _
      letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal P hP) 3
      letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal P hP) 3
      SerreConnectingProductNonzero i
        (positiveSheafOfModules (grading (equationIdeal P hP)) 3) e₀) :
    ∃ (e : SerreExtensionData (hypersurface P hP)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal P hP)) 3)))
      (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e),
      e.toSequenceData = e₀ := by
  exact ⟨cubicClosedPointSerreFreeNeighborhood_native_serreData F P hP hP0 i e₀ hne,
    cubicClosedPointSerreFreeNeighborhood_native_rankTwoAffineCover F P hP hP0 i e₀ hne,
    cubicClosedPointSerreFreeNeighborhood_native_serreData_toSequenceData F P hP hP0 i e₀ hne⟩

end PfaffianDescent.ProjectiveNegativeTwist
