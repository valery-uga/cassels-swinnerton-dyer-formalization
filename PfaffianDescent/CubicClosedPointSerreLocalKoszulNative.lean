import PfaffianDescent.CubicClosedPointSerreLocalKoszulTwist
import PfaffianDescent.CubicClosedPointSerreLocalFreeCoordinate

/-! # Constructed affine Koszul charts for the actual positive-three ideal

Smooth cubic geometry supplies all parameter and trivialization data. The
source short exact sequence is constructed by the preceding actual-kernel
comparison; no sequence-identification hypothesis is supplied.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors
universe u

structure CubicClosedPointSerreLocalKoszulChartData
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (T : X.Modules) where
  U : X.Opens
  affine : IsAffineOpen U
  mem : i default ∈ U
  q : Γ(X, U)
  f : Γ(X, U)
  twist : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
    SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
      (SheafOfModules.commRingSheafOver X.sheaf U))
  regular_first : X.presheaf.germ U (i default) mem q ∈ (X.presheaf.stalk (i default))⁰
  regular_second : Ideal.Quotient.mk
    (Ideal.span {X.presheaf.germ U (i default) mem q})
    (X.presheaf.germ U (i default) mem f) ∈
    ((X.presheaf.stalk (i default)) ⧸ Ideal.span {X.presheaf.germ U (i default) mem q})⁰
  span_maximal : Ideal.span ({X.presheaf.germ U (i default) mem q,
    X.presheaf.germ U (i default) mem f} : Set _) =
    IsLocalRing.maximalIdeal (X.presheaf.stalk (i default))
  span_away : ∀ (y : X) (hy : y ∈ U), y ≠ i default →
    Ideal.span ({X.presheaf.germ U y hy q, X.presheaf.germ U y hy f} : Set _) = ⊤
  sequence : CubicClosedPointSerreLocalKoszulData i T U q f twist

end PfaffianDescent

open AlgebraicGeometry CategoryTheory AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreLocalKoszulNative_exists_chart
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i] :
    Nonempty (CubicClosedPointSerreLocalKoszulChartData i
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3)) := by
  classical
  let X := hypersurface p hp
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (hypersurfaceToBase p hp)
  letI : IsRegularRing Γ(Spec (.of K), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  letI : IsRegularLocalRing (X.presheaf.stalk (i default)) :=
    AllCharacteristics.isRegularLocalRing_stalk_of_smooth_over_affine
      (hypersurfaceToBase p hp) (i default)
  have hclosed : IsClosed ({i default} : Set X) := by
    have hrange : Set.range i = {i default} := by
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨y, rfl⟩
        congr 1
        exact Subsingleton.elim _ _
      · rintro rfl
        exact ⟨default, rfl⟩
    rw [← hrange]
    exact i.isClosedEmbedding.isClosed_range
  let I := equationIdeal p hp
  have hcover : ∃ j : Fin 4, i default ∈ quotientCoordinateOpen I j := by
    have hx : i default ∈ (⨆ j : Fin 4, quotientCoordinateOpen I j) := by
      rw [quotientCoordinateOpen_iSup I]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨j, hj⟩ := hcover
  obtain ⟨U, hU, hx, q, f, hUV, hqreg, hfreg, hmax, haway⟩ :=
    exists_affine_point_koszul_parameters (i default)
      (ringKrullDim_stalk_projective_hypersurface_eq_two p hp hp0 (i default) hclosed)
      hclosed (quotientCoordinateOpen I j) hj
  let T : X.Modules := positiveSheafOfModules (grading I) 3
  let eT := overFunctorUnitIso_restrict T hUV
    (overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j)
      (quotientCoordinatePositiveTwistUnitIso_all I j 3))
  let s := Classical.choice (cubicClosedPointSerreLocalKoszul_exists_data
    i T U hx q f eT hqreg hfreg hmax haway)
  exact ⟨⟨U, hU, hx, q, f, eT, hqreg, hfreg, hmax, haway, s⟩⟩

end PfaffianDescent.ProjectiveNegativeTwist
