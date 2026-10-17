import PfaffianDescent.PointCartierNativeStalkEquationCoordinates
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The actual surface stalk is the quotient by the native Cartier scalar -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  [IsDomain (CoordinateRing (equationIdeal p hp))]

theorem pointCartierNativeStalkRingMap_ker
    (j : Fin 4) (y : hypersurface p hp)
    (hx : X j ∉ (hypersurfaceAmbientPoint p hp y).asHomogeneousIdeal.toIdeal) :
    RingHom.ker ((hypersurfaceToAmbient p hp).stalkMap y).hom =
      Ideal.span ({pointCartierNativeStalkHypersurfaceScalar p hp j
        (hypersurfaceAmbientPoint p hp y) hx} :
          Set ((Proj PS).presheaf.stalk (hypersurfaceAmbientPoint p hp y))) := by
  let x := hypersurfaceAmbientPoint p hp y
  let I := equationIdeal p hp
  let ℬ := grading I
  let q := quotientGradedRingHom I
  let P := Proj.stalkIso' PS x
  let Q := Proj.stalkIso' ℬ y
  let t := pointCartierNativeStalkHypersurfaceScalar p hp j x hx
  let E := localEquation PS (pointIdeal PS x) (⟨p, hp⟩ : PS 3) (p3Coordinate K j) hx
  let L := localTrivialization PS (pointIdeal PS x) (p3Coordinate K j) hx 3
  let F := fun z : stalkSubmodule PS (pointIdeal PS x) 3 =>
    (atPrimeLinearEquivZeroTwistStalk PS (pointIdeal PS x)).symm
      (mulHomogeneousStalk PS (pointIdeal PS x) (⟨p, hp⟩ : PS 3) 0 z)
  let G := HomogeneousLocalization.localRingHom q
    (pointIdeal PS x) (pointIdeal ℬ y) rfl
  have hExact : Function.Exact F G := hypersurface_localRing_exact p hp y
  have hP : P t = E := pointCartierNativeStalkHypersurfaceScalar_coordinates p hp j x hx
  have hF (a : AtPrime PS (pointIdeal PS x)) : F (L a) = E * a := by
    dsimp only [F, L, E]
    rw [mulHomogeneousStalk_localTrivialization_apply]
    exact (congrArg (atPrimeLinearEquivZeroTwistStalk PS (pointIdeal PS x)).symm
      (ambientPointKoszul_localTrivialization_zero K j x hx _)).trans
        ((atPrimeLinearEquivZeroTwistStalk PS (pointIdeal PS x)).symm_apply_apply _)
  ext r
  change (hypersurfaceToAmbient p hp).stalkMap y r = 0 ↔ r ∈ Ideal.span ({t} : Set _)
  have hmap : Q.symm (G (P r)) = (hypersurfaceToAmbient p hp).stalkMap y r :=
    Proj.localRingHom_comp_stalkIso_apply q (irrelevant_le_map_quotientGradedRingHom I) y r
  have hz : (hypersurfaceToAmbient p hp).stalkMap y r = 0 ↔ G (P r) = 0 := by
    rw [← hmap]
    exact Q.symm.map_eq_zero_iff
  rw [hz, hExact]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := L.surjective z
    rw [hF] at hz
    apply Ideal.mem_span_singleton.mpr
    refine ⟨P.symm a, ?_⟩
    apply P.injective
    rw [map_mul, hP, P.apply_symm_apply]
    exact hz.symm
  · intro hr
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hr
    refine ⟨L (P a), ?_⟩
    rw [hF, ← hP, ← map_mul, ha]

/-- The canonical ring equivalence from the actual principal quotient to
the actual surface stalk; it is induced by the actual scheme stalk map. -/
def pointCartierNativeStalkSurfaceRingEquiv
    (j : Fin 4) (y : hypersurface p hp)
    (hx : X j ∉ (hypersurfaceAmbientPoint p hp y).asHomogeneousIdeal.toIdeal) :
    ((Proj PS).presheaf.stalk (hypersurfaceAmbientPoint p hp y) ⧸
      Ideal.span ({pointCartierNativeStalkHypersurfaceScalar p hp j
        (hypersurfaceAmbientPoint p hp y) hx} : Set _)) ≃+*
      (hypersurface p hp).presheaf.stalk y :=
  (Ideal.quotEquivOfEq (pointCartierNativeStalkRingMap_ker p hp j y hx).symm).trans
    (((hypersurfaceToAmbient p hp).stalkMap y).hom.quotientKerEquivOfSurjective
      ((hypersurfaceToAmbient p hp).stalkMap_surjective y))

@[simp]
theorem pointCartierNativeStalkSurfaceRingEquiv_mk
    (j : Fin 4) (y : hypersurface p hp)
    (hx : X j ∉ (hypersurfaceAmbientPoint p hp y).asHomogeneousIdeal.toIdeal)
    (r : (Proj PS).presheaf.stalk (hypersurfaceAmbientPoint p hp y)) :
    pointCartierNativeStalkSurfaceRingEquiv p hp j y hx
      (Ideal.Quotient.mk _ r) = (hypersurfaceToAmbient p hp).stalkMap y r := by
  simp only [pointCartierNativeStalkSurfaceRingEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ r

end PfaffianDescent.ProjectiveNegativeTwist
