import PfaffianDescent.IntrinsicFullQuadraticSystem
import PfaffianDescent.HomogeneousProjectiveKernelSaturation
import PfaffianDescent.HomogeneousIdealPieces

/-! The full, nilpotent-sensitive quadratic space of a projective quotient.
The absence of an irrelevant annihilator identifies actual chart vanishing
with membership of the homogeneous ideal, rather than its radical. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem quotientProjMap_mem_intrinsicQuadraticChartIdeal
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (p : MvPolynomial (Fin 4) K) (hp : p ∈ I.toIdeal) :
    p ∈ intrinsicQuadraticChartIdeal (quotientProjMap I) j := by
  let U := intrinsicQuadraticAmbientOpen (K := K) j
  let evS := Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)
  let a := ambientChartEvaluation j p
  have ha : a ∈ RingHom.ker (quotientAmbientChartMap I j) := by
    rw [quotientAmbientChartMap_ker_eq_ideal_image]
    exact Ideal.mem_map_of_mem (ambientChartEvaluation j) hp
  change evS a ∈ (quotientProjMap I).ker.ideal U
  rw [(quotientProjMap I).ker_apply U]
  change (quotientProjMap I).app U (evS a) = 0
  have he := congrArg (fun g => g a)
    (Proj.awayToSection_comp_appLE (quotientGradedRingHom I)
      (irrelevant_le_map_quotientGradedRingHom I) (isHomogeneous_X K j))
  change (quotientProjMap I).app U (evS a) =
    Proj.awayToSection (grading I) (coordinate I j)
      (quotientAmbientChartMap I j a) at he
  rw [he, show quotientAmbientChartMap I j a = 0 from ha, map_zero]

set_option backward.isDefEq.respectTransparency false in
theorem intrinsicFullQuadraticSystem_eq_ideal_piece
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hsocle : ∀ x : CoordinateRing I,
      (∀ j : Fin 4, coordinate I j * x = 0) → x = 0) :
    intrinsicFullQuadraticSystem (quotientProjMap I) =
      (homogeneousIdealPiece I 2).map (homogeneousSubmodule (Fin 4) K 2).subtype := by
  ext p
  constructor
  · intro hp
    have hI : p ∈ I.toIdeal := by
      apply homogeneous_mem_of_hypersurface_ker_le_of_no_irrelevant_annihilator
        I p hp.1 _ hsocle
      apply quotientProjMap_ker_le_of_intrinsic_chart_ideal (equationIdeal p hp.1)
      intro j
      apply Ideal.span_le.mpr
      intro q hq
      obtain rfl := Set.mem_singleton_iff.mp hq
      exact ((Submodule.mem_iInf _).mp hp.2) j
    exact ⟨⟨p, hp.1⟩, hI, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.property, ?_⟩
    apply (Submodule.mem_iInf _).mpr
    intro j
    exact quotientProjMap_mem_intrinsicQuadraticChartIdeal I j p.val hp

set_option backward.isDefEq.respectTransparency false in
theorem intrinsicFullQuadraticSystem_comp_isIso
    {Z Y : Scheme.{u}} (l : Z ⟶ Y) [IsIso l]
    (i : Y ⟶ Proj (homogeneousSubmodule (Fin 4) K)) :
    intrinsicFullQuadraticSystem (l ≫ i) = intrinsicFullQuadraticSystem i := by
  unfold intrinsicFullQuadraticSystem intrinsicQuadraticChartIdeal
  rw [Scheme.Hom.ker_comp_of_isIso l i]

end PfaffianDescent
