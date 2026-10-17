import PfaffianDescent.ProjectiveClosedPointCoordinates
import PfaffianDescent.CorayNormalizedProjectiveJetTransport
import AllCharacteristics.ClosedPointAlgebra

/-!
# Original residue coordinates of actual projective closed points

The original ground polynomial evaluation is surjective at a genuine closed
field-valued point. Setting the anchor coordinate equal to one preserves that
surjectivity in the actual three-variable affine presentation. In particular,
the evaluation-surjectivity hypothesis of the ground jet construction can be
obtained from an actual closed immersion, rather than assumed as extra geometry.

This does not prove the integral-curve branch, a Jacobian pivot, or a genus
formula. Source draft: production and dependency audits are pending.
-/

noncomputable section
namespace PfaffianDescent.Coray

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual coordinate-one substitution commutes with the original ground
evaluation at a residue point. -/
theorem normalizedGroundAffine_eval_of_coordinate_one
    (anchor : Fin 4) (x : Fin 4 → M) (hx : x anchor = 1)
    (f : MvPolynomial (Fin 4) K) :
    (normalizedAffineEquation anchor f).eval₂ (algebraMap K M)
      (fun i => x (anchor.succAbove i)) = f.eval₂ (algebraMap K M) x := by
  rw [← MvPolynomial.eval_map, ← normalizedAffineEquation_coefficients_map]
  exact (AlgHom.congr_fun (normalizedAffineEquation_evaluation anchor x hx)
    (MvPolynomial.map (algebraMap K M) f)).trans (MvPolynomial.eval_map _ _ _)

/-- Surjective original projective-coordinate evaluation remains surjective
after genuine anchor-coordinate elimination. -/
theorem normalizedGroundAffine_eval_surjective
    (anchor : Fin 4) (x : Fin 4 → M) (hx : x anchor = 1)
    (heval : Function.Surjective (eval₂Hom (algebraMap K M) x)) :
    Function.Surjective (eval₂Hom (algebraMap K M)
      (fun i : Fin 3 => x (anchor.succAbove i))) := by
  intro a
  obtain ⟨f, hf⟩ := heval a
  exact ⟨normalizedAffineEquation anchor f,
    (normalizedGroundAffine_eval_of_coordinate_one anchor x hx f).trans hf⟩

/-- A literal closed point on the actual projective scheme supplies genuine
normalized ground affine coordinates generating its whole residue field. -/
theorem closedProjectivePoint_exists_groundAffine_residue_presentation
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (q : Spec (.of M) ⟶ scheme I) [IsClosedImmersion q]
    (hq : q ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K M))) :
    ∃ anchor : Fin 4, ∃ x : Fin 4 → M,
      x anchor = 1 ∧
      Function.Surjective (eval₂Hom (algebraMap K M)
        (fun i : Fin 3 => x (anchor.succAbove i))) ∧
      ∀ f ∈ I.toIdeal, (normalizedAffineEquation anchor f).eval₂
        (algebraMap K M) (fun i => x (anchor.succAbove i)) = 0 := by
  obtain ⟨anchor, x, hx, heval, hzero⟩ :=
    PfaffianDescent.closed_projective_point_generating_coordinates I q hq
  refine ⟨anchor, x, hx, normalizedGroundAffine_eval_surjective anchor x hx heval, ?_⟩
  intro f hf
  rw [normalizedGroundAffine_eval_of_coordinate_one anchor x hx f]
  exact hzero f hf

/-- An actual scheme-theoretic closed point supplies its finite residue
extension, its exact scheme residue degree, and generating affine coordinates.
All three facts are derived from the actual point and structure morphism. -/
theorem actualClosedPoint_exists_finite_groundAffine_residue_presentation
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (w : closedPoints (scheme I)) :
    letI := AllCharacteristics.pointAlgebra (toBase I) w.1
    Module.Finite K ((scheme I).residueField w.1) ∧
      Module.finrank K ((scheme I).residueField w.1) = (toBase I).residueDegree w.1 ∧
      ∃ anchor : Fin 4, ∃ x : Fin 4 → (scheme I).residueField w.1,
        x anchor = 1 ∧
        Function.Surjective (eval₂Hom (algebraMap K ((scheme I).residueField w.1))
          (fun i : Fin 3 => x (anchor.succAbove i))) ∧
        ∀ f ∈ I.toIdeal, (normalizedAffineEquation anchor f).eval₂
          (algebraMap K ((scheme I).residueField w.1))
          (fun i => x (anchor.succAbove i)) = 0 := by
  letI := AllCharacteristics.pointAlgebra (toBase I) w.1
  letI : IsClosedImmersion ((scheme I).fromSpecResidueField w.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp w.2
  refine ⟨AllCharacteristics.closedPoint_moduleFinite (toBase I) w,
    AllCharacteristics.closedPoint_finrank_eq_residueDegree (toBase I) w, ?_⟩
  exact closedProjectivePoint_exists_groundAffine_residue_presentation I
    ((scheme I).fromSpecResidueField w.1)
    (AllCharacteristics.pointAlgebra_spec (toBase I) w.1).symm

end PfaffianDescent.Coray
