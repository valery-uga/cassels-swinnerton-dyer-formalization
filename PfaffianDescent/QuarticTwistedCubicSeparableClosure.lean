import PfaffianDescent.QuarticTwistedCubicGaloisExtensionDescent
import PfaffianDescent.QuarticTwistedCubicProjectiveLine
import PfaffianDescent.ProjectiveLinearCoordinateSchemeIso

/-!
# Twisted cubics split over the separable closure

This is the scheme-level endpoint of coordinate descent over a separable
closure.  Unlike the algebraic-closure formulation, it has no perfectness or
characteristic assumption on the ground field.
-/

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u

variable {K : Type u} [Field K]

/-- A homogeneous three-quadric curve whose coordinate presentation becomes
the standard twisted cubic over the separable closure is already linearly
standard over the ground field. -/
noncomputable def separableClosure_twistedCubic_scheme_iso_standard
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (M : GL (Fin 4) (SeparableClosure K))
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map
      (algebraMap K (SeparableClosure K)) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K))).toRingHom =
        standardTwistedCubicIdeal (SeparableClosure K)) :
    scheme
      (⟨Ideal.span (Set.range Q), Ideal.homogeneous_span _ _ (by
        intro q hq
        obtain ⟨i, rfl⟩ := hq
        exact ⟨2, hQ i⟩)⟩ :
          HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) ≅
      scheme (standardTwistedCubicHomogeneousIdeal (K := K)) := by
  let Y := Classical.choose (separableClosure_standardPresentation_descends Q M hM)
  have hY : (Ideal.span (Set.range Q)).map
      (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K :=
    Classical.choose_spec (separableClosure_standardPresentation_descends Q M hM)
  let I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    ⟨Ideal.span (Set.range Q), Ideal.homogeneous_span _ _ (by
      intro q hq
      obtain ⟨i, rfl⟩ := hq
      exact ⟨2, hQ i⟩)⟩
  have hYdet : IsUnit ((Y : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit Y)
  have hIJ : (standardTwistedCubicHomogeneousIdeal (K := K)).toIdeal =
      I.toIdeal.map (linearSubstitutionEquiv (Y : Matrix (Fin 4) (Fin 4) K) hYdet).toRingHom := by
    have hE : (linearSubstitutionEquiv (Y : Matrix (Fin 4) (Fin 4) K) hYdet).toRingEquiv.toRingHom =
        (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom := rfl
    change standardTwistedCubicIdeal K = (Ideal.span (Set.range Q)).map
      (linearSubstitutionEquiv (Y : Matrix (Fin 4) (Fin 4) K) hYdet).toRingHom
    rw [hE]
    exact hY.symm
  exact linearCoordinateChangeSchemeIso (Y : Matrix (Fin 4) (Fin 4) K) hYdet I
    (standardTwistedCubicHomogeneousIdeal (K := K)) hIJ

/-- A homogeneous three-quadric curve whose coordinate presentation becomes
the standard twisted cubic over the separable closure is the ground projective
line. -/
noncomputable def separableClosure_twistedCubic_scheme_iso_projectiveLine
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (M : GL (Fin 4) (SeparableClosure K))
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map
      (algebraMap K (SeparableClosure K)) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K))).toRingHom =
        standardTwistedCubicIdeal (SeparableClosure K)) :
    scheme
      (⟨Ideal.span (Set.range Q), Ideal.homogeneous_span _ _ (by
        intro q hq
        obtain ⟨i, rfl⟩ := hq
        exact ⟨2, hQ i⟩)⟩ :
          HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) ≅
      projectiveLineProj K :=
  separableClosure_twistedCubic_scheme_iso_standard Q hQ M hM ≪≫
    standardTwistedCubicProjectiveLineProjIso (K := K)

end PfaffianDescent.QuarticNet
