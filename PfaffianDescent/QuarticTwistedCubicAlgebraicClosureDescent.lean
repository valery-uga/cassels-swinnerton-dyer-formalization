import PfaffianDescent.QuarticTwistedCubicStabilizerCocycle
import PfaffianDescent.QuarticTwistedCubicFiniteGaloisCoordinates
import PfaffianDescent.QuarticTwistedCubicIdealDescent
import PfaffianDescent.PolynomialCoefficientFaithfullyFlat
import PfaffianDescent.ProjectiveLinearCoordinateSchemeIso
import PfaffianDescent.QuarticTwistedCubicProjectiveLine

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory ProjectiveCocycle
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u

variable {K : Type u} [Field K] [PerfectField K]

/-- A coordinate presentation over the algebraic closure already descends to
an actual ground-field coordinate presentation over a perfect field. -/
theorem algebraicClosure_standardPresentation_descends
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (M : GL (Fin 4) (AlgebraicClosure K))
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map
      (algebraMap K (AlgebraicClosure K)) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K))).toRingHom =
        standardTwistedCubicIdeal (AlgebraicClosure K)) :
    ∃ Y : GL (Fin 4) K,
      (Ideal.span (Set.range Q)).map
        (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom =
          standardTwistedCubicIdeal K := by
  let L := finiteGaloisMatrixField (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K))
  let Y : GL (Fin 4) L := finiteGaloisGLLift M
  let I : Ideal (MvPolynomial (Fin 4) L) :=
    Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K L) (Q i)))
  have hGL : Matrix.GeneralLinearGroup.map
      (algebraMap L (AlgebraicClosure K)) Y = M := by
    dsimp [Y, L]
    exact finiteGaloisGLLift_map M
  have hYM : ((Y : Matrix (Fin 4) (Fin 4) L).map
      (algebraMap L (AlgebraicClosure K))) =
      (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K)) := by
    change ((Matrix.GeneralLinearGroup.map
      (algebraMap L (AlgebraicClosure K)) Y : GL (Fin 4) (AlgebraicClosure K)) :
        Matrix (Fin 4) (Fin 4) (AlgebraicClosure K)) = _
    rw [hGL]
  have hImap : I.map (MvPolynomial.map (algebraMap L (AlgebraicClosure K))) =
      Ideal.span (Set.range (fun i => MvPolynomial.map
        (algebraMap K (AlgebraicClosure K)) (Q i))) := by
    dsimp [I]
    rw [Ideal.map_span]
    congr 1
    ext p
    constructor
    · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      simp only [MvPolynomial.map_map]
      rw [IsScalarTower.algebraMap_eq K L (AlgebraicClosure K)]
    · rintro ⟨i, rfl⟩
      refine ⟨MvPolynomial.map (algebraMap K L) (Q i), ⟨i, rfl⟩, ?_⟩
      simp only [MvPolynomial.map_map]
      rw [IsScalarTower.algebraMap_eq K L (AlgebraicClosure K)]
  have hmap :
      (I.map (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) L)).toRingHom).map
        (MvPolynomial.map (algebraMap L (AlgebraicClosure K))) =
      (standardTwistedCubicIdeal L).map
        (MvPolynomial.map (algebraMap L (AlgebraicClosure K))) := by
    calc
      (I.map (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) L)).toRingHom).map
          (MvPolynomial.map (algebraMap L (AlgebraicClosure K))) =
        (I.map (MvPolynomial.map (algebraMap L (AlgebraicClosure K)))).map
          (linearSubstitution ((Y : Matrix (Fin 4) (Fin 4) L).map
            (algebraMap L (AlgebraicClosure K)))).toRingHom :=
          ideal_map_linearSubstitution_map (algebraMap L (AlgebraicClosure K)) I
            (Y : Matrix (Fin 4) (Fin 4) L)
      _ = (Ideal.span (Set.range (fun i => MvPolynomial.map
          (algebraMap K (AlgebraicClosure K)) (Q i)))).map
          (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K))).toRingHom := by
          rw [hImap, hYM]
      _ = standardTwistedCubicIdeal (AlgebraicClosure K) := hM
      _ = (standardTwistedCubicIdeal L).map
          (MvPolynomial.map (algebraMap L (AlgebraicClosure K))) :=
          (standardTwistedCubicIdeal_map_coefficientExtension (k := L)
            (L := AlgebraicClosure K)).symm
  letI : Module.FaithfullyFlat (MvPolynomial (Fin 4) L)
      (MvPolynomial (Fin 4) (AlgebraicClosure K)) :=
    mvPolynomial_coefficientExtension_faithfullyFlat
  have hYL : I.map
      (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L := by
    exact (Ideal.map_injective_of_faithfullyFlat
      (A := MvPolynomial (Fin 4) L)
      (B := MvPolynomial (Fin 4) (AlgebraicClosure K))) hmap
  simpa [I] using
    (finiteGalois_twistedCubic_ideal_descends_of_geometric_standardPresentation
      K L Q Y hYL)

/-- The descended three-quadric presentation is an actual projective scheme
isomorphic to the standard twisted cubic. -/
noncomputable def algebraicClosure_twistedCubic_scheme_iso_standard
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (M : GL (Fin 4) (AlgebraicClosure K))
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map
      (algebraMap K (AlgebraicClosure K)) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K))).toRingHom =
        standardTwistedCubicIdeal (AlgebraicClosure K)) :
    scheme
      (⟨Ideal.span (Set.range Q), Ideal.homogeneous_span _ _ (by
        intro q hq
        obtain ⟨i, rfl⟩ := hq
        exact ⟨2, hQ i⟩)⟩ :
        HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) ≅
      scheme (standardTwistedCubicHomogeneousIdeal (K := K)) := by
  let Y := Classical.choose (algebraicClosure_standardPresentation_descends Q M hM)
  have hY : (Ideal.span (Set.range Q)).map
      (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K :=
    Classical.choose_spec (algebraicClosure_standardPresentation_descends Q M hM)
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

/-- A three-quadric curve with a standard twisted-cubic presentation over the
algebraic closure is actually the projective line over the ground field. -/
noncomputable def algebraicClosure_twistedCubic_scheme_iso_projectiveLine
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (M : GL (Fin 4) (AlgebraicClosure K))
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map
      (algebraMap K (AlgebraicClosure K)) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K))).toRingHom =
        standardTwistedCubicIdeal (AlgebraicClosure K)) :
    scheme
      (⟨Ideal.span (Set.range Q), Ideal.homogeneous_span _ _ (by
        intro q hq
        obtain ⟨i, rfl⟩ := hq
        exact ⟨2, hQ i⟩)⟩ :
          HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) ≅
      projectiveLineProj K :=
  algebraicClosure_twistedCubic_scheme_iso_standard Q hQ M hM ≪≫
    standardTwistedCubicProjectiveLineProjIso (K := K)

/-- A homogeneous three-quadric curve with a standard twisted-cubic
presentation over the algebraic closure has a ground-field rational section
over a perfect field. -/
theorem algebraicClosure_twistedCubic_has_rational_section
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (M : GL (Fin 4) (AlgebraicClosure K))
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map
      (algebraMap K (AlgebraicClosure K)) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K))).toRingHom =
        standardTwistedCubicIdeal (AlgebraicClosure K)) :
    ∃ s : Spec (.of K) ⟶ scheme
      (⟨Ideal.span (Set.range Q), Ideal.homogeneous_span _ _ (by
        intro q hq
        obtain ⟨i, rfl⟩ := hq
        exact ⟨2, hQ i⟩)⟩ :
        HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)),
      s ≫ toBase _ = 𝟙 _ := by
  obtain ⟨Y, hY⟩ := algebraicClosure_standardPresentation_descends Q M hM
  let I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    ⟨Ideal.span (Set.range Q), Ideal.homogeneous_span _ _ (by
      intro q hq
      obtain ⟨i, rfl⟩ := hq
      exact ⟨2, hQ i⟩)⟩
  have hYdet : IsUnit ((Y : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit Y)
  have hI : I.toIdeal.map
      (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K := by
    change (Ideal.span (Set.range Q)).map
      (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K
    exact hY
  exact splitTwistedCubic_has_rational_section I
    (Y : Matrix (Fin 4) (Fin 4) K) hYdet hI

end PfaffianDescent.QuarticNet
