import PfaffianDescent.QuarticTwistedCubicSeparablePresentation
import PfaffianDescent.HomogeneousIdealPieceCoefficientBaseChange
import PfaffianDescent.QuarticTwistedCubicQuadraticCoordinateChange
import PfaffianDescent.ProjectiveCoefficientGradeBaseChange

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u
variable {K : Type u} [Field K]

theorem quadraticPiece_finrank_le_three_of_separableGeometricallyStandardTwistedCubic
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : SeparableGeometricallyStandardTwistedCubic I) :
    Module.finrank K (homogeneousIdealPiece I 2) ≤ 3 := by
  let J : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin 4) (SeparableClosure K)) :=
    HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom (algebraMap K (SeparableClosure K))) I
  have hJ : I.toIdeal.map (MvPolynomial.map (algebraMap K (SeparableClosure K))) =
      J.toIdeal := by
    change I.toIdeal.map (MvPolynomial.map (algebraMap K (SeparableClosure K))) =
      (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom (algebraMap K (SeparableClosure K))) I).toIdeal
    rw [HomogeneousIdeal.toIdeal_map]
    rfl
  let M : GL (Fin 4) (SeparableClosure K) := Classical.choose hgeo
  have hM : (I.toIdeal.map (MvPolynomial.map (algebraMap K (SeparableClosure K)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K))).toRingHom =
        standardTwistedCubicIdeal (SeparableClosure K) := Classical.choose_spec hgeo
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) (SeparableClosure K)).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have hMJ : (standardTwistedCubicHomogeneousIdeal (K := SeparableClosure K)).toIdeal =
      J.toIdeal.map
        (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K)) hdet).toRingHom := by
    change standardTwistedCubicIdeal (SeparableClosure K) = J.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K)) hdet).toRingHom
    rw [← hJ]
    exact hM.symm
  have hdimJ : Module.finrank (SeparableClosure K) (homogeneousIdealPiece J 2) = 3 :=
    (coordinateChange_standardTwistedCubic_quadraticPiece J
      (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K)) hdet hMJ).2
  calc
    Module.finrank K (homogeneousIdealPiece I 2) ≤
        Module.finrank (SeparableClosure K) (homogeneousIdealPiece J 2) :=
      homogeneousIdealPiece_finrank_le_coefficientExtension I J hJ 2
    _ = 3 := hdimJ

end PfaffianDescent.QuarticNet


namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u
variable {K : Type u} [Field K]

theorem quadraticPiece_finrank_eq_three_of_separableGeometricallyStandardTwistedCubic
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : SeparableGeometricallyStandardTwistedCubic I) :
    Module.finrank K (homogeneousIdealPiece I 2) = 3 := by
  let J : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin 4) (SeparableClosure K)) :=
    HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom (algebraMap K (SeparableClosure K))) I
  have hJ : I.toIdeal.map (MvPolynomial.map (algebraMap K (SeparableClosure K))) =
      J.toIdeal := by
    change I.toIdeal.map (MvPolynomial.map (algebraMap K (SeparableClosure K))) =
      (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom (algebraMap K (SeparableClosure K))) I).toIdeal
    rw [HomogeneousIdeal.toIdeal_map]
    rfl
  let M : GL (Fin 4) (SeparableClosure K) := Classical.choose hgeo
  have hM : (I.toIdeal.map (MvPolynomial.map (algebraMap K (SeparableClosure K)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K))).toRingHom =
        standardTwistedCubicIdeal (SeparableClosure K) := Classical.choose_spec hgeo
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) (SeparableClosure K)).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have hMJ : (standardTwistedCubicHomogeneousIdeal (K := SeparableClosure K)).toIdeal =
      J.toIdeal.map
        (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K)) hdet).toRingHom := by
    change standardTwistedCubicIdeal (SeparableClosure K) = J.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K)) hdet).toRingHom
    rw [← hJ]
    exact hM.symm
  have hdimJ : Module.finrank (SeparableClosure K) (homogeneousIdealPiece J 2) = 3 :=
    (coordinateChange_standardTwistedCubic_quadraticPiece J
      (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K)) hdet hMJ).2
  have hquadricJ : Module.finrank (SeparableClosure K)
      (MvPolynomial.homogeneousSubmodule (Fin 4) (SeparableClosure K) 2) = 10 := by
    rw [four_variable_homogeneous_finrank]
    decide
  have hrelJ := finrank_homogeneousIdealPiece_add_finrank_grading J 2
  have hgradeJ : Module.finrank (SeparableClosure K) (grading J 2) = 7 := by
    omega
  have hgradeI : Module.finrank K (grading I 2) ≤
      Module.finrank (SeparableClosure K) (grading J 2) :=
    grade_finrank_le_coefficientExtension I J hJ 2
  have hquadricI : Module.finrank K
      (MvPolynomial.homogeneousSubmodule (Fin 4) K 2) = 10 := by
    rw [four_variable_homogeneous_finrank]
    decide
  have hrelI := finrank_homogeneousIdealPiece_add_finrank_grading I 2
  have hupper := quadraticPiece_finrank_le_three_of_separableGeometricallyStandardTwistedCubic hgeo
  omega


open scoped TensorProduct


theorem quadraticPieceGenerates_of_separableGeometricallyStandardTwistedCubic
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : SeparableGeometricallyStandardTwistedCubic I) :
    quadraticPieceGenerates I := by
  let L := SeparableClosure K
  let J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L) :=
    HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom (algebraMap K L)) I
  have hJ : I.toIdeal.map (MvPolynomial.map (algebraMap K L)) = J.toIdeal := by
    change I.toIdeal.map (MvPolynomial.map (algebraMap K L)) =
      (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom (algebraMap K L)) I).toIdeal
    rw [HomogeneousIdeal.toIdeal_map]
    rfl
  let M : GL (Fin 4) L := Classical.choose hgeo
  have hM : (I.toIdeal.map (MvPolynomial.map (algebraMap K L))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L := Classical.choose_spec hgeo
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) L).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have hMJ : (standardTwistedCubicHomogeneousIdeal (K := L)).toIdeal =
      J.toIdeal.map
        (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) L) hdet).toRingHom := by
    change standardTwistedCubicIdeal L = J.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) L) hdet).toRingHom
    rw [← hJ]
    exact hM.symm
  have hquadJ : quadraticPieceGenerates J ∧
      Module.finrank L (homogeneousIdealPiece J 2) = 3 :=
    coordinateChange_standardTwistedCubic_quadraticPiece J
      (M : Matrix (Fin 4) (Fin 4) L) hdet hMJ
  have hdimI : Module.finrank K (homogeneousIdealPiece I 2) = 3 :=
    quadraticPiece_finrank_eq_three_of_separableGeometricallyStandardTwistedCubic hgeo
  have hT : Function.Bijective
      (homogeneousIdealPieceCoefficientTensorMap I J hJ 2) :=
    homogeneousIdealPieceCoefficientTensorMap_bijective_of_finrank_eq I J hJ 2 3 hdimI hquadJ.2
  let G : Ideal (MvPolynomial (Fin 4) K) :=
    Ideal.span (Set.range fun p : homogeneousIdealPiece I 2 => p.val.val)
  have hpiece_mem (q : homogeneousIdealPiece J 2) : q.val.val ∈
      G.map (MvPolynomial.map (algebraMap K L)) := by
    obtain ⟨z, hz⟩ := hT.2 q
    subst q
    induction z using TensorProduct.induction_on with
    | zero => simp [homogeneousIdealPieceCoefficientTensorMap]
    | add x y hx hy =>
      simpa [map_add] using Ideal.add_mem (G.map (MvPolynomial.map (algebraMap K L))) hx hy
    | tmul a p =>
      rw [homogeneousIdealPieceCoefficientTensorMap, LinearMap.liftBaseChange_tmul]
      change a • MvPolynomial.map (algebraMap K L) p.val.val ∈
        G.map (MvPolynomial.map (algebraMap K L))
      rw [MvPolynomial.smul_eq_C_mul]
      apply Ideal.mul_mem_left
      apply Ideal.mem_map_of_mem
      exact Ideal.subset_span (Set.mem_range_self p)
  have hJG_le : J.toIdeal ≤ G.map (MvPolynomial.map (algebraMap K L)) := by
    rw [hquadJ.1]
    apply Ideal.span_le.mpr
    rintro p ⟨q, rfl⟩
    exact hpiece_mem q
  have hGI : G ≤ I.toIdeal := by
    apply Ideal.span_le.mpr
    rintro p ⟨q, rfl⟩
    exact q.property
  have hGJ : G.map (MvPolynomial.map (algebraMap K L)) ≤ J.toIdeal := by
    rw [← hJ]
    exact Ideal.map_mono hGI
  have hJG : J.toIdeal = G.map (MvPolynomial.map (algebraMap K L)) :=
    le_antisymm hJG_le hGJ
  unfold quadraticPieceGenerates
  change I.toIdeal = G
  calc
    I.toIdeal = Ideal.comap (MvPolynomial.map (algebraMap K L))
        (I.toIdeal.map (MvPolynomial.map (algebraMap K L))) :=
      (mvPolynomial_comap_map_coefficientExtension I.toIdeal).symm
    _ = Ideal.comap (MvPolynomial.map (algebraMap K L)) J.toIdeal := by rw [hJ]
    _ = Ideal.comap (MvPolynomial.map (algebraMap K L))
        (G.map (MvPolynomial.map (algebraMap K L))) := by rw [hJG]
    _ = G := mvPolynomial_comap_map_coefficientExtension G
/-- The separable coordinate standardization descends all the way to a
 ground-field linear coordinate presentation of the same ideal. -/
theorem groundTwistedCubicPresentation_of_separableGeometricallyStandardTwistedCubic
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : SeparableGeometricallyStandardTwistedCubic I) :
    GroundTwistedCubicPresentation I := by
  exact (separableStandardTwistedCubicPresentation_of_quadraticPiece
    (quadraticPieceGenerates_of_separableGeometricallyStandardTwistedCubic hgeo)
    (quadraticPiece_finrank_eq_three_of_separableGeometricallyStandardTwistedCubic hgeo)
    hgeo).toGroundPresentation

/-- A separably standard twisted-cubic ideal has a ground-field point,
without a perfectness assumption on the base field. -/
theorem separableGeometricallyStandardTwistedCubic_has_rational_section
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : SeparableGeometricallyStandardTwistedCubic I) :
    ∃ s : Spec (.of K) ⟶ scheme I, s ≫ toBase I = 𝟙 _ := by
  obtain ⟨M, hM⟩ :=
    groundTwistedCubicPresentation_of_separableGeometricallyStandardTwistedCubic hgeo
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  exact splitTwistedCubic_has_rational_section I
    (M : Matrix (Fin 4) (Fin 4) K) hdet hM

/-- A quadratically generated ideal which is separably a standard twisted
cubic is the ground projective line.  The dimension of its quadratic piece is
now supplied by coefficient and coordinate descent. -/
noncomputable def schemeIsoProjectiveLine_of_quadraticGeneration
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgen : quadraticPieceGenerates I)
    (hgeo : SeparableGeometricallyStandardTwistedCubic I) :
    scheme I ≅ projectiveLineProj K :=
  schemeIsoProjectiveLine_of_quadraticPiece hgen
    (quadraticPiece_finrank_eq_three_of_separableGeometricallyStandardTwistedCubic hgeo) hgeo


/-- A separably standard twisted cubic has a ground-field projective-line
model; its ideal is generated by the descended quadratic piece. -/
noncomputable def schemeIsoProjectiveLine_of_separableGeometricallyStandardTwistedCubic
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : SeparableGeometricallyStandardTwistedCubic I) :
    scheme I ≅ projectiveLineProj K :=
  GroundTwistedCubicPresentation.schemeIsoProjectiveLine
    (groundTwistedCubicPresentation_of_separableGeometricallyStandardTwistedCubic hgeo)

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u
variable {K : Type u} [Field K]

/-- The all-characteristic separable-coordinate form of `lem:twisted-cubic`.
If the geometric standardization of the homogeneous ideal is defined over the
separable closure, the curve has its standard projective embedding, is the
ground projective line, and has a ground-field point. -/
theorem twistedCubic_descent_separable
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : SeparableGeometricallyStandardTwistedCubic I) :
    GroundTwistedCubicPresentation I ∧
      (∃ _e : scheme I ≅ projectiveLineProj K,
        ∃ s : Spec (.of K) ⟶ scheme I, s ≫ toBase I = 𝟙 _) := by
  refine ⟨groundTwistedCubicPresentation_of_separableGeometricallyStandardTwistedCubic hgeo,
    schemeIsoProjectiveLine_of_separableGeometricallyStandardTwistedCubic hgeo, ?_⟩
  exact separableGeometricallyStandardTwistedCubic_has_rational_section hgeo

end PfaffianDescent.QuarticNet
