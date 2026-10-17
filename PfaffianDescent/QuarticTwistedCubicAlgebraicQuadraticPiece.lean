import PfaffianDescent.QuarticTwistedCubicSeparableQuadraticPiece

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u
variable {K : Type u} [Field K]

theorem quadraticPiece_finrank_le_three_of_geometricallyStandardTwistedCubic
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : GeometricallyStandardTwistedCubic I) :
    Module.finrank K (homogeneousIdealPiece I 2) ≤ 3 := by
  let J : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin 4) (AlgebraicClosure K)) :=
    HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom (algebraMap K (AlgebraicClosure K))) I
  have hJ : I.toIdeal.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K))) =
      J.toIdeal := by
    change I.toIdeal.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K))) =
      (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom (algebraMap K (AlgebraicClosure K))) I).toIdeal
    rw [HomogeneousIdeal.toIdeal_map]
    rfl
  let M : GL (Fin 4) (AlgebraicClosure K) := Classical.choose hgeo
  have hM : (I.toIdeal.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K))).toRingHom =
        standardTwistedCubicIdeal (AlgebraicClosure K) := Classical.choose_spec hgeo
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K)).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have hMJ : (standardTwistedCubicHomogeneousIdeal (K := AlgebraicClosure K)).toIdeal =
      J.toIdeal.map
        (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K)) hdet).toRingHom := by
    change standardTwistedCubicIdeal (AlgebraicClosure K) = J.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K)) hdet).toRingHom
    rw [← hJ]
    exact hM.symm
  have hdimJ : Module.finrank (AlgebraicClosure K) (homogeneousIdealPiece J 2) = 3 :=
    (coordinateChange_standardTwistedCubic_quadraticPiece J
      (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K)) hdet hMJ).2
  calc
    Module.finrank K (homogeneousIdealPiece I 2) ≤
        Module.finrank (AlgebraicClosure K) (homogeneousIdealPiece J 2) :=
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

theorem quadraticPiece_finrank_eq_three_of_geometricallyStandardTwistedCubic
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : GeometricallyStandardTwistedCubic I) :
    Module.finrank K (homogeneousIdealPiece I 2) = 3 := by
  let J : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin 4) (AlgebraicClosure K)) :=
    HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom (algebraMap K (AlgebraicClosure K))) I
  have hJ : I.toIdeal.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K))) =
      J.toIdeal := by
    change I.toIdeal.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K))) =
      (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom (algebraMap K (AlgebraicClosure K))) I).toIdeal
    rw [HomogeneousIdeal.toIdeal_map]
    rfl
  let M : GL (Fin 4) (AlgebraicClosure K) := Classical.choose hgeo
  have hM : (I.toIdeal.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K))).toRingHom =
        standardTwistedCubicIdeal (AlgebraicClosure K) := Classical.choose_spec hgeo
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K)).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have hMJ : (standardTwistedCubicHomogeneousIdeal (K := AlgebraicClosure K)).toIdeal =
      J.toIdeal.map
        (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K)) hdet).toRingHom := by
    change standardTwistedCubicIdeal (AlgebraicClosure K) = J.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K)) hdet).toRingHom
    rw [← hJ]
    exact hM.symm
  have hdimJ : Module.finrank (AlgebraicClosure K) (homogeneousIdealPiece J 2) = 3 :=
    (coordinateChange_standardTwistedCubic_quadraticPiece J
      (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K)) hdet hMJ).2
  have hquadricJ : Module.finrank (AlgebraicClosure K)
      (MvPolynomial.homogeneousSubmodule (Fin 4) (AlgebraicClosure K) 2) = 10 := by
    rw [four_variable_homogeneous_finrank]
    decide
  have hrelJ := finrank_homogeneousIdealPiece_add_finrank_grading J 2
  have hgradeJ : Module.finrank (AlgebraicClosure K) (grading J 2) = 7 := by
    omega
  have hgradeI : Module.finrank K (grading I 2) ≤
      Module.finrank (AlgebraicClosure K) (grading J 2) :=
    grade_finrank_le_coefficientExtension I J hJ 2
  have hquadricI : Module.finrank K
      (MvPolynomial.homogeneousSubmodule (Fin 4) K 2) = 10 := by
    rw [four_variable_homogeneous_finrank]
    decide
  have hrelI := finrank_homogeneousIdealPiece_add_finrank_grading I 2
  have hupper := quadraticPiece_finrank_le_three_of_geometricallyStandardTwistedCubic hgeo
  omega


open scoped TensorProduct


theorem quadraticPieceGenerates_of_geometricallyStandardTwistedCubic
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : GeometricallyStandardTwistedCubic I) :
    quadraticPieceGenerates I := by
  let L := AlgebraicClosure K
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
    quadraticPiece_finrank_eq_three_of_geometricallyStandardTwistedCubic hgeo
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

variable [PerfectField K]

omit [PerfectField K] in
private theorem standardTwistedCubicIdeal_map_algEquiv
    {L E : Type u} [Field L] [Field E] [Algebra K L] [Algebra K E]
    (e : L ≃ₐ[K] E) :
    (standardTwistedCubicIdeal L).map (MvPolynomial.map e.toRingHom) =
      standardTwistedCubicIdeal E := by
  rw [standardTwistedCubicIdeal, Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    fin_cases i <;> simp [standardTwistedCubicGenerators]
  · rintro ⟨i, rfl⟩
    refine ⟨standardTwistedCubicGenerators L i, ⟨i, rfl⟩, ?_⟩
    fin_cases i <;> simp [standardTwistedCubicGenerators]

omit [PerfectField K] in
private theorem ideal_map_coefficient_algEquiv
    {L E : Type u} [Field L] [Field E] [Algebra K L] [Algebra K E]
    (I : Ideal (MvPolynomial (Fin 4) K)) (e : L ≃ₐ[K] E) :
    (I.map (MvPolynomial.map (algebraMap K L))).map
      (MvPolynomial.map e.toRingHom) =
      I.map (MvPolynomial.map (algebraMap K E)) := by
  rw [Ideal.map_map]
  apply congrArg (fun f => Ideal.map f I)
  apply MvPolynomial.ringHom_ext
  · intro x
    simp [e.commutes]
  · intro i
    simp

/-- Over a perfect field, an algebraic-closure coordinate standardization can
be taken over the separable closure.  This identifies the two coordinate
languages used by the all-field and perfect-field descent theorems. -/
theorem separableGeometricallyStandardTwistedCubic_of_geometricallyStandardTwistedCubic
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : GeometricallyStandardTwistedCubic I) :
    SeparableGeometricallyStandardTwistedCubic I := by
  let e : AlgebraicClosure K ≃ₐ[K] SeparableClosure K :=
    IsAlgClosure.equiv K (AlgebraicClosure K) (SeparableClosure K)
  obtain ⟨M, hM⟩ := hgeo
  refine ⟨Matrix.GeneralLinearGroup.map e.toRingHom M, ?_⟩
  have htransport := ideal_map_linearSubstitution_map e.toRingHom
    (I.toIdeal.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K))))
    (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K))
  have hbase :
      (I.toIdeal.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))).map
        (MvPolynomial.map e.toRingHom) =
      I.toIdeal.map (MvPolynomial.map (algebraMap K (SeparableClosure K))) :=
    ideal_map_coefficient_algEquiv I.toIdeal e
  have hstd := standardTwistedCubicIdeal_map_algEquiv (K := K) e
  change
    (I.toIdeal.map (MvPolynomial.map (algebraMap K (SeparableClosure K)))).map
        (linearSubstitution
          ((M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K)).map e.toRingHom)).toRingHom =
      standardTwistedCubicIdeal (SeparableClosure K)
  calc
    (I.toIdeal.map (MvPolynomial.map (algebraMap K (SeparableClosure K)))).map
        (linearSubstitution
          ((M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K)).map e.toRingHom)).toRingHom =
      ((I.toIdeal.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))).map
        (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K))).toRingHom).map
          (MvPolynomial.map e.toRingHom) := by
      rw [htransport, hbase]
    _ = (standardTwistedCubicIdeal (AlgebraicClosure K)).map
          (MvPolynomial.map e.toRingHom) := by rw [hM]
    _ = standardTwistedCubicIdeal (SeparableClosure K) := hstd

/-- Over a perfect field, an ideal which becomes a standard twisted cubic over
 the algebraic closure has a ground-field linear coordinate presentation. -/
theorem groundTwistedCubicPresentation_of_geometricallyStandardTwistedCubic
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : GeometricallyStandardTwistedCubic I) :
    GroundTwistedCubicPresentation I := by
  exact (geometricStandardTwistedCubicPresentation_of_threeQuadrics
    (threeQuadraticPresentation_of_quadraticPieceGenerates
      (quadraticPieceGenerates_of_geometricallyStandardTwistedCubic hgeo)
      (quadraticPiece_finrank_eq_three_of_geometricallyStandardTwistedCubic hgeo))
    hgeo).toGround

/-- The perfect-field twisted-cubic descent conclusion needed in the
 degree-four argument: the projective curve has a ground-field point. -/
theorem geometricallyStandardTwistedCubic_has_rational_section
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : GeometricallyStandardTwistedCubic I) :
    ∃ s : Spec (.of K) ⟶ scheme I, s ≫ toBase I = 𝟙 _ := by
  obtain ⟨M, hM⟩ :=
    groundTwistedCubicPresentation_of_geometricallyStandardTwistedCubic hgeo
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  exact splitTwistedCubic_has_rational_section I
    (M : Matrix (Fin 4) (Fin 4) K) hdet hM

/-- `lem:twisted-cubic` in the homogeneous-ideal model relevant to the
 perfect-field degree-four argument.  A geometric standardization supplies
 the standard projective embedding, the projective-line model, and a rational
 point. -/
theorem twistedCubic_descent_perfect
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : GeometricallyStandardTwistedCubic I) :
    GroundTwistedCubicPresentation I ∧
      (∃ _e : scheme I ≅ projectiveLineProj K,
        ∃ s : Spec (.of K) ⟶ scheme I, s ≫ toBase I = 𝟙 _) := by
  refine ⟨groundTwistedCubicPresentation_of_geometricallyStandardTwistedCubic hgeo,
    GroundTwistedCubicPresentation.schemeIsoProjectiveLine
      (groundTwistedCubicPresentation_of_geometricallyStandardTwistedCubic hgeo), ?_⟩
  exact geometricallyStandardTwistedCubic_has_rational_section hgeo

/-- The ideal-level form of the twisted-cubic descent lemma over a perfect
 field, including its projective embedding. -/
noncomputable def schemeIsoProjectiveLine_of_geometricallyStandardTwistedCubic
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : GeometricallyStandardTwistedCubic I) :
    scheme I ≅ projectiveLineProj K :=
  GroundTwistedCubicPresentation.schemeIsoProjectiveLine
    (groundTwistedCubicPresentation_of_geometricallyStandardTwistedCubic hgeo)

end PfaffianDescent.QuarticNet
