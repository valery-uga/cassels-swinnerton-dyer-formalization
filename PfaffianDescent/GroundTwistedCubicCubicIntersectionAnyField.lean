import PfaffianDescent.GroundTwistedCubicCubicIntersection
import PfaffianDescent.ProjectiveLinearCoordinateSchemeIso
import AllCharacteristics.ProjectiveBaseChangeFiniteRank
import Mathlib.FieldTheory.RatFunc.Basic

/-! Remove the infinite-field restriction from
the ACTUAL twisted-cubic/cubic intersection rank statement.  Full coefficient
ideals, actual Proj base change and the original GL presentation are used. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Parametrization commutes with actual coefficient extension. -/
theorem standardTwistedCubicParam_coefficientExtension
    (F : MvPolynomial (Fin 4) k) :
    standardTwistedCubicParam K (MvPolynomial.map (algebraMap k K) F) =
      MvPolynomial.map (algebraMap k K) (standardTwistedCubicParam k F) := by
  have h : (standardTwistedCubicParam K).toRingHom.comp
      (MvPolynomial.map (algebraMap k K)) =
    (MvPolynomial.map (algebraMap k K)).comp
      (standardTwistedCubicParam k).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [standardTwistedCubicParam]
    · intro i
      fin_cases i <;> simp [standardTwistedCubicParam]
  exact DFunLike.congr_fun h F

/-- The entire summed intersection ideal commutes with field extension,
including all nilpotent structure. -/
theorem standardTwistedCubicCubicIntersectionIdeal_coefficientExtension
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) :
    (standardTwistedCubicCubicIntersectionIdeal F hF).toIdeal.map
      (MvPolynomial.map (algebraMap k K)) =
    (standardTwistedCubicCubicIntersectionIdeal
      (MvPolynomial.map (algebraMap k K) F) (hF.map (algebraMap k K))).toIdeal := by
  change (standardTwistedCubicIdeal k ⊔ Ideal.span {F}).map
      (MvPolynomial.map (algebraMap k K)) =
    standardTwistedCubicIdeal K ⊔ Ideal.span {MvPolynomial.map (algebraMap k K) F}
  rw [Ideal.map_sup, standardTwistedCubicIdeal_map_coefficientExtension,
    Ideal.map_span, Set.image_singleton]

/-- Standard actual intersection rank nine over ANY field.  The homogeneous
Hilbert bound gives finiteness without an infinite-field assumption, and the
accepted actual Proj coefficient base change descends rank from RatFunc k. -/
theorem standardTwistedCubicCubicIntersection_finite_rank_nine_anyField
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hnonzero : standardTwistedCubicParam k F ≠ 0) :
    ∃ hfinite : IsFinite (toBase (standardTwistedCubicCubicIntersectionIdeal F hF)),
      @AllCharacteristics.finiteSchemeRank k _ _
        (toBase (standardTwistedCubicCubicIntersectionIdeal F hF)) hfinite = 9 := by
  let I := standardTwistedCubicCubicIntersectionIdeal F hF
  letI : IsFinite (toBase I) := by
    apply projective_finite_of_hilbert_bound I 3 9
    intro d hd
    exact (standardTwistedCubicCubicIntersection_grade_finrank F hF hnonzero d hd).le
  letI : Infinite (RatFunc k) :=
    Infinite.of_injective (algebraMap (Polynomial k) (RatFunc k))
      (RatFunc.algebraMap_injective k)
  let J := standardTwistedCubicCubicIntersectionIdeal
    (MvPolynomial.map (algebraMap k (RatFunc k)) F)
    (hF.map (algebraMap k (RatFunc k)))
  have hnonzeroK : standardTwistedCubicParam (RatFunc k)
      (MvPolynomial.map (algebraMap k (RatFunc k)) F) ≠ 0 := by
    rw [standardTwistedCubicParam_coefficientExtension]
    intro hz
    apply hnonzero
    apply MvPolynomial.map_injective (algebraMap k (RatFunc k)) (RingHom.injective _)
    simpa only [map_zero] using hz
  letI : IsFinite (toBase J) :=
    standardTwistedCubicCubicIntersection_isFinite _ _ hnonzeroK
  have hJ : AllCharacteristics.finiteSchemeRank (toBase J) = 9 :=
    standardTwistedCubicCubicIntersection_finiteSchemeRank _ _ hnonzeroK
  have hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k (RatFunc k))) =
      J.toIdeal :=
    standardTwistedCubicCubicIntersectionIdeal_coefficientExtension
      (K := RatFunc k) F hF
  exact ⟨inferInstance,
    (projective_finiteSchemeRank_baseChange I J hIJ).trans hJ⟩

/-- The actual ground GL presentation now supplies intersection finiteness
and rank nine without ANY field-cardinality restriction. -/
theorem GroundTwistedCubicPresentation.cubicIntersection_finite_rank_nine_anyField
    {B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k)}
    (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hnot : F ∉ B.toIdeal) :
    ∃ hfinite : IsFinite (toBase (groundTwistedCubicCubicIntersectionIdeal B F hF)),
      @AllCharacteristics.finiteSchemeRank k _ _
        (toBase (groundTwistedCubicCubicIntersectionIdeal B F hF)) hfinite = 9 := by
  obtain ⟨M, hM⟩ := hB
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) k).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have hnonzero : standardTwistedCubicParam k
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) k) F) ≠ 0 := by
    intro hz
    exact hnot ((twisted_cubic_mem_iff_transformed_param_zero B M hM F).mpr hz)
  let I := groundTwistedCubicCubicIntersectionIdeal B F hF
  let J := standardTwistedCubicCubicIntersectionIdeal
    (linearSubstitution (M : Matrix (Fin 4) (Fin 4) k) F)
    (linearSubstitution_homogeneous _ hF)
  have hIJ : J.toIdeal = I.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) k) hdet).toRingHom :=
    groundTwistedCubicCubicIntersectionIdeal_coordinate_map B M hM F hF hdet
  let e := linearCoordinateChangeSchemeIso
    (M : Matrix (Fin 4) (Fin 4) k) hdet I J hIJ
  have he : e.hom ≫ toBase J = toBase I :=
    linearCoordinateChangeSchemeIso_hom_toBase _ _ _ _ _
  obtain ⟨hfiniteJ, hJ⟩ :=
    standardTwistedCubicCubicIntersection_finite_rank_nine_anyField _ _ hnonzero
  letI := hfiniteJ
  letI : IsFinite (toBase I) := by
    rw [← he]
    infer_instance
  have hRank : AllCharacteristics.finiteSchemeRank (toBase I) =
      AllCharacteristics.finiteSchemeRank (toBase J) := by
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank,
      AllCharacteristics.finiteSchemeRank_eq_finrank, ← he]
    exact congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.hom (toBase J)) _
  exact ⟨inferInstance, hRank.trans hJ⟩

end PfaffianDescent.QuarticNet
