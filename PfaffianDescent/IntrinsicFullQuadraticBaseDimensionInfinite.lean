import PfaffianDescent.IntrinsicFullQuadraticBasePoint
import PfaffianDescent.IntrinsicFiniteTripleQuadraticDimension
import PfaffianDescent.OriginalFiniteNetOTwoCohomologicalDimension
import PfaffianDescent.ActualP3QuadraticRestrictionChartComparison

/-! The length comparison and full-series dimension, for the intrinsic
scheme-theoretic quadratic series over an infinite field.  The point
proposition itself is already arbitrary-field in the imported endpoint. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [Infinite K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem intrinsicFullQuadraticSystem_exists_finite_triple_iso
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)]
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ ambientToBase) = 8)
    [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i))] :
    ∃ q : Fin 3 → intrinsicFullQuadraticSystem i,
      IsFinite (toBase (intrinsicFullQuadraticTripleIdeal i q)) ∧
      ∃ l : Z ⟶ scheme (intrinsicFullQuadraticTripleIdeal i q),
        IsIso l ∧
        l ≫ quotientProjMap (intrinsicFullQuadraticTripleIdeal i q) = i ∧
        l ≫ toBase (intrinsicFullQuadraticTripleIdeal i q) = i ≫ ambientToBase := by
  obtain ⟨q, hfinite, l, hl, hfac, hbase⟩ :=
    intrinsicFullQuadraticSystem_exists_finite_triple_containing i
  letI := hfinite
  letI := hl
  let T := intrinsicFullQuadraticTripleIdeal i q
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (q 0).val (q 1).val (q 2).val
      (intrinsicFullQuadraticSystem_homogeneous i _ (q 0).property)
      (intrinsicFullQuadraticSystem_homogeneous i _ (q 1).property)
      (intrinsicFullQuadraticSystem_homogeneous i _ (q 2).property))) :=
    inferInstanceAs (IsFinite (toBase T))
  letI : IsFinite (l ≫ toBase T) := by rw [hbase]; infer_instance
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ ambientToBase)
  letI := finiteSchemeCoefficientAlgebra (i ≫ ambientToBase)
  letI := finiteSchemeCoefficient_finite (i ≫ ambientToBase)
  have hΓ8 : Module.finrank K Γ(Z, ⊤) = 8 :=
    (finiteSchemeCoefficient_finrank (i ≫ ambientToBase)).trans hZ
  letI : Nontrivial Γ(Z, ⊤) := Module.nontrivial_of_finrank_pos (by rw [hΓ8]; decide)
  have hT : Nonempty (scheme T) :=
    Nonempty.map l (Nonempty.map Z.isoSpec.inv inferInstance)
  have hseq := AllCharacteristics.sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
    (q 0).val (q 1).val (q 2).val
    (intrinsicFullQuadraticSystem_homogeneous i _ (q 0).property)
    (intrinsicFullQuadraticSystem_homogeneous i _ (q 1).property)
    (intrinsicFullQuadraticSystem_homogeneous i _ (q 2).property) hT
  have hT8 : AllCharacteristics.finiteSchemeRank (toBase T) = 8 :=
    triple_quadrics_intersection_length_eight_of_regular_sequence _ _ _ _ _ _ hseq
  have hL8 : AllCharacteristics.finiteSchemeRank (l ≫ toBase T) = 8 := by
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hbase,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hZ
  have hLIso : IsIso l :=
    isIso_of_finite_closedImmersion_of_finiteSchemeRank_eq l (toBase T)
      (hL8.trans hT8.symm)
  exact ⟨q, hfinite, l, hLIso, hfac, hbase⟩

theorem intrinsicFullQuadraticSystem_finrank_eq_three_of_finite_base
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)]
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ ambientToBase) = 8)
    [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i))] :
    Module.finrank K (intrinsicFullQuadraticSystem i) = 3 := by
  obtain ⟨q, hfinite, l, hl, hfac, hbase⟩ :=
    intrinsicFullQuadraticSystem_exists_finite_triple_iso i hZ
  let f : homogeneousSubmodule (Fin 4) K 2 :=
    ⟨(q 0).val, intrinsicFullQuadraticSystem_homogeneous i _ (q 0).property⟩
  let g : homogeneousSubmodule (Fin 4) K 2 :=
    ⟨(q 1).val, intrinsicFullQuadraticSystem_homogeneous i _ (q 1).property⟩
  let h : homogeneousSubmodule (Fin 4) K 2 :=
    ⟨(q 2).val, intrinsicFullQuadraticSystem_homogeneous i _ (q 2).property⟩
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)) := hfinite
  have hker : (quotientProjMap (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)).ker ≤ i.ker :=
    intrinsicFullQuadraticTripleIdeal_ker_le i q
  have hd := p3OriginalFiniteNet_idealHZero_finrank_by_OTwo_cohomology
    f g h i hker hZ
  exact (p3ActualIdealQuadratic_finrank_eq_intrinsic i).symm.trans hd

end PfaffianDescent
