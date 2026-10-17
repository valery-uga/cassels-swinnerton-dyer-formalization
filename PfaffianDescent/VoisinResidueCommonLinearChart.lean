import PfaffianDescent.VoisinProjectivePointRenormalization
import PfaffianDescent.VoisinGeometricEightGoodPoint
import Mathlib.Algebra.Module.Submodule.Union

/-!
# A common ground-field linear chart for residue-field points

The points obtained by descending an ordered configuration need not be
rational over the ground field.  Nevertheless, over an infinite ground
field one can choose a single ground-field linear form which is nonzero on
all of their residue-field coordinate vectors.  This is the finite-union of
proper subspaces argument needed to place the descended configuration in one
common projective affine chart.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Finitely many normalized vectors over an extension field admit a common
linear chart whose coefficients already lie in the infinite ground field. -/
theorem exists_groundField_common_linear_chart_for_normalized_vectors
    {K Q : Type u} [Field K] [Field Q] [Algebra K Q] [Infinite K]
    {ι : Type*} [Finite ι]
    (y : ι → Fin 4 → Q) (j : ι → Fin 4)
    (hyj : ∀ i, y i (j i) = 1) :
    ∃ c : Fin 4 → K, ∀ i,
      (homogeneousLinearForm c).eval₂ (algebraMap K Q) (y i) ≠ 0 := by
  classical
  let f : ι → (Fin 4 → K) →ₗ[K] Q := fun i =>
    Fintype.linearCombination K (y i)
  have hker : ∀ i, LinearMap.ker (f i) ≠ ⊤ := by
    intro i htop
    have hm : Pi.single (j i) 1 ∈ LinearMap.ker (f i) := by
      rw [htop]
      exact Submodule.mem_top
    have hz := LinearMap.mem_ker.mp hm
    have : y i (j i) = 0 := by
      simpa only [f, Fintype.linearCombination_apply_single, one_smul] using hz
    exact one_ne_zero (hyj i ▸ this)
  obtain ⟨c, hc⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top
      (fun i => LinearMap.ker (f i)) hker
  refine ⟨c, fun i => ?_⟩
  have hfc : f i c ≠ 0 := by
    simpa only [LinearMap.mem_ker, ne_eq] using hc i
  simpa only [f, Fintype.linearCombination_apply, Algebra.smul_def,
    homogeneousLinearForm, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X] using hfc

/-- Finitely many nonzero vectors over an extension field admit a common
linear chart whose coefficients lie in the infinite ground field. -/
theorem exists_groundField_common_linear_chart_for_nonzero_vectors
    {K Q : Type u} [Field K] [Field Q] [Algebra K Q] [Infinite K]
    {ι : Type*} [Finite ι]
    (y : ι → Fin 4 → Q) (hy : ∀ i, y i ≠ 0) :
    ∃ c : Fin 4 → K, ∀ i,
      (homogeneousLinearForm c).eval₂ (algebraMap K Q) (y i) ≠ 0 := by
  classical
  choose j hj using fun i => Function.ne_iff.mp (hy i)
  let n : ι → Fin 4 → Q := fun i => (y i (j i))⁻¹ • y i
  have hnj : ∀ i, n i (j i) = 1 := by
    intro i
    simp only [n, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ (hj i)
  obtain ⟨c, hc⟩ :=
    exists_groundField_common_linear_chart_for_normalized_vectors
      (K := K) (Q := Q) n j hnj
  refine ⟨c, fun i hzero => hc i ?_⟩
  have hnEval : (homogeneousLinearForm c).eval₂
      (algebraMap K Q) (n i) =
      (y i (j i))⁻¹ * (homogeneousLinearForm c).eval₂
        (algebraMap K Q) (y i) := by
    simp only [n, homogeneousLinearForm, MvPolynomial.eval₂_sum,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_X, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hnEval, hzero, mul_zero]

/-- Detecting residue coordinates place the descended ordered configuration
point in one linear basic open defined over the ground field. -/
theorem detectingCoordinates_mem_orderedFamilyCommonLinearBasicOpen
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (hz : OriginalCubicOrderedEightDetectingCoordinatesAt p hp z) :
    ∃ c : Fin 4 → K,
      z.val ∈ orderedFamilyCommonOpen (hypersurfaceToBase p hp)
        (Proj.basicOpen (grading (equationIdeal p hp))
          (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
            (homogeneousLinearForm c))) 8 := by
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let Q := O.residueField z
  letI : Algebra K Q := pointAlgebra
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom z
  obtain ⟨j, y, hyj, hmarked, hyDetect⟩ := hz
  obtain ⟨c, hc⟩ :=
    exists_groundField_common_linear_chart_for_normalized_vectors
      (K := K) (Q := Q) y j hyj
  refine ⟨c, (mem_orderedFamilyCommonOpen_iff
    (hypersurfaceToBase p hp)
    (Proj.basicOpen (grading (equationIdeal p hp))
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
        (homogeneousLinearForm c))) 8 z.val).mpr ?_⟩
  intro i
  obtain ⟨he0, hX, hmarked_i⟩ := hmarked i
  have hambient :
      (O.fromSpecResidueField z ≫
        (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
          hsep 8 (hypersurfaceToAmbient p hp) i))
          (IsLocalRing.closedPoint Q) ∈
        Proj.basicOpen (homogeneousSubmodule (Fin 4) K)
          (homogeneousLinearForm c) := by
    rw [← hmarked_i]
    exact linearNormalizedPoint_mem_basicOpen_of_eval₂_ne_zero
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
      (y i) (j i) (hyj i) he0 (homogeneousLinearForm c)
      (homogeneousLinearForm_isHomogeneous c) (hc i)
  have hambient' :
      hypersurfaceToAmbient p hp
          (Over.Hom.left
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i) z.val) ∈
        Proj.basicOpen (homogeneousSubmodule (Fin 4) K)
          (homogeneousLinearForm c) := by
    have hr : O.fromSpecResidueField z (IsLocalRing.closedPoint Q) = z :=
      Scheme.fromSpecResidueField_apply z (IsLocalRing.closedPoint Q)
    rw [show (O.fromSpecResidueField z ≫
      (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
        hsep 8 (hypersurfaceToAmbient p hp) i))
          (IsLocalRing.closedPoint Q) =
        (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
          hsep 8 (hypersurfaceToAmbient p hp) i) z by
      exact congrArg (fun w : O =>
        (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
          hsep 8 (hypersurfaceToAmbient p hp) i) w) hr] at hambient
    change hypersurfaceToAmbient p hp
        (Over.Hom.left
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i)
            ((orderedFamilyConfigurationOpen
              (hypersurfaceToBase p hp) 8).ι z)) ∈
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K)
        (homogeneousLinearForm c) at hambient
    simpa only [show (orderedFamilyConfigurationOpen
      (hypersurfaceToBase p hp) 8).ι z = z.val by rfl] using hambient
  change Over.Hom.left
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i) z.val ∈
    hypersurfaceToAmbient p hp ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K)
        (homogeneousLinearForm c) at hambient'
  change Over.Hom.left
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i) z.val ∈
    Proj.basicOpen (grading (equationIdeal p hp))
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
        (homogeneousLinearForm c))
  change Over.Hom.left
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i) z.val ∈
    quotientProjMap (equationIdeal p hp) ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K)
        (homogeneousLinearForm c)
  exact hambient'

end PfaffianDescent
