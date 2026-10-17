import PfaffianDescent.AmbientPointKoszulStalkExactness
import PfaffianDescent.PolynomialLinearChange
import PfaffianDescent.VoisinProjectiveSpaceCech

/-! # Actual ambient chart transport under a homogeneous coordinate basis

An invertible linear coordinate substitution induces an equivalence of the
actual degree-zero homogeneous chart rings. Thus the coordinate Koszul
matrices remain exact on every chart of the changed coordinate basis.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The actual polynomial substitution, viewed as a graded ring map. -/
def ambientPointKoszul_basisGradedHom (M : Matrix (Fin 4) (Fin 4) K) : PS →+*ᵍ PS where
  __ := (linearSubstitution M).toRingHom
  map_mem := by
    intro n p hp
    exact linearSubstitution_homogeneous M hp

@[simp] theorem ambientPointKoszul_basisGradedHom_X
    (M : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    ambientPointKoszul_basisGradedHom M (X i) = linearCoordinate M i :=
  linearSubstitution_X M i

theorem ambientPointKoszul_basisGradedHom_comp_inv
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    (ambientPointKoszul_basisGradedHom M⁻¹).comp (ambientPointKoszul_basisGradedHom M) =
      GradedRingHom.id PS := by
  apply GradedRingHom.ext
  intro p
  change linearSubstitution M⁻¹ (linearSubstitution M p) = p
  have h := congrArg (fun f : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) K => f p)
    (linearSubstitution_comp M⁻¹ M)
  simpa [Matrix.mul_nonsing_inv M hM, linearSubstitution_one] using h

theorem ambientPointKoszul_basisGradedHom_inv_comp
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    (ambientPointKoszul_basisGradedHom M).comp (ambientPointKoszul_basisGradedHom M⁻¹) =
      GradedRingHom.id PS := by
  apply GradedRingHom.ext
  intro p
  change linearSubstitution M (linearSubstitution M⁻¹ p) = p
  have h := congrArg (fun f : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) K => f p)
    (linearSubstitution_comp M M⁻¹)
  simpa [Matrix.nonsing_inv_mul M hM, linearSubstitution_one] using h

private theorem basis_inverse_powers_le
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (s : MvPolynomial (Fin 4) K) :
    Submonoid.powers (ambientPointKoszul_basisGradedHom M s) ≤
      (Submonoid.powers s).comap (ambientPointKoszul_basisGradedHom M⁻¹) := by
  rintro _ ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  rw [map_pow]
  have h := DFunLike.congr_fun (ambientPointKoszul_basisGradedHom_comp_inv M hM) s
  change s ^ n = (ambientPointKoszul_basisGradedHom M⁻¹
    (ambientPointKoszul_basisGradedHom M s)) ^ n
  exact congrArg (fun p => p ^ n) h.symm

private theorem basis_forward_powers_le
    (M : Matrix (Fin 4) (Fin 4) K) (s : MvPolynomial (Fin 4) K) :
    Submonoid.powers s ≤
      (Submonoid.powers (ambientPointKoszul_basisGradedHom M s)).comap
        (ambientPointKoszul_basisGradedHom M) := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, (map_pow (ambientPointKoszul_basisGradedHom M) s n).symm⟩

private theorem homogeneousMap_eq_id (f : PS →+*ᵍ PS) (hf : f = GradedRingHom.id PS)
    (P : Submonoid (MvPolynomial (Fin 4) K)) (hp : P ≤ P.comap f) :
    HomogeneousLocalization.map f hp = RingHom.id (HomogeneousLocalization PS P) := by
  cases hf
  exact HomogeneousLocalization.map_id PS P

private theorem homogeneousMaps_left_inverse (f g : PS →+*ᵍ PS)
    (hgf : g.comp f = GradedRingHom.id PS)
    (P Q : Submonoid (MvPolynomial (Fin 4) K))
    (hf : P ≤ Q.comap f) (hg : Q ≤ P.comap g) :
    Function.LeftInverse (HomogeneousLocalization.map g hg) (HomogeneousLocalization.map f hf) := by
  intro z
  rw [HomogeneousLocalization.map_map]
  exact DFunLike.congr_fun (homogeneousMap_eq_id _ hgf _ _) z

def ambientPointKoszul_basisChartHom
    (M : Matrix (Fin 4) (Fin 4) K) (j : Fin 4) :
    Away PS (X j) →+* Away PS (ambientPointKoszul_basisGradedHom M (X j)) :=
  Away.map (ambientPointKoszul_basisGradedHom M) (X j)

def ambientPointKoszul_basisChartHomInv
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (j : Fin 4) :
    Away PS (ambientPointKoszul_basisGradedHom M (X j)) →+* Away PS (X j) :=
  HomogeneousLocalization.map (ambientPointKoszul_basisGradedHom M⁻¹)
    (basis_inverse_powers_le M hM (X j))

private theorem basisChart_left_inverse
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (j : Fin 4) :
    Function.LeftInverse (ambientPointKoszul_basisChartHomInv M hM j)
      (ambientPointKoszul_basisChartHom M j) := by
  exact homogeneousMaps_left_inverse _ _
    (ambientPointKoszul_basisGradedHom_comp_inv M hM) _ _
    (basis_forward_powers_le M (X j)) (basis_inverse_powers_le M hM (X j))

private theorem basisChart_right_inverse
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (j : Fin 4) :
    Function.RightInverse (ambientPointKoszul_basisChartHomInv M hM j)
      (ambientPointKoszul_basisChartHom M j) := by
  exact homogeneousMaps_left_inverse _ _
    (ambientPointKoszul_basisGradedHom_inv_comp M hM) _ _
    (basis_inverse_powers_le M hM (X j)) (basis_forward_powers_le M (X j))

/-- The actual homogeneous affine chart equivalence induced by an
invertible linear substitution. -/
def ambientPointKoszul_basisChartEquiv
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (j : Fin 4) :
    Away PS (X j) ≃+* Away PS (ambientPointKoszul_basisGradedHom M (X j)) where
  __ := ambientPointKoszul_basisChartHom M j
  invFun := ambientPointKoszul_basisChartHomInv M hM j
  left_inv := basisChart_left_inverse M hM j
  right_inv := basisChart_right_inverse M hM j

/-- The changed coordinates, as actual degree-one homogeneous elements. -/
def ambientPointKoszul_basis (M : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) : PS 1 :=
  ⟨ambientPointKoszul_basisGradedHom M (X i),
    Graded.map_mem (ambientPointKoszul_basisGradedHom M) (isHomogeneous_X K i)⟩

@[simp] theorem ambientPointKoszul_basis_coe
    (M : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    (ambientPointKoszul_basis M i : MvPolynomial (Fin 4) K) = linearCoordinate M i :=
  ambientPointKoszul_basisGradedHom_X M i

set_option backward.isDefEq.respectTransparency false in
/-- Invertible degree-one basis elements generate the actual irrelevant ideal. -/
theorem ambientPointKoszul_basis_span_irrelevant
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    (HomogeneousIdeal.irrelevant PS).toIdeal ≤
      Ideal.span (Set.range fun i : Fin 4 =>
        (ambientPointKoszul_basis M i : MvPolynomial (Fin 4) K)) := by
  apply (ProjectiveNegativeTwist.p3Coordinates_span_irrelevant K).trans
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  change X j ∈ Ideal.span (Set.range fun i : Fin 4 =>
    (ambientPointKoszul_basis M i : MvPolynomial (Fin 4) K))
  have hj : linearSubstitution M (linearCoordinate M⁻¹ j) = X j := by
    rw [linearSubstitution_coordinate, Matrix.nonsing_inv_mul M hM]
    simpa only [linearSubstitution_one, AlgHom.id_apply] using
      (linearSubstitution_X (1 : Matrix (Fin 4) (Fin 4) K) j).symm
  rw [← hj]
  change linearSubstitution M (∑ i : Fin 4, C (M⁻¹ j i) * X i) ∈ _
  simp only [map_sum, map_mul, linearSubstitution_X, AlgHom.commutes, algebraMap_eq]
  apply Ideal.sum_mem
  intro i _
  apply Ideal.mul_mem_left
  exact Ideal.subset_span ⟨i, ambientPointKoszul_basis_coe M i⟩

/-- The actual charts of any invertible homogeneous coordinate basis cover `P3`. -/
theorem ambientPointKoszul_basisOpen_iSup
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    ⨆ i : Fin 4, Proj.basicOpen PS
      (ambientPointKoszul_basis M i : MvPolynomial (Fin 4) K) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  exact ambientPointKoszul_basis_span_irrelevant M hM

/-- The normalized basis coordinate in its actual projective chart ring. -/
def ambientPointKoszul_basisChartCoordinate
    (M : Matrix (Fin 4) (Fin 4) K) (j i : Fin 4) :
    Away PS (ambientPointKoszul_basis M j : MvPolynomial (Fin 4) K) :=
  AllCharacteristics.GradedChart.normalized PS (ambientPointKoszul_basis M j).property
    (ambientPointKoszul_basis M i) (ambientPointKoszul_basis M i).property

set_option backward.isDefEq.respectTransparency false in
theorem ambientPointKoszul_basisChartEquiv_coordinate
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (j i : Fin 4) :
    ambientPointKoszul_basisChartEquiv M hM j
      (ambientChartCoordinate (R := K) (σ := Fin 4) j i) =
    ambientPointKoszul_basisChartCoordinate M j i := by
  change Away.map (ambientPointKoszul_basisGradedHom M) (X j)
    (Away.mk PS (isHomogeneous_X K j) 1 (X i) _) = _
  rw [Away.map_mk]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Degree-two exactness on every actual chart of an invertible basis. -/
theorem ambientPointKoszul_basisChart_exact_middle
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (j : Fin 4) :
    LinearMap.range (threeGeneratorFirst
      (ambientPointKoszul_basisChartCoordinate M j 1)
      (ambientPointKoszul_basisChartCoordinate M j 2)
      (ambientPointKoszul_basisChartCoordinate M j 3)) =
    LinearMap.ker (threeGeneratorMiddle
      (ambientPointKoszul_basisChartCoordinate M j 1)
      (ambientPointKoszul_basisChartCoordinate M j 2)
      (ambientPointKoszul_basisChartCoordinate M j 3)) := by
  have h := ambientPointKoszul_exact_middle_of_ringEquiv
    (ambientPointKoszul_basisChartEquiv M hM j)
    (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
    (ambientChartCoordinate (R := K) (σ := Fin 4) j 2)
    (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)
    (ambientPointKoszul_chart_exact_middle K j)
  simpa only [ambientPointKoszul_basisChartEquiv_coordinate, ambientPointKoszul_basis] using h

set_option backward.isDefEq.respectTransparency false in
/-- Degree-one exactness on every actual chart of an invertible basis. -/
theorem ambientPointKoszul_basisChart_exact_last
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (j : Fin 4) :
    LinearMap.range (threeGeneratorMiddle
      (ambientPointKoszul_basisChartCoordinate M j 1)
      (ambientPointKoszul_basisChartCoordinate M j 2)
      (ambientPointKoszul_basisChartCoordinate M j 3)) =
    LinearMap.ker (threeGeneratorLast
      (ambientPointKoszul_basisChartCoordinate M j 1)
      (ambientPointKoszul_basisChartCoordinate M j 2)
      (ambientPointKoszul_basisChartCoordinate M j 3)) := by
  have h := ambientPointKoszul_exact_last_of_ringEquiv
    (ambientPointKoszul_basisChartEquiv M hM j)
    (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
    (ambientChartCoordinate (R := K) (σ := Fin 4) j 2)
    (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)
    (ambientPointKoszul_chart_exact_last K j)
  simpa only [ambientPointKoszul_basisChartEquiv_coordinate, ambientPointKoszul_basis] using h

end PfaffianDescent
