import PfaffianDescent.AmbientPointKoszulBasisGeometry

/-! # Uniqueness of the actual affine restriction map of a basis point -/

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

def ambientPointKoszul_basisChartPolynomialEquiv
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    MvPolynomial (Fin 3) K ≃+* Away PS (ambientPointKoszul_basis M 0).val :=
  (ambientPointKoszul_chartPolynomialEquiv K).trans (ambientPointKoszul_basisChartEquiv M hM 0)

set_option backward.isDefEq.respectTransparency false in
theorem ambientPointKoszul_basisChartPolynomialEquiv_C
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (a : K) :
    ambientPointKoszul_basisChartPolynomialEquiv M hM (C a) =
      AllCharacteristics.GradedChart.baseMap PS (z := (ambientPointKoszul_basis M 0).val) a :=
  (congrArg (ambientPointKoszul_basisChartEquiv M hM 0)
    (ambientPointKoszul_chartPolynomialEquiv_C K a)).trans
      (ambientPointKoszul_basisChartEquiv_base M hM 0 a)

set_option backward.isDefEq.respectTransparency false in
theorem ambientPointKoszul_basisChartPolynomialEquiv_X
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (i : Fin 3) :
    ambientPointKoszul_basisChartPolynomialEquiv M hM (X i) =
      ambientPointKoszul_basisChartCoordinate M 0 i.succ :=
  (congrArg (ambientPointKoszul_basisChartEquiv M hM 0)
    (ambientPointKoszul_chartPolynomialEquiv_X K i)).trans
      (ambientPointKoszul_basisChartEquiv_coordinate M hM 0 i.succ)

set_option backward.isDefEq.respectTransparency false in
/-- A homomorphism from the actual point-containing basis chart is
determined by its base coefficients and its three normalized coordinates. -/
theorem ambientPointKoszul_basisChart_hom_ext
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    {A : Type*} [CommRing A]
    (φ ψ : Away PS (ambientPointKoszul_basis M 0).val →+* A)
    (hC : ∀ a : K,
      φ (AllCharacteristics.GradedChart.baseMap PS (z := (ambientPointKoszul_basis M 0).val) a) =
      ψ (AllCharacteristics.GradedChart.baseMap PS (z := (ambientPointKoszul_basis M 0).val) a))
    (hX : ∀ i : Fin 3,
      φ (ambientPointKoszul_basisChartCoordinate M 0 i.succ) =
      ψ (ambientPointKoszul_basisChartCoordinate M 0 i.succ)) : φ = ψ := by
  let e := ambientPointKoszul_basisChartPolynomialEquiv M hM
  have h : φ.comp e.toRingHom = ψ.comp e.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      exact (congrArg φ (ambientPointKoszul_basisChartPolynomialEquiv_C M hM a)).trans
        ((hC a).trans (congrArg ψ (ambientPointKoszul_basisChartPolynomialEquiv_C M hM a)).symm)
    · intro i
      exact (congrArg φ (ambientPointKoszul_basisChartPolynomialEquiv_X M hM i)).trans
        ((hX i).trans (congrArg ψ (ambientPointKoszul_basisChartPolynomialEquiv_X M hM i)).symm)
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := e.surjective z
  exact DFunLike.congr_fun h p

set_option backward.isDefEq.respectTransparency false in
/-- The original basis point restriction is uniquely characterized by
coefficient preservation and vanishing of the three point equations. -/
theorem ambientPointKoszul_basisChartMap_unique
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (φ : Away PS (ambientPointKoszul_basis M 0).val →+* K)
    (hC : ∀ a : K,
      φ (AllCharacteristics.GradedChart.baseMap PS (z := (ambientPointKoszul_basis M 0).val) a) = a)
    (hX : ∀ i : Fin 3, φ (ambientPointKoszul_basisChartCoordinate M 0 i.succ) = 0) :
    φ = ambientPointKoszul_basisChartMap M hM := by
  apply ambientPointKoszul_basisChart_hom_ext M hM
  · intro a
    exact (hC a).trans (ambientPointKoszul_basisChartMap_base M hM a).symm
  · intro i
    have hi : ambientPointKoszul_vector K i.succ = 0 := by fin_cases i <;> rfl
    exact (hX i).trans ((ambientPointKoszul_basisChartMap_coordinate M hM i.succ).trans hi).symm

end PfaffianDescent
