import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProjectiveGroundChartSquare

/-! # Literal coordinates of universe-compatible projective polynomial charts -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidenceProjectiveLiftedChartPolynomialEquiv
    {K : Type u} [CommRing K] {σ : Type} (j : σ) :
    MvPolynomial (ULift.{u} {i : σ // i ≠ j}) K ≃+*
      ChartRing (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j :=
  (MvPolynomial.renameEquiv K Equiv.ulift).toRingEquiv.trans (chartPolynomialEquiv (R := K) j)

def serreIncidenceProjectiveLiftedChartPolynomialIso
    {K : Type u} [CommRing K] {σ : Type} (j : σ) :
    Spec (.of (MvPolynomial (ULift.{u} {i : σ // i ≠ j}) K)) ≅
      Spec (.of (ChartRing (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j)) :=
  Scheme.Spec.mapIso (serreIncidenceProjectiveLiftedChartPolynomialEquiv
    (K := K) j).toCommRingCatIso.symm.op

theorem serreIncidenceProjectiveLiftedChartPolynomialEquiv_C
    {K : Type u} [CommRing K] {σ : Type} (j : σ) (k : K) :
    serreIncidenceProjectiveLiftedChartPolynomialEquiv j (MvPolynomial.C k) =
      chartBaseMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j k := by
  change chartPolynomialEquiv j (MvPolynomial.rename Equiv.ulift (MvPolynomial.C k)) = _
  rw [MvPolynomial.rename_C, chartPolynomialEquiv_C]

theorem serreIncidenceProjectiveLiftedChartPolynomialEquiv_X
    {K : Type u} [CommRing K] {σ : Type} (j : σ)
    (i : ULift.{u} {i : σ // i ≠ j}) :
    serreIncidenceProjectiveLiftedChartPolynomialEquiv (K := K) j (MvPolynomial.X i) =
      chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j i.down.val := by
  unfold serreIncidenceProjectiveLiftedChartPolynomialEquiv
  rw [RingEquiv.trans_apply]
  simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  exact projectiveChartPolynomialEquiv_X K j i.down

end PfaffianDescent
