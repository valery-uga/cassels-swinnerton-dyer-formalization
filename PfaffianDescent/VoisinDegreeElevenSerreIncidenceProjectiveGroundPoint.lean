import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProjectiveLiftedChartSquare

/-! # Literal ground projective points and their coefficient-change square -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceProjectiveLiftedChartPolynomialIso_toBase
    {K : Type u} [Field K] {σ : Type} (j : σ) :
    let I := (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (serreIncidenceProjectiveLiftedChartPolynomialIso (K := K) j).hom ≫
      Spec.map (CommRingCat.ofHom (chartBaseMap I j)) =
    Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} {i : σ // i ≠ j}) K)) := by
  simp only [serreIncidenceProjectiveLiftedChartPolynomialIso, Functor.mapIso_hom,
    Iso.op_hom, Scheme.Spec_map]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro k
  apply (serreIncidenceProjectiveLiftedChartPolynomialEquiv (K := K) j).injective
  simp [serreIncidenceProjectiveLiftedChartPolynomialEquiv_C]

def serreIncidenceProjectiveGroundPoint
    {K : Type u} [Field K] {σ : Type} (j : σ)
    (x : ULift.{u} {i : σ // i ≠ j} → K) :
    Spec (.of K) ⟶ scheme (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval x)) ≫
    (serreIncidenceProjectiveLiftedChartPolynomialIso (K := K) j).hom ≫ chartι _ j

theorem serreIncidenceProjectiveGroundPoint_toBase
    {K : Type u} [Field K] {σ : Type} (j : σ)
    (x : ULift.{u} {i : σ // i ≠ j} → K) :
    serreIncidenceProjectiveGroundPoint j x ≫
      toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) = 𝟙 _ := by
  simp only [serreIncidenceProjectiveGroundPoint, Category.assoc, chartι_toBase,
    serreIncidenceProjectiveLiftedChartPolynomialIso_toBase]
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((MvPolynomial.eval x).comp MvPolynomial.C)) = _
  have h : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id K := by ext k; simp
  rw [h]
  change Scheme.Spec.map (𝟙 (Opposite.op (CommRingCat.of K))) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

theorem serreIncidenceProjectiveGroundPoint_coefficient_square
    {K E : Type u} [Field K] [Field E] [Algebra K E] {σ : Type} (j : σ)
    (x : ULift.{u} {i : σ // i ≠ j} → K) :
    serreIncidenceProjectiveGroundPoint j (fun i => algebraMap K E (x i)) ≫
      projectiveCoefficientMap (algebraMap K E)
        (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
        (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E)) (by simp) =
    Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ serreIncidenceProjectiveGroundPoint j x := by
  simp only [serreIncidenceProjectiveGroundPoint, Category.assoc,
    chartι_projectiveCoefficientMap]
  rw [← Category.assoc _ _ (chartι _ j)]
  rw [serreIncidenceProjectiveLiftedChartPolynomial_coefficient_square]
  simpa only [Category.assoc] using congrArg
    (fun z => z ≫ (serreIncidenceProjectiveLiftedChartPolynomialIso (K := K) j).hom ≫
      chartι (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j)
    (serreIncidenceGroundGridSpec_coefficient_square (E := E) x)

end PfaffianDescent
