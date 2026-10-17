import PfaffianDescent.NormalizedPointIntrinsicQuadraticExactKernel

/- SOURCE ONLY / UNVERIFIED. The actual chart ring map determines the
normalized point and its exact full quadratic system, with no point-square
certificate. The base compatibility below is an algebra-map hypothesis,
not a geometric comparison; native algebra maps discharge it internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualNativeChart_coordinates_equations
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4)
    (phi : ChartRing I j →+* A)
    (hbase : phi.comp (chartBaseMap I j) = algebraMap K A) :
    ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A)
      (fun r => phi (chartCoordinate I j r)) = 0 := by
  intro p hp
  have h := congrArg phi (eval₂_chartCoordinate_eq_zero_of_mem I j p hp)
  rw [hom_eval₂, hbase, map_zero] at h
  exact h

lemma actualNativeChart_coordinates_normalized
    {K A : Type u} [Field K] [CommRing A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4)
    (phi : ChartRing I j →+* A) :
    phi (chartCoordinate I j j) = 1 := by
  rw [chartCoordinate_self, map_one]

set_option backward.isDefEq.respectTransparency false in
theorem actualNativeChart_algebraPoint_eq_normalized
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4)
    (phi : ChartRing I j →+* A)
    (hbase : phi.comp (chartBaseMap I j) = algebraMap K A) :
    let x := fun r => phi (chartCoordinate I j r)
    let he := actualNativeChart_coordinates_equations I j phi hbase
    let hOne : (X j).eval₂ (algebraMap K A) x = 1 := by
      simpa only [eval₂_X] using actualNativeChart_coordinates_normalized I j phi
    Spec.map (CommRingCat.ofHom phi) ≫ chartι I j =
      normalizedFiniteEquationPoint I x (X j) (isHomogeneous_X K j) hOne he := by
  dsimp only
  let x := fun r => phi (chartCoordinate I j r)
  let he := actualNativeChart_coordinates_equations I j phi hbase
  let hz : (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K A) x) he)
      (coordinate I j) = 1 := by
    simpa only [coordinate, Ideal.Quotient.lift_mk, eval₂Hom_X'] using
      actualNativeChart_coordinates_normalized I j phi
  have hphi := linearNormalizedPointChartMapAt_eq_of_base_and_coordinates I x he
    (coordinate I j) (coordinate_mem I j) hz phi hbase (fun r => rfl)
  change Spec.map (CommRingCat.ofHom phi) ≫ chartι I j =
    Spec.map (CommRingCat.ofHom (linearNormalizedPointChartMapAt I x he
      (coordinate I j) (coordinate_mem I j) hz)) ≫ chartι I j
  rw [hphi]

theorem actualNativeChart_intrinsicQuadratic_mem_iff
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4)
    (phi : ChartRing I j →+* A)
    (hbase : phi.comp (chartBaseMap I j) = algebraMap K A)
    (Q : MvPolynomial (Fin 4) K) :
    Q ∈ intrinsicFullQuadraticSystem
      ((Spec.map (CommRingCat.ofHom phi) ≫ chartι I j) ≫ quotientProjMap I) ↔
      Q.IsHomogeneous 2 ∧
        phi (Q.eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0 := by
  rw [actualNativeChart_algebraPoint_eq_normalized I j phi hbase]
  rw [normalizedFiniteEquationPoint_intrinsicQuadratics_eq_evaluationKernel
    I _ (X j) (isHomogeneous_X K j) _ _ j 1
      (actualNativeChart_coordinates_normalized I j phi).symm]
  rw [mem_homogeneousVanishingPolynomialSubmodule_iff]
  rw [hom_eval₂, hbase]

end PfaffianDescent
