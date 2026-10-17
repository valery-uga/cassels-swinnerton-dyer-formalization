import PfaffianDescent.VoisinSelectedIntrinsicFieldIdeal
import PfaffianDescent.VoisinGenericTripleFinite
import PfaffianDescent.VoisinIntrinsicIdealFiniteTransfer

/-! Finiteness of the intrinsic selected triple over the chart fraction field. -/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Finiteness on a neighborhood of the selected chart's generic point
implies finiteness of its intrinsic eight-point triple over the chart's
fraction field. -/
theorem selectedIntrinsicEightPointTriple_generic_isFinite_of_finiteNeighborhood
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    [IsDomain (Localization.Away (quadraticMinorDet m y))]
    (p : MvPolynomial (Fin 4)
      (Localization.Away (quadraticMinorDet m y)))
    (hp : p.IsHomogeneous 3)
    (V : (Spec (.of (Localization.Away (quadraticMinorDet m y)))).Opens)
    (hη : genericPoint
      (Spec (.of (Localization.Away (quadraticMinorDet m y)))) ∈ V)
    [IsFinite ((relativeTripleIntersectionToBase p
      (quadraticSelectedOpenPolynomial m y 0)
      (quadraticSelectedOpenPolynomial m y 1) hp
      (quadraticSelectedOpenPolynomial_isHomogeneous m y 0)
      (quadraticSelectedOpenPolynomial_isHomogeneous m y 1)) ∣_ V)] :
    let S := Localization.Away (quadraticMinorDet m y)
    let g := algebraMap S (FractionRing S)
    IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
      (p.map g) (hp.map g)
      (fun k j => g (algebraMap R S (y k j))))) := by
  dsimp only
  let S := Localization.Away (quadraticMinorDet m y)
  let g : S →+* FractionRing S := algebraMap S (FractionRing S)
  let f : R →+* FractionRing S := g.comp (algebraMap R S)
  have hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det := by
    have heq : (eightPointQuadraticEvaluationMinor m
        (fun k j => f (y k j))).det = f (quadraticMinorDet m y) := by
      change (eightPointQuadraticEvaluationMinor m
        (fun k j => f (y k j))).det =
        f (eightPointQuadraticEvaluationMinor m y).det
      rw [RingHom.map_det,
        RingHom.mapMatrix_apply, eightPointQuadraticEvaluationMinor_map]
    rw [heq]
    exact (IsLocalization.Away.algebraMap_isUnit (quadraticMinorDet m y)).map g
  have hgf : quadraticMinorSelectedPointLift m y f hm = g := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (quadraticMinorDet m y))
    rw [quadraticMinorSelectedPointLift_comp]
  let q₀ := quadraticSelectedOpenPolynomial m y 0
  let q₁ := quadraticSelectedOpenPolynomial m y 1
  haveI hfin : IsFinite (relativeTripleIntersectionToBase
      (p.map g) (q₀.map g) (q₁.map g)
      (hp.map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m y 0).map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m y 1).map g)) := by
    change IsFinite (toBase (relativeTripleIntersectionHomogeneousIdeal
      (p.map g) (q₀.map g) (q₁.map g)
      (hp.map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m y 0).map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m y 1).map g)))
    rw [relativeTripleIntersectionHomogeneousIdeal_eq_triple]
    exact relativeTripleIntersection_generic_isFinite_of_finiteNeighborhood
      p q₀ q₁ hp
      (quadraticSelectedOpenPolynomial_isHomogeneous m y 0)
      (quadraticSelectedOpenPolynomial_isHomogeneous m y 1) V hη
  have hEq := selectedIntrinsicEightPointTripleHomogeneousIdeal_eq_specializedFrame
    m y p hp f hm
  dsimp only at hEq
  rw [hgf] at hEq
  exact isFinite_toBase_of_eq_relativeTripleIdeal
    (p.map g) (q₀.map g) (q₁.map g)
    (hp.map g)
    ((quadraticSelectedOpenPolynomial_isHomogeneous m y 0).map g)
    ((quadraticSelectedOpenPolynomial_isHomogeneous m y 1).map g)
    (intrinsicEightPointTripleHomogeneousIdeal
      (p.map g) (hp.map g) (fun k j => f (y k j))) hEq

end PfaffianDescent
