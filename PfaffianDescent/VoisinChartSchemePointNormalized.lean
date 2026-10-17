import PfaffianDescent.VoisinChartFieldNormalizedPoint

/-! A field-valued scheme point of an affine Proj chart has normalized coordinates. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Reconstruct the normalized homogeneous vector directly from a
field-valued scheme point of an affine Proj chart. -/
theorem chartSchemePoint_normalizedPointAt
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (hellz : Ideal.Quotient.mk I.toIdeal ell = z)
    (a : Spec (.of F) ⟶ Spec (.of (Away (grading I) z)))
    (hbase : (Spec.preimage a).hom.comp
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
        algebraMap K F) :
    let x : Fin 4 → F := fun j =>
      (Spec.preimage a).hom (linearChartCoordinate I z hz j)
    ell.eval₂ (algebraMap K F) x = 1 ∧
    ∃ (he : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap K F) x = 0),
    ∃ (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K F) x) he) z = 1),
      linearNormalizedPointAt I x he z hz hzOne =
        a ≫ Proj.awayι (grading I) z hz (by decide : 0 < 1) := by
  have hmap : Spec.map (CommRingCat.ofHom (Spec.preimage a).hom) = a := by
    change Spec.map (Spec.preimage a) = a
    exact Spec.map_preimage a
  obtain ⟨hnorm, he, hzOne, hpoint⟩ :=
    chartFieldPoint_normalizedPointAt I z hz ell hell hellz
      (Spec.preimage a).hom hbase
  exact ⟨hnorm, he, hzOne, hpoint.trans (by rw [hmap])⟩

end PfaffianDescent
