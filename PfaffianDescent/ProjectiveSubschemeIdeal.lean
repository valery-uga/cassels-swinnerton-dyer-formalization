import PfaffianDescent.FiniteProjectiveChart
import PfaffianDescent.LinearChartCoordinates
import PfaffianDescent.HomogeneousChartPrime
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [CommRing K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def polynomialQuotientGradedHom
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) :
    MvPolynomial.homogeneousSubmodule σ K →+*ᵍ grading I where
  __ := Ideal.Quotient.mk I.toIdeal
  map_mem := by
    intro d f hf
    exact polynomial_class_mem_grading I f hf

/-- The homogeneous vanishing ideal of the actual image of a projective
subscheme, contracted to the original polynomial ring. For reduced subschemes
this records their equations without nilpotent thickening. -/
noncomputable def projectiveSubschemeIdeal
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K) :=
  (ProjectiveSpectrum.vanishingIdeal (Set.range i)).comap (polynomialQuotientGradedHom I)

lemma mem_projectiveSubschemeIdeal
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) (f : MvPolynomial σ K) :
    f ∈ projectiveSubschemeIdeal I i ↔
      ∀ x : Z, Ideal.Quotient.mk I.toIdeal f ∈ (i x).asHomogeneousIdeal := by
  change Ideal.Quotient.mk I.toIdeal f ∈ ProjectiveSpectrum.vanishingIdeal (Set.range i) ↔ _
  rw [ProjectiveSpectrum.mem_vanishingIdeal]
  exact ⟨fun h x => h (i x) (Set.mem_range_self x), fun h _ ⟨x, hx⟩ => hx ▸ h x⟩

/-- In a linear chart, reducedness converts vanishing at every scheme point
into equality to zero in the actual global-section ring. -/
theorem projectiveSubschemeIdeal_chart_membership
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    {Z : Scheme.{u}} [IsAffine Z] [AlgebraicGeometry.IsReduced Z]
    (i : Z ⟶ scheme I) (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (g : Away (grading I) z →+* Γ(Z, ⊤))
    (hg : Spec.map (CommRingCat.ofHom g) ≫ Proj.awayι (grading I) z hz (by decide : 0 < 1) =
      Z.isoSpec.inv ≫ i)
    (f : MvPolynomial σ K) {d : ℕ} (hf : f.IsHomogeneous d) :
    f ∈ projectiveSubschemeIdeal I i ↔
      g (f.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
        (linearChartCoordinate I z hz)) = 0 := by
  rw [mem_projectiveSubschemeIdeal, eval₂_linearChartCoordinate_eq_fraction I z hz f hf]
  let a := Away.mk (grading I) hz d (Ideal.Quotient.mk I.toIdeal f)
    (by simpa using polynomial_class_mem_grading I f hf)
  have hq (q : Spec Γ(Z, ⊤)) :
      Ideal.Quotient.mk I.toIdeal f ∈ (i (Z.isoSpec.inv q)).asHomogeneousIdeal ↔
        g a ∈ q.asIdeal := by
    have hpt := congrArg (fun k => k q) hg
    change Proj.awayι (grading I) z hz (by decide : 0 < 1)
      (Spec.map (CommRingCat.ofHom g) q) = i (Z.isoSpec.inv q) at hpt
    rw [← hpt]
    exact homogeneousChart_prime_membership (grading I) z hz
      (Spec.map (CommRingCat.ofHom g) q) d (Ideal.Quotient.mk I.toIdeal f)
      (polynomial_class_mem_grading I f hf)
  constructor
  · intro h
    apply IsNilpotent.eq_zero
    apply nilpotent_iff_mem_prime.mpr
    intro P hP
    exact (hq ⟨P, hP⟩).mp (h _)
  · intro h x
    let q := Z.isoSpec.hom x
    have hx : Z.isoSpec.inv q = x := congrArg (fun k => k x) Z.isoSpec.hom_inv_id
    rw [← hx]
    apply (hq q).mpr
    change g a = 0 at h
    rw [h]
    exact Ideal.zero_mem _

end
end PfaffianDescent
