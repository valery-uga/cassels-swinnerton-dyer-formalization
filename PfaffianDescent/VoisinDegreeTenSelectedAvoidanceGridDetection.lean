import PfaffianDescent.TripleHomogeneousNoIrrelevantAnnihilator
import PfaffianDescent.VoisinTwelvePointEvaluationFaithful
import AllCharacteristics.TwistedCubicLemma

/-! # Evaluation detects equations of a reduced regular triple intersection -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- Radical homogeneous membership gives inclusion of the actual ambient
kernel ideal sheaves when the native projective source is reduced. -/
theorem voisinDegreeTenSelectedAvoidance_hypersurface_kernel_le_of_radical
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    [IsReduced (scheme I)]
    (s : MvPolynomial (Fin 4) K) {d : ℕ} (hs : s.IsHomogeneous d)
    (hsrad : s ∈ I.toIdeal.radical) :
    (hypersurfaceToAmbient s hs).ker ≤ (quotientProjMap I).ker := by
  have hrange : Set.range (quotientProjMap I) ⊆
      Set.range (hypersurfaceToAmbient s hs) := by
    intro z hz
    rw [range_quotientProjMap] at hz
    change I.toIdeal ≤ z.asHomogeneousIdeal.toIdeal at hz
    change z ∈ Set.range (quotientProjMap (equationIdeal s hs))
    rw [quotientProjMap_mem_range_iff]
    change Ideal.span ({s} : Set (MvPolynomial (Fin 4) K)) ≤
      z.asHomogeneousIdeal.toIdeal
    apply Ideal.span_le.mpr
    rintro f (rfl : f = s)
    exact z.isPrime.radical_le_iff.mpr hz hsrad
  rw [closedImmersion_ker_eq_vanishingIdeal_support_of_reduced_source
    (quotientProjMap I)]
  apply Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
  change ((quotientProjMap I).ker.support : Set (Proj (homogeneousSubmodule (Fin 4) K))) ⊆
    ((hypersurfaceToAmbient s hs).ker.support : Set (Proj (homogeneousSubmodule (Fin 4) K)))
  rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker]
  exact closure_mono hrange

set_option backward.isDefEq.respectTransparency false in
/-- The actual reduced projective intersection and regular-sequence
saturation turn radical homogeneous membership into literal ideal membership.
The polynomial degrees are arbitrary. -/
theorem voisinDegreeTenSelectedAvoidance_mem_triple_of_radical
    {K : Type u} [Field K]
    (s f g h : MvPolynomial (Fin 4) K) {d a b c : ℕ}
    (hs : s.IsHomogeneous d) (hf : f.IsHomogeneous a)
    (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) (hrel : IsRelPrime f g)
    (hregular : ∀ F : MvPolynomial (Fin 4) K,
      h * F ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        F ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    [IsReduced (scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    (hsrad : s ∈ (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal.radical) :
    s ∈ Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh
  have hker := voisinDegreeTenSelectedAvoidance_hypersurface_kernel_le_of_radical
    I s hs hsrad
  apply triple_polynomials_mem_of_coordinate_localization_eq_zero
    s f g h hf0 hg0 hrel hregular
  intro j
  change algebraMap (CoordinateRing I)
    (Localization (Submonoid.powers (coordinate I j)))
    (Ideal.Quotient.mk I.toIdeal s) = 0
  apply localization_eq_zero_of_away_mk_eq_zero (grading I) (coordinate_mem I j) d
  · exact away_mk_eq_zero_of_hypersurface_ker_le_quotientProjMap_coordinate s hs I hker j
  · simpa using polynomial_class_mem_grading I s hs

set_option backward.isDefEq.respectTransparency false in
/-- A finite family covering the cone detects every positive-degree
homogeneous equation of an actual reduced regular triple intersection. -/
theorem voisinDegreeTenSelectedAvoidance_mem_triple_of_evaluations_zero
    {K : Type u} [Field K] [IsAlgClosed K]
    {ι : Type v} (x : ι → Fin 4 → K)
    (s f g h : MvPolynomial (Fin 4) K) {d a b c : ℕ}
    (hd : 0 < d) (hs : s.IsHomogeneous d) (hf : f.IsHomogeneous a)
    (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) (hrel : IsRelPrime f g)
    (hregular : ∀ F : MvPolynomial (Fin 4) K,
      h * F ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        F ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    [IsReduced (scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K
        (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal,
      y = 0 ∨ ∃ (i : ι) (t : K), y = t • x i)
    (hzero : ∀ i, MvPolynomial.aeval (x i) s = 0) :
    s ∈ Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)) := by
  apply voisinDegreeTenSelectedAvoidance_mem_triple_of_radical
    s f g h hs hf hg hh hf0 hg0 hrel hregular
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) (k := K)]
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro y hy
  rcases hcover y hy with h0 | ⟨i, t, ht⟩
  · subst y
    exact aeval_zero_eq_zero_of_homogeneous_pos s hs hd
  · rw [ht, QuarticNet.aeval_smul_of_homogeneous s d hs, hzero i, mul_zero]

end PfaffianDescent
