import PfaffianDescent.CorayActualComponentHilbertDegree
import AllCharacteristics.HomogeneousProjectiveAmbient

/-!
# Actual relevant prime component: construct hyperplane and degree without minwhole

A relevant actual homogeneous prime C containing original p/q defines an
actual projective point of the original intersection via its literal quotient
map. The genuine regular-pair finite-point selector chooses H avoiding that
actual point, hence H not in C. The actual triple Hilbert bound derives SAME
cut finiteness. This applies to geometric components minimal over the selected
prime's extension without assuming they are minimal over the whole p/q ideal.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Construct a regular original hyperplane avoiding the literal actual
relevant homogeneous prime C, through an OWN actual projective preimage point.
No minimality over the whole p/q ideal, Hnoncontainment or lift certificate. -/
theorem regularPair_relevantPrime_exists_regular_linear_not_mem
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K) {a b : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [C.toIdeal.IsPrime]
    (hCrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C)
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal) :
    ∃ (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1),
      (∀ y : MvPolynomial (Fin 4) K,
        H * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧ H ∉ C.toIdeal := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let c : ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K) := ⟨C, inferInstance, hCrel⟩
  obtain ⟨x, hx⟩ := (quotientProjMap_mem_range_iff I c).mpr hIC
  let point : PUnit.{1} → scheme I := fun _ => x
  obtain ⟨H, hH, hregular, havoid⟩ :=
    regular_pair_exists_linear_nonzerodivisor_avoiding_finite_projective_family
      p q hp hq hp0 hrel point
  refine ⟨H, hH, hregular, ?_⟩
  intro hHC
  apply havoid PUnit.unit
  have hpoint : H ∈ (quotientProjMap I x).asHomogeneousIdeal := by
    rw [hx]
    exact hHC
  change Ideal.Quotient.mk I.toIdeal H ∈ x.asHomogeneousIdeal at hpoint
  exact hpoint

/-- Every ACTUAL relevant homogeneous prime containing original smooth cubic/q
has a constructed finite hyperplane cut whose OWN native rank realizes its
intrinsic coordinate degree≤3n, with actual stabilized increments. No desired
finite/degree/Hilbert/minwhole certificate is supplied. -/
theorem selectedProjectiveRelevantPrime_exists_hyperplane_degree_bound
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [C.toIdeal.IsPrime]
    (hCrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C)
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal) :
    ∃ (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1), H ∉ C.toIdeal ∧
      ∃ hfinite : IsFinite (toBase (C ⊔ equationIdeal H hH)),
        letI := hfinite
        actualCurveCoordinateHilbertDegree C = finiteSchemeRank (toBase (C ⊔ equationIdeal H hH)) ∧
          actualCurveCoordinateHilbertDegree C ≤ 3 * n ∧ ∃ N : ℕ, ∀ m, N ≤ m →
            finrank K (grading C (m + 1)) = finrank K (grading C m) +
              actualCurveCoordinateHilbertDegree C := by
  classical
  have hq0 : q ≠ 0 := by
    intro hz
    apply hnot
    rw [hz]
    exact Ideal.zero_mem _
  have hrel := isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot
  obtain ⟨H, hH, hregular, hnotC⟩ :=
    regularPair_relevantPrime_exists_regular_linear_not_mem p q hp hq hp0 hrel C hCrel hIC
  have hfinite := selectedProjectiveComponent_regular_linearSection_isFinite
    p q H hp hq hH hp0 hq0 hrel hregular C hIC
  letI := hfinite
  obtain ⟨heq, N, hN⟩ := primeComponent_linearSection_degree_and_eventualIncrement C H hH hnotC
  obtain ⟨M, hM⟩ := finiteProjectiveHomogeneousIdeal_hilbertFunction_eventually_eq_rank
    (C ⊔ equationIdeal H hH)
  have hbound := selectedProjectiveComponent_regular_linearSection_hilbertBound
    p q H hp hq hH hp0 hq0 hrel hregular C hIC (max M (n + 4)) (le_max_right _ _)
  rw [hM (max M (n + 4)) (le_max_left _ _)] at hbound
  refine ⟨H, hH, hnotC, hfinite, heq, heq.trans_le hbound, N, ?_⟩
  intro m hm
  rw [heq]
  exact hN m hm

end PfaffianDescent.Coray
