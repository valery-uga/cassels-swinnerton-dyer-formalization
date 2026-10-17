import PfaffianDescent.CorayRelevantPrimeComponentHyperplaneDegree
import PfaffianDescent.CoraySelectedComponentHeightAndRelevance
import PfaffianDescent.CorayPolynomialComponentContraction
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridCurveNotFinite

/-! Actual selected curve degree positivity. Zero actual Hilbert increment
would make OWN projective structure finite, contradicting actual height-two
curve geometry. The original selected-minimal-prime condition also transports
to WHOLE original intersection minimality by derived coefficient contraction.
No degree positivity, dimension, finite/nonfinite or comparison certificate is
supplied to the selected-component caller. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Minimality of the ORIGINAL selected prime over J transports to every
actual minimal prime over its coefficient extension. Equal contraction and
the final minimality are derived internally, with the literal coefficient map. -/
theorem originalMinimalPrime_coefficientExtension_minimalPrime_over_wholeIdeal
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    (J I : Ideal (MvPolynomial (Fin 4) K)) [I.IsPrime]
    (hI : I ∈ J.minimalPrimes) (P : Ideal (MvPolynomial (Fin 4) E))
    (hP : P ∈ (I.map (MvPolynomial.map (algebraMap K E))).minimalPrimes) :
    P ∈ (J.map (MvPolynomial.map (algebraMap K E))).minimalPrimes := by
  let f := MvPolynomial.map (σ := Fin 4) (algebraMap K E)
  have hcontract : P.comap f = I :=
    polynomialCoefficientExtension_minimalPrime_comap_eq I P hP
  refine ⟨⟨hP.isPrime, (Ideal.map_mono hI.le).trans hP.le⟩, ?_⟩
  intro Q hQ hQP
  have hQI : Q.comap f ≤ I := by
    rw [← hcontract]
    exact Ideal.comap_mono hQP
  have hJQ : J ≤ Q.comap f := Ideal.map_le_iff_le_comap.mp hQ.2
  have hIQ : I ≤ Q.comap f := hI.2 ⟨hQ.1.comap f, hJQ⟩ hQI
  exact hP.2 ⟨hQ.1, Ideal.map_le_iff_le_comap.mpr hIQ⟩ hQP

/-- An ACTUAL height-two prime component containing original cubic/q has
positive OWN coordinate degree. Its increment and nonfiniteness are derived
from actual hyperplane selection and actual curve geometry, respectively. -/
theorem selectedHeightTwoPrimeComponent_hilbertDegree_pos
    {K : Type u} [Field K] [IsAlgClosed K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [C.toIdeal.IsPrime]
    (hCheight : C.toIdeal.height = 2)
    (hPQC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal) :
    0 < actualCurveCoordinateHilbertDegree C := by
  classical
  have hCrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C :=
    PfaffianDescent.homogeneousIdeal_relevant_of_height_le_two C hCheight.le
  obtain ⟨_H, _hH, _hnotH, _hfiniteH, _hdegreeH, _hboundH, N, hN⟩ :=
    selectedProjectiveRelevantPrime_exists_hyperplane_degree_bound
      p q hp hp0 n hq hnot C hCrel hPQC
  by_contra hpos
  have hzero : actualCurveCoordinateHilbertDegree C = 0 := by omega
  have hconstant : ∀ t : ℕ, finrank K (grading C (N + t)) = finrank K (grading C N) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hstep := hN (N + t) (by omega)
      rw [hzero, Nat.add_zero] at hstep
      have hindex : finrank K (grading C (N + Nat.succ t)) =
          finrank K (grading C (N + t + 1)) :=
        (congrArg (fun d => finrank K (grading C d)) (Nat.add_assoc N t 1)).symm
      exact hindex.trans (hstep.trans ih)
  have hfinite : IsFinite (toBase C) :=
    PfaffianDescent.projective_finite_of_hilbert_bound C N (finrank K (grading C N)) (by
      intro m hm
      have hindex : N + (m - N) = m := by omega
      have hdim := congrArg (fun d => finrank K (grading C d)) hindex
      exact (hdim.symm.trans (hconstant (m - N))).le)
  exact PfaffianDescent.voisinDegreeTenSelectedAvoidance_heightTwoPrime_not_finite_algClosed
    C inferInstance hCheight hfinite

/-- The actual selected minimal component's height is constructed from the
original equations, so degree positivity is NOT a supplied height/dimension
or nonfiniteness premise. Degree remains that component's OWN, possibly <3n. -/
theorem selectedProjectiveMinimalComponent_hilbertDegree_pos
    {K : Type u} [Field K] [IsAlgClosed K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hC : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    0 < actualCurveCoordinateHilbertDegree C := by
  letI : C.toIdeal.IsPrime := hC.isPrime
  exact selectedHeightTwoPrimeComponent_hilbertDegree_pos
    p q hp hp0 n hq hnot C
    (selectedProjectiveMinimalComponent_homogeneous_height_eq_two p q hp hp0 n hq hnot C hC) hC.le

end PfaffianDescent.Coray
