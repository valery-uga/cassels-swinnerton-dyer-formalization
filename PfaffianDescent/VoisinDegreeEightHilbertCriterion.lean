import PfaffianDescent.VoisinQuadraticPencilHilbertDetection
import PfaffianDescent.VoisinDegreeTenResidualEnd
import PfaffianDescent.VoisinDegreeEightCommonCurveWitness
import PfaffianDescent.VoisinGenericQuadraticDetection

/-!
# Hilbert criterion for Voisin's degree-eight quadratic pencil

This file restates the last no-fixed-curve input in the exact eventual
Hilbert-function form supplied by the graded calculation.  It is equivalent
to the regular-pair interface already consumed by the degree-four residual
construction.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The quadratic system through a degree-eight datum contains a
cubic--quadric--quadric pair whose homogeneous quotient has eventual
Hilbert function bounded by the expected length twelve. -/
def DegreeEightQuadraticHilbertBoundPairExists
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
  Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
  ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2),
    q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
    q ≠ 0 ∧ IsRelPrime p q ∧
    ∃ (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2),
      r.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        Module.finrank K (tripleCompleteIntersectionComponent p q r n) ≤ 12

/-- The source-faithful selected-coordinate form of the last degree-eight
input.  It records one normalized affine presentation and one pair from its
quadratic pencil, rather than asking for a suitable pair in every coordinate
presentation. -/
def DegreeEightSelectedQuadraticHilbertData
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
      (ell : MvPolynomial (Fin 4) K),
    Function.Surjective
        (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧
      ell.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
      ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2),
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
          q ≠ 0 ∧ IsRelPrime p q ∧
          ∃ (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2),
            r.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
              ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
                Module.finrank K
                  (tripleCompleteIntersectionComponent p q r n) ≤ 12

/-- The final condition specialized to the canonical basis of one normalized
quadratic pencil.  All coordinate and kernel facts are recorded; the only
geometric clause is the eventual Hilbert bound for the two displayed basis
quadrics. -/
def DegreeEightNormalizedPencilBasisHilbertData
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
      (ell : MvPolynomial (Fin 4) K),
    Function.Surjective
        (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧
      ell.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
      ∃ hker : Module.finrank K (LinearMap.ker
          (homogeneousSectionRestriction (K := K) x 2)) = 2,
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          Module.finrank K (tripleCompleteIntersectionComponent p
            (quadraticVanishingPencilBasis x hker 0).1.1
            (quadraticVanishingPencilBasis x hker 1).1.1 n) ≤ 12

/-- The sole geometric condition left on a packaged normalized pencil. -/
def NormalizedQuadraticPencilBasisData.HasEventualHilbertBound
    {A : Type u} [CommRing A] [Algebra K A] [FiniteDimensional K A]
    {p : MvPolynomial (Fin 4) K}
    (d : NormalizedQuadraticPencilBasisData K A p) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    Module.finrank K (tripleCompleteIntersectionComponent p
      (quadraticVanishingPencilBasis d.x d.kernelFinrank 0).1.1
      (quadraticVanishingPencilBasis d.x d.kernelFinrank 1).1.1 n) ≤ 12

/-- The algebraic form of the no-fixed-curve condition for the canonical
basis of a normalized quadratic pencil: the second basis quadric is a
non-zero-divisor modulo the cubic and the first basis quadric. -/
def NormalizedQuadraticPencilBasisData.HasCanonicalRegularPair
    {A : Type u} [CommRing A] [Algebra K A] [FiniteDimensional K A]
    {p : MvPolynomial (Fin 4) K}
    (d : NormalizedQuadraticPencilBasisData K A p) : Prop :=
  ∀ f : MvPolynomial (Fin 4) K,
    (quadraticVanishingPencilBasis d.x d.kernelFinrank 1).1.1 * f ∈
        Ideal.span ({p,
          (quadraticVanishingPencilBasis d.x d.kernelFinrank 0).1.1} :
            Set (MvPolynomial (Fin 4) K)) →
      f ∈ Ideal.span ({p,
        (quadraticVanishingPencilBasis d.x d.kernelFinrank 0).1.1} :
          Set (MvPolynomial (Fin 4) K))

/-- For a prime cubic, the sole eventual-Hilbert condition on a normalized
canonical pencil is equivalent to regularity of its two displayed basis
quadrics modulo the cubic. -/
theorem NormalizedQuadraticPencilBasisData.hasEventualHilbertBound_iff_regular
    {A : Type u} [CommRing A] [Algebra K A] [FiniteDimensional K A]
    {p : MvPolynomial (Fin 4) K}
    (d : NormalizedQuadraticPencilBasisData K A p)
    (hp : p.IsHomogeneous 3) (hpprime : Prime p) :
    d.HasEventualHilbertBound ↔ d.HasCanonicalRegularPair := by
  let q := (quadraticVanishingPencilBasis d.x d.kernelFinrank 0).1.1
  let r := (quadraticVanishingPencilBasis d.x d.kernelFinrank 1).1.1
  have hq : q.IsHomogeneous 2 := (d.basisData 0).1
  have hr : r.IsHomogeneous 2 := (d.basisData 1).1
  have hq0 : q ≠ 0 := by
    intro hzero
    apply (quadraticVanishingPencilBasis_linearIndependent
      d.x d.kernelFinrank).ne_zero 0
    apply Subtype.ext
    apply Subtype.ext
    exact hzero
  have hrel : IsRelPrime p q :=
    isRelPrime_of_prime_homogeneous_degree_lt hp hq hpprime hq0 (by decide)
  exact (cubic_two_quadrics_regular_iff_eventually_finrank_le_twelve
    p q r hp hq hr hpprime.ne_zero hq0 hrel).symm

/-- Failure of canonical regularity produces the literal fixed-component
obstruction for that canonical pencil.  One associated prime of `(p,q₀)`
contains `q₁`; since `q₀,q₁` are a basis of the full quadratic restriction
kernel, it contains every homogeneous quadric vanishing on the datum. -/
theorem NormalizedQuadraticPencilBasisData.exists_associatedPrime_containing_pencil_of_not_regular
    {A : Type u} [CommRing A] [Algebra K A] [FiniteDimensional K A]
    {p : MvPolynomial (Fin 4) K}
    (d : NormalizedQuadraticPencilBasisData K A p)
    (hnot : ¬ d.HasCanonicalRegularPair) :
    let q₀ := (quadraticVanishingPencilBasis d.x d.kernelFinrank 0).1.1
    let q₁ := (quadraticVanishingPencilBasis d.x d.kernelFinrank 1).1.1
    let I := Ideal.span ({p, q₀} : Set (MvPolynomial (Fin 4) K))
    ∃ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
        (MvPolynomial (Fin 4) K ⧸ I),
      Ideal.Quotient.mk I q₁ ∈ P ∧
      ∀ s ∈ homogeneousVanishingPolynomialSubmodule
          (K := K) (A := A) (sigma := Fin 4) d.x 2,
        Ideal.Quotient.mk I s ∈ P := by
  classical
  let q₀ := (quadraticVanishingPencilBasis d.x d.kernelFinrank 0).1.1
  let q₁ := (quadraticVanishingPencilBasis d.x d.kernelFinrank 1).1.1
  let I := Ideal.span ({p, q₀} : Set (MvPolynomial (Fin 4) K))
  dsimp only
  have hnotreg : Ideal.Quotient.mk I q₁ ∉
      nonZeroDivisors (MvPolynomial (Fin 4) K ⧸ I) := by
    intro hreg
    apply hnot
    intro f hf
    have hz : Ideal.Quotient.mk I q₁ * Ideal.Quotient.mk I f = 0 := by
      rw [← (Ideal.Quotient.mk I).map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hf
    have hfzero : Ideal.Quotient.mk I f = 0 :=
      (mul_left_mem_nonZeroDivisors_eq_zero_iff hreg).mp hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp hfzero
  have hmem : Ideal.Quotient.mk I q₁ ∈
      ⋃ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
        (MvPolynomial (Fin 4) K ⧸ I),
          (P : Set (MvPolynomial (Fin 4) K ⧸ I)) := by
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
    exact hnotreg
  obtain ⟨P, hP, hq₁P⟩ := Set.mem_iUnion₂.mp hmem
  refine ⟨P, hP, hq₁P, ?_⟩
  intro s hs
  obtain ⟨hshom, hsval⟩ :=
    (mem_homogeneousVanishingPolynomialSubmodule_iff
      (K := K) (A := A) (sigma := Fin 4) d.x 2 s).mp hs
  let sk : LinearMap.ker
      (homogeneousSectionRestriction (K := K) d.x 2) :=
    ⟨⟨s, hshom⟩, by
      rw [LinearMap.mem_ker, homogeneousSectionRestriction_apply]
      exact hsval⟩
  have hexp := quadraticVanishingPencilBasis_sum_repr
    d.x d.kernelFinrank sk
  have hbasisP : ∀ i : Fin 2,
      Ideal.Quotient.mk I
          (quadraticVanishingPencilBasis d.x d.kernelFinrank i).1.1 ∈ P := by
    intro i
    fin_cases i
    · rw [Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (by simp [q₀]))]
      exact P.zero_mem
    · simpa [q₁] using hq₁P
  have hsumP : Ideal.Quotient.mk I
      (∑ i, ((quadraticVanishingPencilBasis d.x d.kernelFinrank).repr sk i) •
        (quadraticVanishingPencilBasis d.x d.kernelFinrank i).1.1) ∈ P := by
    rw [map_sum]
    apply P.sum_mem
    intro i hi
    rw [smul_eq_C_mul, map_mul]
    exact P.mul_mem_left _ (hbasisP i)
  have hpoly :
      (∑ i, ((quadraticVanishingPencilBasis d.x d.kernelFinrank).repr sk i) •
        (quadraticVanishingPencilBasis d.x d.kernelFinrank i).1.1) = s := by
    exact congrArg (fun z => z.1.1) hexp
  rw [hpoly] at hsumP
  exact hsumP

/-- A packaged normalized pencil plus its sole remaining Hilbert condition
gives the datum consumed by the final residual endpoint. -/
theorem NormalizedQuadraticPencilBasisData.normalizedHilbertData
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (d : letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) :=
          D₈.property.1
        letI := finiteSchemeCoefficientAlgebra
          (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
        NormalizedQuadraticPencilBasisData
          K Γ(D₈.val.subscheme, ⊤) p)
    (hbound : letI : IsFinite (D₈.val.subschemeι ≫
          hypersurfaceToBase p hp) := D₈.property.1
        letI := finiteSchemeCoefficientAlgebra
          (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
        letI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
          finiteSchemeCoefficient_finite
            (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
        d.HasEventualHilbertBound) :
    DegreeEightNormalizedPencilBasisHilbertData p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  exact ⟨d.x, d.ell, d.evalSurjective, d.ellHomogeneous,
    d.ellEvaluation, d.cubicEvaluation, d.kernelFinrank, hbound⟩

/-- For a prime cubic, the normalized canonical-basis Hilbert condition is
exactly strong enough to supply the selected pair.  Basis independence gives
a nonzero first quadric, and the degree inequality `2 < 3` makes it relatively
prime to the cubic. -/
theorem DegreeEightNormalizedPencilBasisHilbertData.selectedHilbertData_of_prime
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpprime : Prime p)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (h : DegreeEightNormalizedPencilBasisHilbertData p hp D₈) :
    DegreeEightSelectedQuadraticHilbertData p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hx, hell, hxell, hpx, hker, hbound⟩ := h
  let q := (quadraticVanishingPencilBasis x hker 0).1.1
  let r := (quadraticVanishingPencilBasis x hker 1).1.1
  have hqdata := quadraticVanishingPencilBasis_data x hker 0
  have hrdata := quadraticVanishingPencilBasis_data x hker 1
  have hq0 : q ≠ 0 := by
    intro hzero
    apply (quadraticVanishingPencilBasis_linearIndependent x hker).ne_zero 0
    apply Subtype.ext
    apply Subtype.ext
    exact hzero
  have hrel : IsRelPrime p q :=
    isRelPrime_of_prime_homogeneous_degree_lt hp hqdata.1 hpprime hq0
      (by decide)
  exact ⟨x, ell, hx, hell, hxell, hpx,
    q, hqdata.1, hqdata.2, hq0, hrel,
    r, hrdata.1, hrdata.2, hbound⟩

/-- One normalized pencil satisfying the eventual Hilbert bound already
gives the degree-four cycle.  This is the narrow endpoint actually used by
Voisin's residual construction. -/
theorem DegreeEightSelectedQuadraticHilbertData.effectiveDegreeFourCycle
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (h : DegreeEightSelectedQuadraticHilbertData p hp D₈) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hx, hell, hxell, hpx,
    q, hq, hqvan, hq0, hrel, r, hr, hrvan, hbound⟩ := h
  have hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) :=
    regular_of_eventually_cubic_two_quadrics_finrank_le_twelve
      p q r hp hq hr hp0 hrel hbound
  exact
    finiteSubschemeDatum_degree_eight_complement_cycle_degree_four_of_selected_coordinates
      p q r hp hq hr hp0 hq0 hrel hregular D₈
      ⟨x, ell, hx, hell, hxell, hpx, hqvan, hrvan⟩

/-- The eventual Hilbert criterion supplies the regular pair used in
Voisin's residual construction. -/
theorem DegreeEightQuadraticHilbertBoundPairExists.regularPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (h : DegreeEightQuadraticHilbertBoundPairExists p hp D₈) :
    DegreeEightRegularQuadricPairExists p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx
  obtain ⟨q, hq, hqvan, hq0, hrel, r, hr, hrvan, hbound⟩ := h x hx
  refine ⟨q, hq, hqvan, hq0, hrel, r, hr, hrvan, ?_⟩
  exact regular_of_eventually_cubic_two_quadrics_finrank_le_twelve
    p q r hp hq hr hp0 hrel hbound

/-- A regular pair has eventual Hilbert function exactly twelve and hence
satisfies the Hilbert-bound formulation. -/
theorem DegreeEightRegularQuadricPairExists.hilbertBoundPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (h : DegreeEightRegularQuadricPairExists p hp D₈) :
    DegreeEightQuadraticHilbertBoundPairExists p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx
  obtain ⟨q, hq, hqvan, hq0, hrel, r, hr, hrvan, hregular⟩ := h x hx
  refine ⟨q, hq, hqvan, hq0, hrel, r, hr, hrvan, ?_⟩
  exact (cubic_two_quadrics_regular_iff_eventually_finrank_le_twelve
    p q r hp hq hr hp0 hq0 hrel).mp hregular

/-- Voisin's regular-pair input is exactly the eventual Hilbert-bound input. -/
theorem degreeEightQuadraticHilbertBoundPair_iff_regularPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) :
    DegreeEightQuadraticHilbertBoundPairExists p hp D₈ ↔
      DegreeEightRegularQuadricPairExists p hp D₈ := by
  constructor
  · exact DegreeEightQuadraticHilbertBoundPairExists.regularPair p hp hp0 D₈
  · exact DegreeEightRegularQuadricPairExists.hilbertBoundPair p hp hp0 D₈

/-- The eventual Hilbert bound is also exactly Voisin's source-faithful
no-common-curve condition.  This identifies the new graded criterion with
the geometric interface used by the fixed-component argument. -/
theorem degreeEightQuadraticHilbertBoundPair_iff_noCommonCurveComponent
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) :
    DegreeEightQuadraticHilbertBoundPairExists p hp D₈ ↔
      DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈ := by
  rw [degreeEightQuadraticHilbertBoundPair_iff_regularPair p hp hp0 D₈,
    degreeEightQuadraticSystem_hasNoCommonCurveComponent_iff_regularPair]

end PfaffianDescent
