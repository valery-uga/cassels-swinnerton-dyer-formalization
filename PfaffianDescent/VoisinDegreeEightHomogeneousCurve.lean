import PfaffianDescent.VoisinDegreeEightCommonCurveWitness
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import PfaffianDescent.CubicFiniteSubschemeHyperplane

/-!
# Projective support of the degree-eight common-curve witness

The residual-end algebra produces a homogeneous prime ideal containing the
quadratic vanishing system.  This module records its precise projective
interpretation once relevance has been established: it gives an actual point
of projective spectrum at which every member of that system vanishes.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every proper homogeneous ideal in a polynomial ring over a field is
contained in the irrelevant ideal.  Its degree-zero component cannot contain
a nonzero constant, since such a constant is a unit. -/
theorem homogeneousIdeal_le_irrelevant_of_ne_top
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hne : I.toIdeal ≠ ⊤) :
    I ≤ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) := by
  intro f hf
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
  change ((decomposition.decompose' f 0 :
    MvPolynomial.homogeneousSubmodule (Fin 4) K 0) :
      MvPolynomial (Fin 4) K) = 0
  rw [MvPolynomial.decomposition.decompose'_apply,
    MvPolynomial.homogeneousComponent_zero, MvPolynomial.C_eq_zero]
  have hc_mem : MvPolynomial.homogeneousComponent 0 f ∈ I.toIdeal := by
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact I.isHomogeneous 0 hf
  rw [MvPolynomial.homogeneousComponent_zero] at hc_mem
  by_contra hc
  have huK : IsUnit (MvPolynomial.coeff 0 f) := isUnit_iff_ne_zero.mpr hc
  have huC : IsUnit (MvPolynomial.C (MvPolynomial.coeff 0 f) :
      MvPolynomial (Fin 4) K) := huK.map MvPolynomial.C
  exact hne (I.toIdeal.eq_top_of_isUnit_mem hc_mem huC)

/-- A relevant homogeneous prime ideal determines a projective point with
exactly that homogeneous ideal. -/
noncomputable def homogeneousPrimeIdeal_projectivePoint
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C) :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
  ⟨C, hprime, hrelevant⟩

/-- A strict height gap from the irrelevant ideal proves projective
relevance.  This isolates the commutative-algebra calculation needed for the
complete-intersection associated-prime witness. -/
theorem homogeneousIdeal_relevant_of_height_lt_irrelevant
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hheight : C.toIdeal.height <
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 4) K)).toIdeal.height) :
    ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C := by
  intro hle
  exact (not_le_of_gt hheight) (Ideal.height_mono hle)

/-- In four homogeneous variables, an ideal of height strictly below four
cannot contain the irrelevant ideal.  This form is useful after cutting the
height-two fixed curve by one additional homogeneous equation: the resulting
height-three ideal still has nonempty projective support. -/
theorem homogeneousIdeal_relevant_of_height_lt_four
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hheight : C.toIdeal.height < 4) :
    ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C := by
  intro hle
  have hvars : MvPolynomial.idealOfVars (Fin 4) K ≤ C.toIdeal := by
    rw [MvPolynomial.idealOfVars]
    apply Ideal.span_le.mpr
    rintro f ⟨j, rfl⟩
    exact hle (HomogeneousIdeal.mem_irrelevant_of_mem
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) (by decide : 0 < 1)
      (isHomogeneous_X K j))
  have hfour : (4 : ℕ∞) ≤ C.toIdeal.height :=
    (four_le_height_idealOfVars (K := K)).trans (Ideal.height_mono hvars)
  exact (not_le_of_gt hheight) hfour

/-- A height-at-most-three homogeneous ideal in four variables is still
projectively relevant.  This is the hyperplane-section version of the
height-two relevance lemma below. -/
theorem homogeneousIdeal_relevant_of_height_le_three
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hheight : C.toIdeal.height ≤ 3) :
    ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C := by
  apply homogeneousIdeal_relevant_of_height_lt_four C
  exact lt_of_le_of_lt hheight (by norm_num)

/-- In four variables, every homogeneous ideal of height at most two is
projectively relevant.  The coordinate chain gives height at least four for
the irrelevant ideal. -/
theorem homogeneousIdeal_relevant_of_height_le_two
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hheight : C.toIdeal.height ≤ 2) :
    ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C := by
  intro hle
  have hvars : MvPolynomial.idealOfVars (Fin 4) K ≤ C.toIdeal := by
    rw [MvPolynomial.idealOfVars]
    apply Ideal.span_le.mpr
    rintro f ⟨j, rfl⟩
    exact hle (HomogeneousIdeal.mem_irrelevant_of_mem
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) (by decide : 0 < 1)
      (isHomogeneous_X K j))
  have hfour : (4 : ℕ∞) ≤ C.toIdeal.height :=
    (four_le_height_idealOfVars (K := K)).trans (Ideal.height_mono hvars)
  have : (4 : ℕ∞) ≤ 2 := hfour.trans hheight
  norm_num at this

/-- A homogeneous system contained in a relevant homogeneous prime ideal
vanishes at the corresponding projective point. -/
theorem homogeneousVanishingSystem_vanishes_at_projectivePoint_of_le_prime
    {K : Type u} [Field K]
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C)
    (hW : W ≤ Submodule.restrictScalars K C.toIdeal) :
    ∃ x : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) K),
      ∀ f : MvPolynomial (Fin 4) K, f ∈ W → f ∈ x.asHomogeneousIdeal.toIdeal := by
  let x := homogeneousPrimeIdeal_projectivePoint C hprime hrelevant
  refine ⟨x, ?_⟩
  intro f hf
  exact hW hf

end PfaffianDescent

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The residual-end associated-prime witness is projectively relevant if each
homogeneous prime supplied by the witness avoids the irrelevant ideal.  This
is the remaining geometric content needed to turn a common curve component
into an actual projective fixed curve. -/
def DegreeEightHomogeneousCurveWitnessesRelevant
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
    Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
    ∀ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2),
      q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
      q ≠ 0 → IsRelPrime p q →
      ∀ (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)),
        C.toIdeal.IsPrime →
        Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal →
        homogeneousVanishingPolynomialSubmodule
          (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
          Submodule.restrictScalars K C.toIdeal →
        ¬ HomogeneousIdeal.irrelevant
          (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C

/-- Under projective relevance, failure of the no-common-curve condition
produces a literal projective point carrying every quadric through the
rank-eight datum, as well as the cubic and chosen first quadric. -/
theorem degreeEight_exists_projectiveCommonCurveWitness_of_not_noCommonCurveComponent
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcommon : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈)
    (hrelevant : DegreeEightHomogeneousCurveWitnessesRelevant p hp D₈) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      ∀ (q : MvPolynomial (Fin 4) K) (_hq : q.IsHomogeneous 2),
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
        q ≠ 0 → IsRelPrime p q →
        ∃ z : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) K),
          Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤
            z.asHomogeneousIdeal.toIdeal ∧
          homogeneousVanishingPolynomialSubmodule
              (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
            Submodule.restrictScalars K z.asHomogeneousIdeal.toIdeal := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hx, hwitness⟩ :=
    degreeEight_exists_homogeneousPrimeCurveIdealWitness_of_not_noCommonCurveComponent
      p hp D₈ hcommon
  refine ⟨x, hx, ?_⟩
  intro q hq hqvan hq0 hrel
  obtain ⟨C, hprime, hspan, hW⟩ := hwitness q hq hqvan hq0 hrel
  have hCrel : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C :=
    hrelevant x hx q hq hqvan hq0 hrel C hprime hspan hW
  let z := homogeneousPrimeIdeal_projectivePoint C hprime hCrel
  refine ⟨z, ?_, ?_⟩
  · exact hspan
  · exact hW

end PfaffianDescent

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Height-two control for every homogeneous associated-prime curve witness.
For a regular cubic--quadric complete intersection this is precisely the
unmixedness statement still needed from commutative algebra. -/
def DegreeEightHomogeneousCurveWitnessesHeightLeTwo
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
    Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
    ∀ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2),
      q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
      q ≠ 0 → IsRelPrime p q →
      ∀ (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)),
        C.toIdeal.IsPrime →
        Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal →
        homogeneousVanishingPolynomialSubmodule
          (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
          Submodule.restrictScalars K C.toIdeal →
        C.toIdeal.height ≤ 2

/-- The height-two complete-intersection bound implies projective relevance
of every residual-end common-curve witness. -/
theorem DegreeEightHomogeneousCurveWitnessesRelevant.ofHeightLeTwo
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hheight : DegreeEightHomogeneousCurveWitnessesHeightLeTwo p hp D₈) :
    DegreeEightHomogeneousCurveWitnessesRelevant p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx q hq hqvan hq0 hrel C hprime hspan hW
  exact homogeneousIdeal_relevant_of_height_le_two C
    (hheight x hx q hq hqvan hq0 hrel C hprime hspan hW)

end PfaffianDescent

namespace PfaffianDescent

open MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous prime that is minimal over a cubic and a quadric has height
at most two.  This is the Krull-height part of the needed unmixedness bridge. -/
theorem homogeneousPrime_height_le_two_of_mem_minimalPrimes_span_pair
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hminimal : C.toIdeal ∈ (Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) K))).minimalPrimes) :
    C.toIdeal.height ≤ 2 := by
  have hcard : ({p, q} : Set (MvPolynomial (Fin 4) K)).ncard ≤ 2 := by
    calc
      ({p, q} : Set (MvPolynomial (Fin 4) K)).ncard =
          (Set.insert p ({q} : Set (MvPolynomial (Fin 4) K))).ncard := rfl
      _ ≤ ({q} : Set (MvPolynomial (Fin 4) K)).ncard + 1 :=
        Set.ncard_insert_le p {q}
      _ = 2 := by simp
  have hheight := Ideal.height_le_card_of_mem_minimalPrimes_span
    (s := ({p, q} : Set (MvPolynomial (Fin 4) K)))
    ((Set.finite_singleton q).insert p) hminimal
  exact hheight.trans (by exact_mod_cast hcard)

end PfaffianDescent

namespace PfaffianDescent

open MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous prime minimal over a cubic--quadric ideal is relevant in
projective three-space. -/
theorem homogeneousPrime_relevant_of_mem_minimalPrimes_span_pair
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hminimal : C.toIdeal ∈ (Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) K))).minimalPrimes) :
    ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C := by
  exact homogeneousIdeal_relevant_of_height_le_two C
    (homogeneousPrime_height_le_two_of_mem_minimalPrimes_span_pair p q C hminimal)

end PfaffianDescent

namespace PfaffianDescent

open MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Krull's height bound for an arbitrary ideal minimal over a cubic and a
quadric.  Homogeneity is not needed for this commutative-algebra step. -/
theorem ideal_height_le_two_of_mem_minimalPrimes_span_pair
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K)
    (J : Ideal (MvPolynomial (Fin 4) K))
    (hminimal : J ∈ (Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) K))).minimalPrimes) :
    J.height ≤ 2 := by
  have hcard : ({p, q} : Set (MvPolynomial (Fin 4) K)).ncard ≤ 2 := by
    calc
      ({p, q} : Set (MvPolynomial (Fin 4) K)).ncard =
          (Set.insert p ({q} : Set (MvPolynomial (Fin 4) K))).ncard := rfl
      _ ≤ ({q} : Set (MvPolynomial (Fin 4) K)).ncard + 1 :=
        Set.ncard_insert_le p {q}
      _ = 2 := by simp
  have hheight := Ideal.height_le_card_of_mem_minimalPrimes_span
    (s := ({p, q} : Set (MvPolynomial (Fin 4) K)))
    ((Set.finite_singleton q).insert p) hminimal
  exact hheight.trans (by exact_mod_cast hcard)

/-- Minimal primes descend through the quotient by a cubic--quadric ideal. -/
theorem comap_mem_minimalPrimes_span_pair_of_quotient_mem_minimalPrimes
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) K))))
    (hP : P ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))).minimalPrimes) :
    P.comap (Ideal.Quotient.mk (Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) K)))) ∈
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes := by
  have h := Ideal.minimalPrimes_comap_of_surjective
    (f := Ideal.Quotient.mk (Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) K)))) Ideal.Quotient.mk_surjective hP
  simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using h

/-- A homogeneous ideal below the pullback of a quotient-minimal prime over a
cubic and quadric is projectively relevant. -/
theorem homogeneousIdeal_relevant_of_le_quotientMinimalPrime_span_pair
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) K))))
    (hP : P ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))).minimalPrimes)
    (hC : C.toIdeal ≤ P.comap (Ideal.Quotient.mk (Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))) :
    ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C := by
  apply homogeneousIdeal_relevant_of_height_le_two C
  calc
    C.toIdeal.height ≤ (P.comap (Ideal.Quotient.mk (Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K))))).height :=
      Ideal.height_mono hC
    _ ≤ 2 := ideal_height_le_two_of_mem_minimalPrimes_span_pair p q _
      (comap_mem_minimalPrimes_span_pair_of_quotient_mem_minimalPrimes p q P hP)

end PfaffianDescent

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The specific unmixedness statement needed for the degree-eight residual
argument. -/
def CubicQuadricQuotientAssociatedPrimesMinimal
    (p : MvPolynomial (Fin 4) K) : Prop :=
  ∀ (q : MvPolynomial (Fin 4) K), q.IsHomogeneous 2 → q ≠ 0 → IsRelPrime p q →
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set
        (MvPolynomial (Fin 4) K))),
      P ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K)))).minimalPrimes

theorem degreeEight_exists_projectiveCommonCurveWitness_of_associatedPrimesMinimal
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcommon : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈)
    (hunmixed : CubicQuadricQuotientAssociatedPrimesMinimal p) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      ∀ (q : MvPolynomial (Fin 4) K) (_hq : q.IsHomogeneous 2),
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
        q ≠ 0 → IsRelPrime p q →
        ∃ z : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) K),
          Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤
            z.asHomogeneousIdeal.toIdeal ∧
          homogeneousVanishingPolynomialSubmodule
              (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
            Submodule.restrictScalars K z.asHomogeneousIdeal.toIdeal := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hx, hwitness⟩ :=
    degreeEight_exists_associatedPrime_commonCurveWitness_of_not_noCommonCurveComponent
      p hp D₈ hcommon
  refine ⟨x, hx, ?_⟩
  intro q hq hqvan hq0 hrel
  obtain ⟨P, hP, hcontains⟩ := hwitness q hq hqvan hq0 hrel
  let I := P.comap (Ideal.Quotient.mk
    (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))))
  let C := I.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  have hspanI : Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ I :=
    (associatedPrimeComap_isPrime_and_contains_span p q P hP).1
  have hprimeI : I.IsPrime :=
    (associatedPrimeComap_isPrime_and_contains_span p q P hP).2
  have hCprime : C.toIdeal.IsPrime := hprimeI.homogeneousCore
  have hpI : p ∈ I := hspanI (Ideal.subset_span (by simp))
  have hqI : q ∈ I := hspanI (Ideal.subset_span (by simp))
  have hpC : p ∈ C.toIdeal :=
    Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (SetLike.isHomogeneousElem_coe ⟨p, hp⟩) hpI
  have hqC : q ∈ C.toIdeal :=
    Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (SetLike.isHomogeneousElem_coe ⟨q, hq⟩) hqI
  have hspanC : Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal := by
    rw [Ideal.span_le]
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with hr | hr
    · subst r
      exact hpC
    · subst r
      exact hqC
  have hWC : homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
      Submodule.restrictScalars K C.toIdeal := by
    intro r hr
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (SetLike.isHomogeneousElem_coe ⟨r,
        (mem_homogeneousVanishingPolynomialSubmodule_iff
          (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 r).mp hr |>.1⟩)
    exact hcontains r hr
  have hCrel : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C := by
    apply homogeneousIdeal_relevant_of_le_quotientMinimalPrime_span_pair p q C P
      (hunmixed q hq hq0 hrel P hP)
    exact Ideal.toIdeal_homogeneousCore_le
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) I
  let z := homogeneousPrimeIdeal_projectivePoint C hCprime hCrel
  exact ⟨z, hspanC, hWC⟩


end PfaffianDescent

namespace PfaffianDescent

open MvPolynomial

universe u

/-- In a Noetherian domain the regular module has only the zero associated
prime, which is its unique minimal prime. -/
theorem associatedPrime_mem_minimalPrimes_of_isDomain
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (P : Ideal R) (hP : P ∈ associatedPrimes R R) :
    P ∈ minimalPrimes R := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hP
  obtain ⟨hprime, x, hPx⟩ := hP
  have hx : x ≠ 0 := by
    intro hzero
    subst x
    apply hprime.ne_top
    rw [hPx]
    simp
  have hPbot : P = ⊥ := by
    apply bot_unique
    intro r hr
    rw [hPx, Submodule.mem_colon_singleton] at hr
    change r * x = 0 at hr
    exact (mul_eq_zero.mp hr).resolve_right hx
  rw [hPbot, IsDomain.minimalPrimes_eq_singleton_bot]
  simp

/-- In a Noetherian reduced ring, every associated prime of the regular
module is a minimal prime. -/
theorem associatedPrime_mem_minimalPrimes_of_isReduced
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (P : Ideal R) (hP : P ∈ associatedPrimes R R) :
    P ∈ minimalPrimes R := by
  have hPprime : P.IsPrime := hP.1
  have hsubset : (P : Set R) ⊆ ⋃ Q ∈ minimalPrimes R, (Q : Set R) := by
    intro x hx
    rw [Ideal.iUnion_minimalPrimes, Ideal.radical_bot_of_isReduced,
      Set.mem_ofPred_eq]
    have hxnot : x ∉ nonZeroDivisors R := by
      have hxcomp : x ∈ (↑(nonZeroDivisors R) : Set R)ᶜ := by
        rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors R]
        exact Set.mem_iUnion₂.2 ⟨P, hP, hx⟩
      exact hxcomp
    rw [mem_nonZeroDivisors_iff_left] at hxnot
    push Not at hxnot
    obtain ⟨y, hxy, hy⟩ := hxnot
    exact ⟨y, by simpa using hy, by simpa using hxy⟩
  obtain ⟨Q, hQmin, hPQ⟩ :=
    (P.subset_union_prime_finite (minimalPrimes.finite_of_isNoetherianRing R)
      (f := id) P P (fun i hi _ _ => hi.isPrime)).mp hsubset
  have hQleP : Q ≤ P := hQmin.2 ⟨hPprime, bot_le⟩ hPQ
  have hEq : P = Q := le_antisymm hPQ hQleP
  simpa [hEq] using hQmin

/-- The associated-prime witness is quotient-minimal whenever the selected
cubic--quadric ideal is prime.  This discharges the relevance bridge on the
integral-intermediate-curve branch. -/
theorem quotientAssociatedPrime_mem_minimalPrimes_of_span_pair_isPrime
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) K))))
    (hI : (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hP : P ∈ associatedPrimes
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    P ∈ minimalPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))) := by
  letI : IsDomain (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hI
  exact associatedPrime_mem_minimalPrimes_of_isDomain P hP

/-- The associated-prime witness is quotient-minimal whenever the selected
cubic--quadric quotient is reduced. -/
theorem quotientAssociatedPrime_mem_minimalPrimes_of_span_pair_isReduced
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) K))))
    (hI : IsReduced (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hP : P ∈ associatedPrimes
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    P ∈ minimalPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))) := by
  letI : IsReduced (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))) := hI
  exact associatedPrime_mem_minimalPrimes_of_isReduced P hP

end PfaffianDescent

namespace PfaffianDescent

open MvPolynomial

universe u

/-- If every relevant cubic--quadric intermediate curve is integral, the
associated-prime minimality condition needed by the degree-eight projective
witness follows automatically. -/
theorem CubicQuadricQuotientAssociatedPrimesMinimal.of_span_pair_isPrime
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K)
    (hprime : ∀ (q : MvPolynomial (Fin 4) K), q.IsHomogeneous 2 → q ≠ 0 →
      IsRelPrime p q →
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    CubicQuadricQuotientAssociatedPrimesMinimal p := by
  intro q hq hq0 hrel P hP
  exact quotientAssociatedPrime_mem_minimalPrimes_of_span_pair_isPrime
    p q P (hprime q hq hq0 hrel) hP

/-- If every relevant cubic--quadric intermediate curve is reduced, the
associated-prime minimality condition needed by the degree-eight projective
witness follows automatically. -/
theorem CubicQuadricQuotientAssociatedPrimesMinimal.of_isReduced
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K)
    (hreduced : ∀ (q : MvPolynomial (Fin 4) K), q.IsHomogeneous 2 → q ≠ 0 →
      IsRelPrime p q →
      IsReduced (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    CubicQuadricQuotientAssociatedPrimesMinimal p := by
  intro q hq hq0 hrel P hP
  exact quotientAssociatedPrime_mem_minimalPrimes_of_span_pair_isReduced
    p q P (hreduced q hq hq0 hrel) hP

end PfaffianDescent

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If every relevant cubic--quadric intermediate curve is reduced, failure
of the degree-eight no-fixed-curve condition produces a projective common
curve witness. -/
theorem degreeEight_exists_projectiveCommonCurveWitness_of_isReduced
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcommon : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈)
    (hreduced : ∀ (q : MvPolynomial (Fin 4) K), q.IsHomogeneous 2 → q ≠ 0 →
      IsRelPrime p q →
      IsReduced (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      ∀ (q : MvPolynomial (Fin 4) K) (_hq : q.IsHomogeneous 2),
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
        q ≠ 0 → IsRelPrime p q →
        ∃ z : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) K),
          Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤
            z.asHomogeneousIdeal.toIdeal ∧
          homogeneousVanishingPolynomialSubmodule
              (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
            Submodule.restrictScalars K z.asHomogeneousIdeal.toIdeal := by
  exact degreeEight_exists_projectiveCommonCurveWitness_of_associatedPrimesMinimal
    p hp D₈ hcommon
    (CubicQuadricQuotientAssociatedPrimesMinimal.of_isReduced p hreduced)

end PfaffianDescent

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Associated-prime avoidance supplies the no-common-curve condition once a
regular first quadric is available.  This makes explicit the direct logical
link between the two degree-eight interfaces used in Voisin's argument. -/
theorem DegreeEightQuadraticSystemHasNoCommonCurveComponent.of_avoidsAssociatedPrimes
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hpair : DegreeEightRegularQuadricPairExists p hp D₈)
    (havoid : DegreeEightSecondQuadricAvoidsAssociatedPrimes p hp D₈) :
    DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx
  obtain ⟨q, hq, hqvan, hq0, hrel, -⟩ := hpair x hx
  exact ⟨q, hq, hqvan, hq0, hrel, havoid x hx q hq hqvan hq0 hrel⟩

end PfaffianDescent

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On a prime cubic, the associated-prime rank-drop condition already supplies
Voisin's required regular cubic--quadric--quadric pair.  The first quadric is
chosen from the at-least two-dimensional system through the rank-eight datum;
the rank drop then chooses a second one regular on the resulting curve. -/
theorem DegreeEightRegularQuadricPairExists.of_finrankDrop_of_prime_cubic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hpprime : Prime p)
    (hdrop : DegreeEightSecondQuadricFinrankDrop p hp D₈) :
    DegreeEightRegularQuadricPairExists p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx
  have hsections : 2 ≤ Module.finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)) := by
    apply quadric_degree_eight_vanishing_sections_finrank x
    apply (finiteSchemeCoefficient_finrank
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact D₈.property.2.2.2 (IsLocalRing.closedPoint K)
  obtain ⟨q, hq, hqvan, hq0, hrel⟩ :=
    exists_quadric_section_data_isRelPrime_of_prime_cubic p hp hpprime x hsections
  obtain ⟨r, hr, hrvan, hrregular⟩ :=
    exists_regular_second_quadric_data_of_finrank_drop p q x
      (hdrop x hx q hq hqvan hq0 hrel)
  exact ⟨q, hq, hqvan, hq0, hrel, r, hr, hrvan, hrregular⟩

/-- A prime member of the quadratic system through each normalized
degree-eight presentation already supplies the proper-intersection pair.
The second quadric is chosen outside the first one in the two-dimensional
vanishing space, and primeness of the cubic--first-quadric ideal makes it a
non-zero-divisor. This is the algebraic interface for the repaired incidence
argument that constructs a smooth integral first member through a general
eight-tuple. -/
def DegreeEightPrimeFirstMemberExists
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) :=
    D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
    Function.Surjective (eval₂Hom
      (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
    ∃ q : MvPolynomial (Fin 4) K,
      q.IsHomogeneous 2 ∧
      q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
      q ≠ 0 ∧ IsRelPrime p q ∧
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime

theorem DegreeEightRegularQuadricPairExists.of_prime_first_member
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hfirst : DegreeEightPrimeFirstMemberExists p hp D₈) :
    DegreeEightRegularQuadricPairExists p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx
  have hsections : 2 ≤ Module.finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)) := by
    apply quadric_degree_eight_vanishing_sections_finrank x
    apply (finiteSchemeCoefficient_finrank
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact D₈.property.2.2.2 (IsLocalRing.closedPoint K)
  obtain ⟨q, hq, hqvan, hq0, hrel, hIprime⟩ := hfirst x hx
  obtain ⟨r, hr, hrvan, hrregular⟩ :=
    exists_regular_second_quadric_data_of_selected_prime_intermediate
      p q x hp hq hsections hqvan hq0 hIprime
  exact ⟨q, hq, hqvan, hq0, hrel, r, hr, hrvan, hrregular⟩

/-- On a smooth cubic, the associated-prime rank-drop condition already
implies the source-faithful assertion that the quadratic system through the
degree-eight datum has no fixed curve component. -/
theorem DegreeEightQuadraticSystemHasNoCommonCurveComponent.of_finrankDrop_of_smooth_cubic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hdrop : DegreeEightSecondQuadricFinrankDrop p hp D₈) :
    DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈ := by
  have hpprime : Prime p :=
    (Ideal.span_singleton_prime hne).mp
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hne)
  exact DegreeEightQuadraticSystemHasNoCommonCurveComponent.ofRegularPair
    p hp D₈
    (DegreeEightRegularQuadricPairExists.of_finrankDrop_of_prime_cubic
      p hp D₈ hpprime hdrop)

/-- On a prime cubic, the geometric associated-prime avoidance condition
implies the regular-pair formulation without any separate first-section
hypothesis. -/
theorem DegreeEightRegularQuadricPairExists.of_avoidsAssociatedPrimes_of_prime_cubic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hpprime : Prime p)
    (havoid : DegreeEightSecondQuadricAvoidsAssociatedPrimes p hp D₈) :
    DegreeEightRegularQuadricPairExists p hp D₈ :=
  DegreeEightRegularQuadricPairExists.of_finrankDrop_of_prime_cubic p hp D₈ hpprime
    (havoid.finrankDrop p hp D₈)

/-- On a smooth cubic, associated-prime avoidance already is the literal
no-common-curve condition.  Smoothness supplies primeness of the cubic;
the section-count and avoidance arguments then construct the required regular
pair internally. -/
theorem DegreeEightQuadraticSystemHasNoCommonCurveComponent.of_avoidsAssociatedPrimes_of_smooth_cubic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (havoid : DegreeEightSecondQuadricAvoidsAssociatedPrimes p hp D₈) :
    DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈ := by
  have hpprime : Prime p :=
    (Ideal.span_singleton_prime hne).mp
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hne)
  exact DegreeEightQuadraticSystemHasNoCommonCurveComponent.of_avoidsAssociatedPrimes
    p hp D₈
    (DegreeEightRegularQuadricPairExists.of_avoidsAssociatedPrimes_of_prime_cubic
      p hp D₈ hpprime havoid)
    havoid

/-- The relative Krull-principal-ideal bound for a hyperplane section of a
homogeneous curve ideal.  If `P` is minimal over `C` together with one
coordinate, its image in the quotient by `C` has height at most one.  The
remaining projective hyperplane step is precisely the comparison between
this relative height and the ambient height in the polynomial ring. -/
theorem homogeneousPrime_hyperplaneSection_quotient_height_le_one
    (C P : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4)
    (hminimal : P.toIdeal ∈
      (C.toIdeal ⊔ Ideal.span ({MvPolynomial.X j} : Set
        (MvPolynomial (Fin 4) K))).minimalPrimes) :
    (P.toIdeal.map (Ideal.Quotient.mk C.toIdeal)).height ≤ 1 := by
  exact Ideal.map_height_le_one_of_mem_minimalPrimes hminimal

end PfaffianDescent
