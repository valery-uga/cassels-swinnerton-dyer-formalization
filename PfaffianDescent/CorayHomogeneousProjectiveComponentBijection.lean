import PfaffianDescent.CorayHomogeneousMinimalPrimeReducedComponent
import PfaffianDescent.CorayComponentFiniteGaloisDefinition
import Mathlib.RingTheory.GradedAlgebra.Radical

/-!
# Constructed homogeneous minimal primes and the actual projective component bijection

Minimality identifies each raw minimal prime with its homogeneous core.
Actual projective components are constructed from these relevant primes and
recovered in reverse from their native generic points. An original relevant
prime has all extended minimal primes relevant, yielding an actual bijection
with all projective components after any field extension. Neither a component
count, splitting field nor geometric-integrality certificate is an input.
SOURCE ONLY / UNVERIFIED: root alone compiles and audits.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u v
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every ACTUAL raw minimal prime of a homogeneous ideal is its homogeneous
core; hence the homogeneous structure is constructed rather than assumed. -/
theorem homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (P : Ideal (MvPolynomial (Fin 4) K)) (hP : P ∈ I.toIdeal.minimalPrimes) :
    (P.homogeneousCore (homogeneousSubmodule (Fin 4) K)).toIdeal = P := by
  let C := P.homogeneousCore (homogeneousSubmodule (Fin 4) K)
  have hprime : C.toIdeal.IsPrime := hP.1.1.homogeneousCore
  have hIC : I.toIdeal ≤ C.toIdeal :=
    I.isHomogeneous.toIdeal_homogeneousCore_eq_self.symm.trans_le
      (Ideal.homogeneousCore_mono _ hP.1.2)
  have hCP : C.toIdeal ≤ P := Ideal.toIdeal_homogeneousCore_le _ _
  exact le_antisymm hCP (hP.2 ⟨hprime, hIC⟩ hCP)

/-- The ACTUAL relevant homogeneous minimal prime set is equivalent to the
ACTUAL projective irreducible component set. The forward function is the
image of the canonical quotient closed immersion, with its reduced structure
already identified by the checked component theorem. Surjectivity is proved
from native generic points and minimal-prime existence; injectivity is proved
by recovering relevant primes from their ambient vanishing ideals. -/
def homogeneousRelevantMinimalPrimesEquivProjectiveComponents
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    {C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) //
      C.toIdeal ∈ I.toIdeal.minimalPrimes ∧
      ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C} ≃
      irreducibleComponents (scheme I) := by
  classical
  let j := quotientProjMap I
  let jRaw : scheme I → ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K) :=
    fun x => j x
  have hjRaw : Topology.IsClosedEmbedding jRaw := j.isClosedEmbedding
  have hImage (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
      (hIC : I.toIdeal ≤ C.toIdeal) :
      jRaw '' Set.range (schemeQuotientMap I C hIC) =
        ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) K) C.toIdeal := by
    change j '' Set.range (schemeQuotientMap I C hIC) = _
    rw [← Set.range_comp]
    change Set.range (schemeQuotientMap I C hIC ≫ j) = _
    rw [schemeQuotientMap_comp_quotientProjMap, range_quotientProjMap]
  let f : {C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) //
      C.toIdeal ∈ I.toIdeal.minimalPrimes ∧
      ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C} →
      irreducibleComponents (scheme I) := fun C =>
    ⟨Set.range (schemeQuotientMap I C.1 C.2.1.1.2),
      (homogeneousMinimalPrime_projective_reducedComponent I C.1 C.2.1 C.2.2).1⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro C D hCD
    apply Subtype.ext
    have hranges : Set.range (schemeQuotientMap I C.1 C.2.1.1.2) =
        Set.range (schemeQuotientMap I D.1 D.2.1.1.2) := congrArg Subtype.val hCD
    have hzero : ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) K) C.1.toIdeal =
        ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) K) D.1.toIdeal :=
      (hImage C.1 C.2.1.1.2).symm.trans
        ((congrArg (Set.image jRaw) hranges).trans (hImage D.1 D.2.1.1.2))
    exact (vanishingIdeal_zeroLocus_eq_of_prime_relevant C.1 C.2.1.1.1 C.2.2).symm.trans
      ((congrArg ProjectiveSpectrum.vanishingIdeal hzero).trans
        (vanishingIdeal_zeroLocus_eq_of_prime_relevant D.1 D.2.1.1.1 D.2.2))
  · intro Z
    let eta := Z.2.1.genericPoint
    have heta : IsGenericPoint eta Z.1 :=
      Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z.1 Z.2)
    let J := (jRaw eta).asHomogeneousIdeal.toIdeal
    letI : J.IsPrime := (jRaw eta).isPrime
    have hIJ : I.toIdeal ≤ J :=
      (quotientProjMap_mem_range_iff I (jRaw eta)).mp ⟨eta, rfl⟩
    obtain ⟨P, hP, hPJ⟩ := Ideal.exists_minimalPrimes_le hIJ
    let C := P.homogeneousCore (homogeneousSubmodule (Fin 4) K)
    have hCeq : C.toIdeal = P := homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal I P hP
    have hCmin : C.toIdeal ∈ I.toIdeal.minimalPrimes := hCeq.symm ▸ hP
    have hCJ : C ≤ (jRaw eta).asHomogeneousIdeal := by
      change C.toIdeal ≤ J
      rw [hCeq]
      exact hPJ
    have hCrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C :=
      fun h => (jRaw eta).not_irrelevant_le (h.trans hCJ)
    let i := schemeQuotientMap I C hCmin.1.2
    letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion I C hCmin.1.2
    have hcomponent : Set.range i ∈ irreducibleComponents (scheme I) :=
      (homogeneousMinimalPrime_projective_reducedComponent I C hCmin hCrel).1
    have hetaRange : eta ∈ Set.range i := by
      have hamb : jRaw eta ∈ Set.range (quotientProjMap C) :=
        (quotientProjMap_mem_range_iff C (jRaw eta)).mpr hCJ
      obtain ⟨x, hx⟩ := hamb
      refine ⟨x, hjRaw.injective ?_⟩
      have hcomp := schemeQuotientMap_comp_quotientProjMap I C hCmin.1.2
      have hpoint := congrArg (fun φ => φ x) hcomp
      exact hpoint.trans hx
    have hsubset : Z.1 ⊆ Set.range i :=
      (heta.mem_closed_set_iff i.isClosedEmbedding.isClosed_range).mp hetaRange
    have hrange : Set.range i = Z.1 :=
      le_antisymm (Z.2.2 hcomponent.1 hsubset) hsubset
    refine ⟨⟨C, hCmin, hCrel⟩, ?_⟩
    apply Subtype.ext
    exact hrange

/-- Over ANY field extension of an ORIGINAL relevant homogeneous prime, all
actual extended raw minimal primes are homogeneous and relevant INTERNALLY.
They biject with every actual projective irreducible component of its literal
coefficient extension. This does not assert that the extension is a geometric
splitting field; components here are over the ACTUAL field E. -/
def homogeneousCoefficientExtension_minimalPrimesEquivProjectiveComponents
    {E : Type v} [Field E] [Algebra K E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I) :
    (I.toIdeal.map (MvPolynomial.map (algebraMap K E))).minimalPrimes ≃
      irreducibleComponents (scheme (HomogeneousIdeal.map
        (componentPolynomialCoefficientMap (algebraMap K E)) I)) := by
  classical
  let J := HomogeneousIdeal.map (componentPolynomialCoefficientMap (algebraMap K E)) I
  let f : (I.toIdeal.map (MvPolynomial.map (algebraMap K E))).minimalPrimes →
      {C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E) //
        C.toIdeal ∈ J.toIdeal.minimalPrimes ∧
        ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) E) ≤ C} := fun P => by
    let C := P.1.homogeneousCore (homogeneousSubmodule (Fin 4) E)
    have hCeq : C.toIdeal = P.1 :=
      homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal J P.1 P.2
    have hCmin : C.toIdeal ∈ J.toIdeal.minimalPrimes := hCeq.symm ▸ P.2
    exact ⟨C, hCmin, homogeneousCoefficientExtension_minimalPrime_relevant I hIrel C hCmin⟩
  have hunder (P : (I.toIdeal.map (MvPolynomial.map (algebraMap K E))).minimalPrimes) :
      (f P).1.toIdeal = P.1 :=
    homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal J P.1 P.2
  have hbij : Function.Bijective f := by
    constructor
    · intro P Q h
      apply Subtype.ext
      have he : (f P).1.toIdeal = (f Q).1.toIdeal := congrArg (fun C => C.1.toIdeal) h
      exact (hunder P).symm.trans (he.trans (hunder Q))
    · intro C
      let P : (I.toIdeal.map (MvPolynomial.map (algebraMap K E))).minimalPrimes :=
        ⟨C.1.toIdeal, C.2.1⟩
      refine ⟨P, ?_⟩
      apply Subtype.ext
      apply HomogeneousIdeal.toIdeal_injective
      exact hunder P
  exact (Equiv.ofBijective f hbij).trans
    (homogeneousRelevantMinimalPrimesEquivProjectiveComponents J)

end PfaffianDescent.Coray
