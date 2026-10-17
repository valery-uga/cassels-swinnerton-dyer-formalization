import PfaffianDescent.CorayHomogeneousProjectiveComponentBijection
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# One constructed finite Galois field defining every actual component ideal

The finite set of ALL actual minimal primes in the literal coefficient
extension is derived by Noetherianity. Actual finite generators of every prime
supply one finite coefficient union; its finite Galois closure simultaneously
defines the WHOLE homogeneous prime ideals. No finite component collection,
field, generator set, descent equation or component cardinality is supplied.
This is simultaneous ideal definition, not yet a universal-field GI theorem.
SOURCE ONLY / UNVERIFIED: root alone compiles and audits.
-/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω]
variable [Algebra K Ω] [IsGalois K Ω]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Starting with the ORIGINAL homogeneous ideal, construct one finite Galois
intermediate field over which EVERY actual minimal component ideal
is its own literal homogeneous contraction's coefficient extension. Taking Ω
to be the actual algebraic closure gives simultaneous definition of all actual
geometric components identified by checked013. No component list, field,
cardinality, stable generators or desired descent equation is a premise. -/
theorem originalHomogeneousIdeal_exists_simultaneousFiniteGalois_componentDefinitionField
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    let J := HomogeneousIdeal.map (componentPolynomialCoefficientMap (algebraMap K Ω)) I
    ∃ L : FiniteGaloisIntermediateField K Ω,
      ∀ P ∈ J.toIdeal.minimalPrimes,
        let C := P.homogeneousCore (homogeneousSubmodule (Fin 4) Ω)
        let D := C.comap (componentPolynomialCoefficientMap (algebraMap L Ω))
        C.toIdeal = P ∧ D.toIdeal.IsPrime ∧
          D.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = P := by
  classical
  let J := HomogeneousIdeal.map (componentPolynomialCoefficientMap (algebraMap K Ω)) I
  let T := J.toIdeal.minimalPrimes
  letI : Finite T := (Ideal.finite_minimalPrimes_of_isNoetherianRing
    (MvPolynomial (Fin 4) Ω) J.toIdeal).to_subtype
  letI : Fintype T := Fintype.ofFinite T
  choose s hs using fun P : T => Ideal.fg_of_isNoetherianRing P.1
  let a : Finset Ω := Finset.univ.biUnion fun P : T =>
    (s P).biUnion fun q => q.coeffs
  let L : FiniteGaloisIntermediateField K Ω :=
    FiniteGaloisIntermediateField.adjoin K (a : Set Ω)
  let f : MvPolynomial (Fin 4) L →+* MvPolynomial (Fin 4) Ω :=
    MvPolynomial.map (algebraMap L Ω)
  refine ⟨L, ?_⟩
  intro P hP
  let t : T := ⟨P, hP⟩
  let C := P.homogeneousCore (homogeneousSubmodule (Fin 4) Ω)
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap L Ω))
  have hCeq : C.toIdeal = P :=
    homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal J P hP
  letI : C.toIdeal.IsPrime := hP.1.1.homogeneousCore
  have hlift : ∀ q ∈ s t, ∃ r : MvPolynomial (Fin 4) L, f r = q := by
    intro q hq
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    have hca : c ∈ (a : Set Ω) := by
      exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ t,
        Finset.mem_biUnion.mpr ⟨q, hq, hc⟩⟩
    have hcL : c ∈ L.toIntermediateField :=
      FiniteGaloisIntermediateField.subset_adjoin K (a : Set Ω) hca
    exact ⟨⟨c, hcL⟩, rfl⟩
  refine ⟨hCeq, inferInstance, ?_⟩
  change (C.toIdeal.comap f).map f = P
  rw [hCeq]
  apply le_antisymm Ideal.map_comap_le
  apply (hs t).symm.trans_le
  apply Ideal.span_le.mpr
  intro q hq
  obtain ⟨r, hr⟩ := hlift q hq
  have hqP : q ∈ P := by
    change q ∈ t.1
    rw [← hs t]
    exact Ideal.subset_span hq
  have hrP : r ∈ P.comap f := by
    change f r ∈ P
    rw [hr]
    exact hqP
  exact hr ▸ Ideal.mem_map_of_mem f hrP

end PfaffianDescent.Coray
