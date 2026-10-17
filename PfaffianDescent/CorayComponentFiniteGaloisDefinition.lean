import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
# A constructed finite Galois definition field for an actual component ideal

Finite generation of the actual homogeneous prime supplies its finitely many
coefficients. Their finite Galois closure gives a field over which the actual
homogeneous contraction is prime and has precisely the original ideal as its
coefficient extension. No definition field or descent certificate is supplied.

This is not the minimal stabilizer field, an orbit/transitivity theorem, a
geometric-integrality theorem, or a component degree/genus bound.
SOURCE ONLY / UNVERIFIED: root alone compiles and audits.
-/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Raw coefficient change with the actual homogeneous polynomial grading. -/
def componentPolynomialCoefficientMap {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) :
    homogeneousSubmodule (Fin 4) R →+*ᵍ homogeneousSubmodule (Fin 4) S where
  __ := MvPolynomial.map f
  map_mem hx := hx.map f

/-- Every actual homogeneous prime in a Galois ambient field descends to its
actual homogeneous contraction over a constructed finite Galois intermediate
field. The literal coefficient-extension equality is the input needed by the
existing projective coefficient-base-change isomorphism API.

The field need not be minimal, and its degree is not asserted to equal the
number of geometric components. The prime is given as an actual ideal; finite
generators, their coefficients, the field, and the descended prime are produced
in this proof. -/
theorem homogeneousPrime_exists_finiteGalois_definitionField
    {K : Type u} {Ω : Type v} [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Ω))
    [C.toIdeal.IsPrime] :
    ∃ (L : FiniteGaloisIntermediateField K Ω)
      (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L)),
      D = C.comap (componentPolynomialCoefficientMap (algebraMap L Ω)) ∧
      D.toIdeal.IsPrime ∧
      D.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = C.toIdeal := by
  classical
  obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing C.toIdeal
  let a : Finset Ω := s.biUnion fun p => p.coeffs
  let L : FiniteGaloisIntermediateField K Ω :=
    FiniteGaloisIntermediateField.adjoin K (a : Set Ω)
  let f : MvPolynomial (Fin 4) L →+* MvPolynomial (Fin 4) Ω :=
    MvPolynomial.map (algebraMap L Ω)
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap L Ω))
  have hlift : ∀ p ∈ s, ∃ q : MvPolynomial (Fin 4) L, f q = p := by
    intro p hp
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    have hca : c ∈ (a : Set Ω) := by
      exact Finset.mem_biUnion.mpr ⟨p, hp, hc⟩
    have hcL : c ∈ L.toIntermediateField :=
      FiniteGaloisIntermediateField.subset_adjoin K (a : Set Ω) hca
    exact ⟨⟨c, hcL⟩, rfl⟩
  refine ⟨L, D, rfl, inferInstance, ?_⟩
  change (C.toIdeal.comap f).map f = C.toIdeal
  apply le_antisymm Ideal.map_comap_le
  apply hs.symm.trans_le
  apply Ideal.span_le.mpr
  intro p hp
  obtain ⟨q, hq⟩ := hlift p hp
  have hpC : p ∈ C.toIdeal := hs ▸ Ideal.subset_span hp
  have hqC : q ∈ C.toIdeal.comap f := by
    change f q ∈ C.toIdeal
    rw [hq]
    exact hpC
  exact hq ▸ Ideal.mem_map_of_mem f hqC

end PfaffianDescent.Coray
