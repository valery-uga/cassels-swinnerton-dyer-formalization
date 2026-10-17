import PfaffianDescent.CorayPolynomialComponentContraction
import PfaffianDescent.HomogeneousQuotientMap
import AllCharacteristics.HomogeneousProjectiveAmbient
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.Topology.Sober
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# A genuine reduced projective component from a relevant homogeneous minimal prime

The actual canonical immersion has maximal irreducible image, its source is
integral, and its actual kernel ideal sheaf is the vanishing ideal of that image.
The whole original homogeneous quotient may be reducible or nonreduced.
No geometric-integrality, component count or Galois certificate is assumed.
Source only / unverified: root alone compiles and audits.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u v
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A relevant homogeneous minimal prime defines an ACTUAL reduced induced
irreducible component of the original projective quotient. Minimality is used
to prove maximality of the irreducible image. Primeness gives reducedness;
no reducedness of the original scheme, chosen component or desired geometric
integrality is a premise. The actual immersion kernel equals the native
vanishing ideal sheaf, specifying the reduced structure on this image. -/
theorem homogeneousMinimalPrime_projective_reducedComponent
    (I C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ I.toIdeal.minimalPrimes)
    (hrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C) :
    let i := schemeQuotientMap I C hmin.1.2
    letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion I C hmin.1.2
    Set.range i ∈ irreducibleComponents (scheme I) ∧
      IsIntegral (scheme C) ∧
      i.ker = Scheme.IdealSheafData.vanishingIdeal
        ⟨Set.range i, i.isClosedEmbedding.isClosed_range⟩ := by
  classical
  let i := schemeQuotientMap I C hmin.1.2
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion I C hmin.1.2
  let j := quotientProjMap I
  let jRaw : scheme I → ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K) :=
    fun x => j x
  have hjRaw : Topology.IsClosedEmbedding jRaw := j.isClosedEmbedding
  let c : ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K) :=
    ⟨C, hmin.1.1, hrel⟩
  have hc : c ∈ Set.range j :=
    (quotientProjMap_mem_range_iff I c).mpr hmin.1.2
  obtain ⟨eta, heta⟩ := hc
  have hetaRaw : jRaw eta = c := heta
  have hclosure : closure ({c} : Set (ProjectiveSpectrum
      (homogeneousSubmodule (Fin 4) K))) =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) K) C.toIdeal := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    rfl
  have hImageRange : j '' Set.range i =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) K) C.toIdeal := by
    rw [← Set.range_comp]
    change Set.range (i ≫ j) = _
    rw [schemeQuotientMap_comp_quotientProjMap, range_quotientProjMap]
  have hImageClosure : j '' closure ({eta} : Set (scheme I)) =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) K) C.toIdeal := by
    change jRaw '' closure ({eta} : Set (scheme I)) = _
    rw [← hjRaw.closure_image_eq, Set.image_singleton, hetaRaw]
    exact hclosure
  have hrange : Set.range i = closure ({eta} : Set (scheme I)) :=
    (Set.image_injective.mpr hjRaw.injective) (hImageRange.trans hImageClosure.symm)
  have hcomponent : Set.range i ∈ irreducibleComponents (scheme I) := by
    rw [hrange]
    refine ⟨isIrreducible_singleton.closure, ?_⟩
    intro Z hZ hsubset
    let z := hZ.genericPoint
    have hz : closure ({z} : Set (scheme I)) = closure Z :=
      hZ.genericPoint_closure_eq
    have hetaZ : eta ∈ closure ({z} : Set (scheme I)) := by
      rw [hz]
      exact subset_closure (hsubset (subset_closure (Set.mem_singleton eta)))
    have hetaAmbient : j eta ∈ closure ({j z} : Set (ProjectiveSpectrum
        (homogeneousSubmodule (Fin 4) K))) := by
      change jRaw eta ∈ closure ({jRaw z} : Set (ProjectiveSpectrum
        (homogeneousSubmodule (Fin 4) K)))
      rw [← Set.image_singleton (f := jRaw) (a := z), hjRaw.closure_image_eq]
      exact ⟨eta, hetaZ, rfl⟩
    have hJC : (jRaw z).asHomogeneousIdeal.toIdeal ≤ C.toIdeal := by
      have hetaAmbientRaw : jRaw eta ∈ closure ({jRaw z} : Set (ProjectiveSpectrum
          (homogeneousSubmodule (Fin 4) K))) := hetaAmbient
      have h := (ProjectiveSpectrum.le_iff_mem_closure
        (homogeneousSubmodule (Fin 4) K) (jRaw z) c).mpr
        (hetaRaw ▸ hetaAmbientRaw)
      exact h
    have hIJ : I.toIdeal ≤ (jRaw z).asHomogeneousIdeal.toIdeal :=
      (quotientProjMap_mem_range_iff I (jRaw z)).mp ⟨z, rfl⟩
    have hCJ : C.toIdeal ≤ (jRaw z).asHomogeneousIdeal.toIdeal :=
      hmin.2 ⟨(jRaw z).isPrime, hIJ⟩ hJC
    have hjz : jRaw z = c := by
      apply ProjectiveSpectrum.ext
      exact HomogeneousIdeal.toIdeal_injective (le_antisymm hJC hCJ)
    have hzeta : z = eta := hjRaw.injective (hjz.trans hetaRaw.symm)
    intro x hx
    rw [← hzeta, hz]
    exact subset_closure hx
  letI : IsReduced (scheme C) := scheme_isReduced_of_isRadical C hmin.1.1.isRadical
  letI : IrreducibleSpace (Set.range i) := Subtype.irreducibleSpace hcomponent.1
  letI : IrreducibleSpace (scheme C) :=
    i.isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr inferInstance
  have hint : IsIntegral (scheme C) := isIntegral_of_irreducibleSpace_of_isReduced _
  have hradical : i.ker.radical = i.ker := by
    ext U : 2
    rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    apply Ideal.radical_eq_iff.mpr
    change (Ideal.comap (i.app U).hom
      (⊥ : Ideal Γ(scheme C, i ⁻¹ᵁ U.1))).IsRadical
    exact (Ideal.isRadical_bot).comap (i.app U).hom
  have hsupport : i.ker.support =
      (⟨Set.range i, i.isClosedEmbedding.isClosed_range⟩ : Closeds (scheme I)) := by
    apply Closeds.ext
    change (i.ker.support : Set (scheme I)) = Set.range i
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
  have hvanishing := Scheme.IdealSheafData.vanishingIdeal_support (I := i.ker)
  rw [hsupport, hradical] at hvanishing
  exact ⟨hcomponent, hint, hvanishing.symm⟩

/-- Relevance of every actual homogeneous minimal prime after literal
coefficient extension follows from relevance of the ORIGINAL prime. Actual
contraction is derived by checked going down, not supplied. This works for
any field extension, including an algebraic closure. -/
theorem homogeneousCoefficientExtension_minimalPrime_relevant
    {E : Type v} [Field E] [Algebra K E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
    (hC : C.toIdeal ∈
      (I.toIdeal.map (MvPolynomial.map (algebraMap K E))).minimalPrimes) :
    ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) E) ≤ C := by
  intro hbad
  apply hIrel
  apply (HomogeneousIdeal.irrelevant_le (homogeneousSubmodule (Fin 4) K)).mpr
  intro n hn p hp
  have hCp : MvPolynomial.map (algebraMap K E) p ∈ C :=
    hbad (HomogeneousIdeal.mem_irrelevant_of_mem
      (homogeneousSubmodule (Fin 4) E) hn (hp.map (algebraMap K E)))
  have hpcomap : p ∈ C.toIdeal.comap (MvPolynomial.map (algebraMap K E)) := hCp
  rw [polynomialCoefficientExtension_minimalPrime_comap_eq I.toIdeal C.toIdeal hC] at hpcomap
  exact hpcomap

end PfaffianDescent.Coray
