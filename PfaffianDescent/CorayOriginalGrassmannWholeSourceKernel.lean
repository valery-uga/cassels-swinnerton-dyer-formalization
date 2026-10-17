import PfaffianDescent.CorayOriginalGrassmannBadImageDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.FiniteType

noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Order AlgebraicGeometry CategoryTheory
universe u
set_option autoImplicit false

/-- Finite minimal primes construct actual nonzero ORIGINAL-K equations
on all components. Their product maps to a nilpotent, and its actual power
vanishes in the WHOLE source ring. No reducedness, component choice,
dominance, norm or kernel outcome is a premise. -/
theorem grassmannLineChartMap_whole_dimension_le_three_exists_nonzero_kernel001
    {K B : Type u} [Field K] [CommRing B]
    [Algebra K B] [Algebra.FiniteType K B]
    (phi : GrassmannianChartRing K 2 2 →ₐ[K] B)
    (hDim : ringKrullDim B ≤ 3) :
    ∃ q : GrassmannianChartRing K 2 2, q ≠ 0 ∧ phi q = 0 := by
  classical
  rcases subsingleton_or_nontrivial B with hB | hB
  · letI : Subsingleton B := hB
    exact ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
  letI : Nontrivial B := hB
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  letI : Fintype (minimalPrimes B) :=
    (minimalPrimes.finite_of_isNoetherianRing B).fintype
  have hComponent (J : minimalPrimes B) :
      ∃ q : GrassmannianChartRing K 2 2, q ≠ 0 ∧ phi q ∈ J.1 := by
    letI : J.1.IsPrime := J.2.isPrime
    let phiJ : GrassmannianChartRing K 2 2 →ₐ[K] B ⧸ J.1 :=
      (Ideal.Quotient.mkₐ K J.1).comp phi
    have hDimJ : ringKrullDim (B ⧸ J.1) ≤ 3 :=
      (ringKrullDim_quotient_le J.1).trans hDim
    obtain ⟨q, hq0, hq⟩ :=
      grassmannLineChartMap_dimension_le_three_exists_nonzero_kernel001 phiJ hDimJ
    refine ⟨q, hq0, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    change phiJ q = 0
    exact hq
  choose q hq0 hqMem using hComponent
  let Q : GrassmannianChartRing K 2 2 := ∏ J : minimalPrimes B, q J
  have hQ0 : Q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro J _
    exact hq0 J
  have hQMem (J : minimalPrimes B) : phi Q ∈ J.1 := by
    have hDvd : q J ∣ Q := Finset.dvd_prod_of_mem q (Finset.mem_univ J)
    exact J.1.mem_of_dvd (map_dvd phi.toRingHom hDvd) (hqMem J)
  have hNil : IsNilpotent (phi Q) := by
    apply nilpotent_iff_mem_prime.mpr
    intro P hP
    letI : P.IsPrime := hP
    obtain ⟨J, hJ, hJP⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := P) bot_le
    exact hJP (hQMem ⟨J, hJ⟩)
  obtain ⟨n, hn⟩ := hNil
  refine ⟨Q ^ n, pow_ne_zero n hQ0, ?_⟩
  rw [map_pow]
  exact hn

/-- The entire possibly nonreduced source has image closure in a proper
ORIGINAL-K polynomial zero locus, by an equation in its ACTUAL full kernel. -/
theorem grassmannLineChartMap_whole_dimension_le_three_imageClosure_proper001
    {K B : Type u} [Field K] [CommRing B]
    [Algebra K B] [Algebra.FiniteType K B]
    (phi : GrassmannianChartRing K 2 2 →ₐ[K] B)
    (hDim : ringKrullDim B ≤ 3) :
    ∃ q : GrassmannianChartRing K 2 2, q ≠ 0 ∧ phi q = 0 ∧
      closure (Set.range (PrimeSpectrum.comap phi.toRingHom)) ⊆ PrimeSpectrum.zeroLocus {q} ∧
      PrimeSpectrum.zeroLocus {q} ≠ Set.univ := by
  obtain ⟨q, hq0, hq⟩ := grassmannLineChartMap_whole_dimension_le_three_exists_nonzero_kernel001 phi hDim
  have hRange : Set.range (PrimeSpectrum.comap phi.toRingHom) ⊆ PrimeSpectrum.zeroLocus {q} := by
    rintro z ⟨w, rfl⟩
    rw [PrimeSpectrum.mem_zeroLocus]
    intro a ha
    have haq : a = q := Set.mem_singleton_iff.mp ha
    subst a
    change phi q ∈ w.asIdeal
    rw [hq]
    exact Ideal.zero_mem _
  have hProper : PrimeSpectrum.zeroLocus {q} ≠ Set.univ := by
    intro h
    have hMem : (⊥ : PrimeSpectrum (GrassmannianChartRing K 2 2)) ∈ PrimeSpectrum.zeroLocus {q} := by
      rw [h]
      trivial
    have hBot := (PrimeSpectrum.mem_zeroLocus _ _).mp hMem (Set.mem_singleton q)
    exact hq0 (by simpa using hBot)
  exact ⟨q, hq0, hq, (PrimeSpectrum.isClosed_zeroLocus {q}).closure_subset_iff.mpr hRange, hProper⟩

private theorem wholeClosure_range_comp_ne_univ_of_isEmbedding001
    {A B C : Type u} [TopologicalSpace B] [TopologicalSpace C]
    (f : A → B) (i : B → C) (hi : Topology.IsEmbedding i)
    (hf : closure (Set.range f) ≠ Set.univ) :
    closure (Set.range (i ∘ f)) ≠ Set.univ := by
  intro h
  have hClosure := hi.closure_eq_preimage_closure_image (Set.range f)
  rw [← Set.range_comp i f, h] at hClosure
  exact hf (by simpa only [Set.preimage_univ] using hClosure)

/-- The actual map of the WHOLE source, followed by the original chart
inclusion, has proper closure in the WHOLE ORIGINAL Grassmannian. -/
theorem grassmannLineChartMap_whole_dimension_le_three_wholeImageClosure_ne_univ001
    {K B : Type u} [Field K] [CommRing B]
    [Algebra K B] [Algebra.FiniteType K B]
    (phi : GrassmannianChartRing K 2 2 →ₐ[K] B)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (hDim : ringKrullDim B ≤ 3) :
    closure (Set.range (Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ grassmannianChartι K rho)) ≠
      (Set.univ : Set (grassmannianScheme K 2 2)) := by
  obtain ⟨q, _, _, hSub, hProper⟩ :=
    grassmannLineChartMap_whole_dimension_le_three_imageClosure_proper001 phi hDim
  let f : Spec (.of B) ⟶ Spec (.of (GrassmannianChartRing K 2 2)) :=
    Spec.map (CommRingCat.ofHom phi.toRingHom)
  let i : Spec (.of (GrassmannianChartRing K 2 2)) ⟶ grassmannianScheme K 2 2 :=
    grassmannianChartι K rho
  letI : IsOpenImmersion i := by
    change IsOpenImmersion (grassmannianChartι K rho)
    infer_instance
  have hLocal : closure (Set.range f) ≠ (Set.univ : Set (Spec (.of (GrassmannianChartRing K 2 2)))) := by
    change closure (Set.range (PrimeSpectrum.comap phi.toRingHom)) ≠ Set.univ
    intro h
    exact hProper (Set.eq_univ_of_univ_subset (h ▸ hSub))
  exact wholeClosure_range_comp_ne_univ_of_isEmbedding001 f i i.isOpenEmbedding.isEmbedding hLocal

end PfaffianDescent.Coray
