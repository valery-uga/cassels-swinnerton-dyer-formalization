import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.Ideal
import PfaffianDescent.GrassmannianChartEvaluation
import PfaffianDescent.GrassmannianFiniteType

noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Order AlgebraicGeometry CategoryTheory
universe u
set_option autoImplicit false

/-- Actual integral injection lifts every prime chain, hence cannot lower
Krull dimension. Going up and lying over are constructed, not certificates. -/
theorem integralInjectiveRingHom_ringKrullDim_le001
    {R S : Type u} [CommRing R] [CommRing S] [Nontrivial R]
    (f : R →+* S) (hf : Function.Injective f) (hInt : f.IsIntegral) :
    ringKrullDim R ≤ ringKrullDim S := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.IsIntegral R S := algebraMap_isIntegral_iff.mp hInt
  letI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hf
  change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
  unfold Order.krullDim at ⊢
  refine iSup_le fun l => ?_
  let p := l.head.asIdeal
  letI : p.IsPrime := l.head.isPrime
  let Q := Classical.choice (inferInstance : Nonempty (Ideal.primesOver p S))
  letI : Q.1.IsPrime := Q.2.1
  letI : Q.1.LiesOver p := Q.2.2
  obtain ⟨L, hLen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q.1
  simpa only [hLen, Order.krullDim] using L.length_le_krullDim

/-- Actual normalization plus the above lifted-chain lower bound shows
that a finite-type ORIGINAL-K domain of dimension≤3 has trdeg≤3. -/
theorem finiteTypeDomain_ringKrullDim_le_three_trdeg_le_three001
    {K B : Type u} [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra.FiniteType K B]
    (hDim : ringKrullDim B ≤ 3) : Algebra.trdeg K B ≤ 3 := by
  classical
  obtain ⟨s, g, hg, hIntegral⟩ := exists_integral_inj_algHom_of_fg K B
  let P := MvPolynomial (Fin s) K
  have hLower : ringKrullDim P ≤ ringKrullDim B :=
    integralInjectiveRingHom_ringKrullDim_le001 g.toRingHom hg hIntegral
  have hPdim : ringKrullDim P = (s : WithBot ℕ∞) := by
    simp [P, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, Nat.card_fin]
  have hs : s ≤ 3 := by
    have h := hLower.trans hDim
    rw [hPdim] at h
    exact_mod_cast h
  let x : Fin s → B := fun i => g (MvPolynomial.X i)
  let A := Algebra.adjoin K (Set.range x)
  have hRange : A = g.range := by
    dsimp only [A]
    rw [Algebra.adjoin_range_eq_range_aeval]
    congr 1
    apply MvPolynomial.algHom_ext
    intro i
    exact MvPolynomial.aeval_X x i
  let gA : P →ₐ[K] A := g.codRestrict A (by
    intro q
    rw [hRange]
    exact ⟨q, rfl⟩)
  letI : Algebra P B := g.toRingHom.toAlgebra
  letI : Algebra.IsIntegral P B := algebraMap_isIntegral_iff.mp hIntegral
  letI : Algebra P A := gA.toRingHom.toAlgebra
  letI : IsScalarTower P A B := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro q
    change g q = (gA q).1
    rfl)
  letI : Algebra.IsIntegral A B := ⟨fun b =>
    (Algebra.IsIntegral.isIntegral (R := P) b).tower_top⟩
  have hUpper : Algebra.trdeg K B ≤ Cardinal.mk (Set.range x) :=
    Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range x)
  letI : Fintype (Set.range x) := Fintype.ofFinite _
  have hCard : Cardinal.mk (Set.range x) ≤ (s : Cardinal.{u}) := by
    rw [Cardinal.mk_fintype]
    have hCardNat : Fintype.card (Set.range x) ≤ s := by
      simpa only [Fintype.card_fin] using Fintype.card_range_le x
    exact_mod_cast hCardNat
  exact hUpper.trans (hCard.trans (by exact_mod_cast hs))

/-- An ACTUAL map from the four-parameter ORIGINAL Grassmann chart ring
into an actual finite-type domain of dimension≤3 has a nonzero ORIGINAL-K
polynomial in its full kernel. This derives proper-image equations; neither
dominance, nonzero norm nor kernel outcome is an input. -/
theorem grassmannLineChartMap_dimension_le_three_exists_nonzero_kernel001
    {K B : Type u} [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra.FiniteType K B]
    (phi : GrassmannianChartRing K 2 2 →ₐ[K] B)
    (hDim : ringKrullDim B ≤ 3) :
    ∃ q : GrassmannianChartRing K 2 2, q ≠ 0 ∧ phi q = 0 := by
  have hTrdeg := finiteTypeDomain_ringKrullDim_le_three_trdeg_le_three001 (K := K) hDim
  have hNotInjective : ¬ Function.Injective phi := by
    intro hphi
    have hFour : (4 : Cardinal.{u}) ≤ 3 := by
      have h := (_root_.trdeg_le_of_injective phi hphi).trans hTrdeg
      simpa [GrassmannianChartRing, MvPolynomial.trdeg_of_isDomain,
        Cardinal.mk_fintype, Cardinal.lift_natCast] using h
    norm_num at hFour
  have hKernel : RingHom.ker phi.toRingHom ≠ ⊥ := fun h =>
    hNotInjective ((RingHom.injective_iff_ker_eq_bot phi.toRingHom).mpr h)
  obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKernel
  exact ⟨q, hq0, hq⟩

/-- Actual prime comap for a localization is a strict order embedding,
so distinct-pair principal opens do not increase the source dimension. -/
theorem localization_ringKrullDim_le001
    {R S : Type u} [CommRing R] [CommRing S] (M : Submonoid R)
    [Algebra R S] [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
  intro p q hpq
  change p.asIdeal.under R < q.asIdeal.under R
  exact (IsLocalization.orderEmbedding M S).strictMono hpq

/-- The actual affine line-chart map has its entire image closure in a
proper ORIGINAL-K polynomial zero locus, derived from the source bound. -/
theorem grassmannLineChartMap_dimension_le_three_imageClosure_proper001
    {K B : Type u} [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra.FiniteType K B]
    (phi : GrassmannianChartRing K 2 2 →ₐ[K] B)
    (hDim : ringKrullDim B ≤ 3) :
    ∃ q : GrassmannianChartRing K 2 2, q ≠ 0 ∧
      closure (Set.range (PrimeSpectrum.comap phi.toRingHom)) ⊆ PrimeSpectrum.zeroLocus {q} ∧
      PrimeSpectrum.zeroLocus {q} ≠ Set.univ := by
  obtain ⟨q, hq0, hq⟩ := grassmannLineChartMap_dimension_le_three_exists_nonzero_kernel001 phi hDim
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
  exact ⟨q, hq0, (PrimeSpectrum.isClosed_zeroLocus {q}).closure_subset_iff.mpr hRange, hProper⟩

/-- Bounded purely topological closure reflection, with one fixed
source carrier and topology throughout. -/
private theorem closure_range_comp_ne_univ_of_isEmbedding001
    {A B C : Type u} [TopologicalSpace B] [TopologicalSpace C]
    (f : A → B) (i : B → C) (hi : Topology.IsEmbedding i)
    (hf : closure (Set.range f) ≠ Set.univ) :
    closure (Set.range (i ∘ f)) ≠ Set.univ := by
  intro h
  have hClosure := hi.closure_eq_preimage_closure_image (Set.range f)
  rw [← Set.range_comp i f, h] at hClosure
  exact hf (by simpa only [Set.preimage_univ] using hClosure)

/-- The SAME map followed by the ORIGINAL Grassmann chart inclusion has
proper closure in the WHOLE original Grassmannian, not just its chart. -/
theorem grassmannLineChartMap_dimension_le_three_wholeImageClosure_ne_univ001
    {K B : Type u} [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra.FiniteType K B]
    (phi : GrassmannianChartRing K 2 2 →ₐ[K] B)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (hDim : ringKrullDim B ≤ 3) :
    closure (Set.range (Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ grassmannianChartι K rho)) ≠
      (Set.univ : Set (grassmannianScheme K 2 2)) := by
  obtain ⟨q, _, hSub, hProper⟩ := grassmannLineChartMap_dimension_le_three_imageClosure_proper001 phi hDim
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
  exact closure_range_comp_ne_univ_of_isEmbedding001 f i i.isOpenEmbedding.isEmbedding hLocal

end PfaffianDescent.Coray
