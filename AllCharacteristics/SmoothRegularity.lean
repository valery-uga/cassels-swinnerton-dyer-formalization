import AllCharacteristics.EtaleCoordinates
import AllCharacteristics.EtaleRegularity
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Smooth algebras over regular rings are regular

A standard smooth presentation supplies a differential basis, hence an étale
map from a polynomial algebra. Polynomial algebras over regular rings are
regular, and regularity ascends along that étale map. Standard smooth
localizations then prove the result for every smooth algebra.
-/

open Algebra
namespace AllCharacteristics
universe u v
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- A standard smooth algebra over a regular ring is regular. -/
theorem isRegularRing_of_standardSmooth [IsRegularRing R] [Algebra.IsStandardSmooth R S] :
    IsRegularRing S := by
  classical
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := R) (S := S)
  let κ := ((Set.range P.map)ᶜ : Set ι)
  let φ : MvPolynomial κ R →ₐ[R] S := MvPolynomial.aeval (fun i : κ => P.val i)
  let : Algebra (MvPolynomial κ R) S := φ.toAlgebra
  have : IsScalarTower R (MvPolynomial κ R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : Algebra.FormallyEtale (MvPolynomial κ R) S :=
    formallyEtale_of_polynomial_differential_basis R S P.basisKaehler (by
      intro i
      change P.basisKaehler i = KaehlerDifferential.D R S
        ((MvPolynomial.aeval (fun i : κ => P.val i)) (MvPolynomial.X i))
      rw [MvPolynomial.aeval_X, P.basisKaehler_apply])
  have : Algebra.FiniteType (MvPolynomial κ R) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (MvPolynomial κ R) S
  have : Algebra.FinitePresentation (MvPolynomial κ R) S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale (MvPolynomial κ R) S := {}
  exact isRegularRing_of_flat_formallyUnramified (MvPolynomial κ R) S

/-- A local standard-smooth algebra of relative dimension `n` over a field has dimension at most
`n`. -/
theorem ringKrullDim_le_of_standardSmoothOfRelativeDimension_of_field
    {K A : Type*} (n : ℕ) [Field K] [CommRing A] [Algebra K A] [IsLocalRing A]
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] : ringKrullDim A ≤ n := by
  letI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  letI : IsRegularRing A := isRegularRing_of_standardSmooth K A
  letI : IsRegularLocalRing A := IsRegularLocalRing.of_isRegularRing_of_isLocalRing A
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K A
  let P := MvPolynomial (Fin n) K
  letI : Algebra P A := g.toAlgebra
  letI : IsScalarTower K P A := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  letI : Algebra.Etale P A := hg
  let m := IsLocalRing.maximalIdeal A
  let q : Ideal P := m.comap (algebraMap P A)
  letI : q.IsPrime := Ideal.IsPrime.comap (algebraMap P A)
  letI : m.LiesOver q := ⟨rfl⟩
  let T := Localization.AtPrime q
  let U := Localization.AtPrime m
  letI : Algebra T U := Localization.AtPrime.algebraOfLiesOver q m
  letI : Algebra.EssFiniteType P A := inferInstance
  letI : Algebra.EssFiniteType P U := inferInstance
  letI : Algebra.EssFiniteType T U := Algebra.EssFiniteType.of_comp P T U
  letI : Algebra.FormallyUnramified T U :=
    Algebra.FormallyUnramified.of_restrictScalars P T U
  have hmax : (IsLocalRing.maximalIdeal T).map (algebraMap T U) =
      IsLocalRing.maximalIdeal U :=
    Algebra.FormallyUnramified.map_maximalIdeal
  letI : IsLocalization m.primeCompl A := IsLocalization.of_le_isUnit (by
    intro x hx
    change x ∉ IsLocalRing.maximalIdeal A at hx
    change IsUnit x
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using hx)
  let e : U ≃+* A := (Localization.algEquiv m.primeCompl A).toRingEquiv
  letI : IsRegularLocalRing U := IsRegularLocalRing.of_ringEquiv e.symm
  letI : IsRegularRing K := inferInstance
  letI : IsRegularRing P := inferInstance
  letI : IsRegularLocalRing T := IsRegularRing.isRegularLocalRing_localization q
  have hT : ringKrullDim T ≤ n := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q T]
    refine Ideal.height_le_ringKrullDim_of_isPrime.trans ?_
    simp [P, MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have hfg : (IsLocalRing.maximalIdeal T).FG :=
    (IsLocalRing.maximalIdeal T).fg_of_isNoetherianRing
  have hU : ringKrullDim U ≤ n := by
    calc
      ringKrullDim U = (IsLocalRing.maximalIdeal U).spanFinrank :=
        IsRegularLocalRing.spanFinrank_maximalIdeal.symm
      _ = ((IsLocalRing.maximalIdeal T).map (algebraMap T U)).spanFinrank := by rw [hmax]
      _ ≤ (IsLocalRing.maximalIdeal T).spanFinrank :=
        by exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap T U) hfg
      _ = ringKrullDim T := IsRegularLocalRing.spanFinrank_maximalIdeal
      _ ≤ n := hT
  rw [← ringKrullDim_eq_of_ringEquiv e]
  exact hU

/-- Every prime localization of a standard-smooth algebra of relative dimension `n` over a field
has dimension at most `n`. -/
theorem ringKrullDim_localizationAtPrime_le_of_standardSmoothOfRelativeDimension_of_field
    {K A : Type*} (n : ℕ) [Field K] [CommRing A] [Algebra K A]
    [Algebra.IsStandardSmoothOfRelativeDimension n K A]
    (q : Ideal A) [q.IsPrime] : ringKrullDim (Localization.AtPrime q) ≤ n := by
  letI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  letI : IsRegularRing A := isRegularRing_of_standardSmooth K A
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K A
  let P := MvPolynomial (Fin n) K
  letI : Algebra P A := g.toAlgebra
  letI : IsScalarTower K P A := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  letI : Algebra.Etale P A := hg
  let p : Ideal P := q.comap (algebraMap P A)
  letI : p.IsPrime := Ideal.IsPrime.comap (algebraMap P A)
  letI : q.LiesOver p := ⟨rfl⟩
  let T := Localization.AtPrime p
  let U := Localization.AtPrime q
  letI : Algebra T U := Localization.AtPrime.algebraOfLiesOver p q
  letI : Algebra.EssFiniteType P A := inferInstance
  letI : Algebra.EssFiniteType P U := inferInstance
  letI : Algebra.EssFiniteType T U := Algebra.EssFiniteType.of_comp P T U
  letI : Algebra.FormallyUnramified T U :=
    Algebra.FormallyUnramified.of_restrictScalars P T U
  have hmax : (IsLocalRing.maximalIdeal T).map (algebraMap T U) =
      IsLocalRing.maximalIdeal U :=
    Algebra.FormallyUnramified.map_maximalIdeal
  letI : IsRegularRing K := inferInstance
  letI : IsRegularRing P := inferInstance
  letI : IsRegularLocalRing T := IsRegularRing.isRegularLocalRing_localization p
  letI : IsRegularLocalRing U := IsRegularRing.isRegularLocalRing_localization q
  have hT : ringKrullDim T ≤ n := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p T]
    refine Ideal.height_le_ringKrullDim_of_isPrime.trans ?_
    simp [P, MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have hfg : (IsLocalRing.maximalIdeal T).FG :=
    (IsLocalRing.maximalIdeal T).fg_of_isNoetherianRing
  calc
    ringKrullDim U = (IsLocalRing.maximalIdeal U).spanFinrank :=
      IsRegularLocalRing.spanFinrank_maximalIdeal.symm
    _ = ((IsLocalRing.maximalIdeal T).map (algebraMap T U)).spanFinrank := by rw [hmax]
    _ ≤ (IsLocalRing.maximalIdeal T).spanFinrank :=
      by exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap T U) hfg
    _ = ringKrullDim T := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ ≤ n := hT

/-- Every prime localization of a locally standard-smooth algebra of relative dimension `n` over
a field has dimension at most `n`. -/
theorem ringKrullDim_localizationAtPrime_le_of_locally_standardSmoothOfRelativeDimension_of_field
    {K A : Type u} (n : ℕ) [Field K] [CommRing A] [Algebra K A]
    (hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap K A))
    (q : Ideal A) [q.IsPrime] : ringKrullDim (Localization.AtPrime q) ≤ n := by
  obtain ⟨s, hs, hstd⟩ := hlocal
  have hnot : ∃ t ∈ s, t ∉ q := by
    by_contra h
    push Not at h
    have hle : Ideal.span s ≤ q := Ideal.span_le.mpr fun x hx => h x hx
    have hq : q = ⊤ := by
      apply top_unique
      rw [← hs]
      exact hle
    exact (Ideal.IsPrime.ne_top' (I := q)) hq
  obtain ⟨t, ht, htq⟩ := hnot
  let Aₜ := Localization.Away t
  letI : Algebra K Aₜ := ((algebraMap A Aₜ).comp (algebraMap K A)).toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension n K Aₜ := hstd t ht
  let qₜ : Ideal Aₜ := q.map (algebraMap A Aₜ)
  have hdisj : Disjoint (Submonoid.powers t : Set A) (q : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := q) t).mpr htq
  letI : qₜ.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) Aₜ
    q inferInstance hdisj
  have hdim : ringKrullDim (Localization.AtPrime qₜ) ≤ n :=
    ringKrullDim_localizationAtPrime_le_of_standardSmoothOfRelativeDimension_of_field
      (K := K) (A := Aₜ) n qₜ
  letI : IsLocalization.AtPrime (Localization.AtPrime qₜ) q := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers t) (Localization.AtPrime qₜ) qₜ using 1
    exact (IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers t)
      Aₜ inferInstance hdisj).symm
  let e : Localization.AtPrime qₜ ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime qₜ)
      (Localization.AtPrime q)).toRingEquiv
  rw [← ringKrullDim_eq_of_ringEquiv e]
  exact hdim

/-- A local algebra that is locally standard smooth of relative dimension `n` over a field has
dimension at most `n`. -/
theorem ringKrullDim_le_of_locally_standardSmoothOfRelativeDimension_of_field
    {K A : Type u} (n : ℕ) [Field K] [CommRing A] [Algebra K A] [IsLocalRing A]
    (hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap K A)) : ringKrullDim A ≤ n := by
  obtain ⟨s, hs, hstd⟩ := hlocal
  have hnot : ∃ t ∈ s, t ∉ IsLocalRing.maximalIdeal A := by
    by_contra h
    push Not at h
    apply Ideal.IsMaximal.ne_top (IsLocalRing.maximalIdeal.isMaximal A)
    apply top_unique
    rw [← hs]
    exact Ideal.span_le.mpr fun x hx => h x hx
  obtain ⟨t, ht, htm⟩ := hnot
  have hunit : IsUnit t := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using htm
  letI : IsLocalization.Away t A :=
    IsLocalization.away_of_isUnit_of_bijective A hunit Function.bijective_id
  let e : A ≃+* Localization.Away t :=
    (IsLocalization.atUnit A (Localization.Away t) t hunit).toRingEquiv
  have hstd' : RingHom.IsStandardSmoothOfRelativeDimension n
      (e.toRingHom.comp (algebraMap K A)) := by
    convert hstd t ht using 1
    ext x
    exact (IsLocalization.atUnit A (Localization.Away t) t hunit).commutes _
  have hstdA : RingHom.IsStandardSmoothOfRelativeDimension n (algebraMap K A) := by
    have h := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).1
      (e.toRingHom.comp (algebraMap K A)) e.symm hstd'
    convert h using 1
    ext x
    simp
  letI : Algebra.IsStandardSmoothOfRelativeDimension n K A :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).mp hstdA
  exact ringKrullDim_le_of_standardSmoothOfRelativeDimension_of_field (K := K) (A := A) n

/-- Every prime localization of a residue fibre of a locally standard-smooth
algebra has dimension bounded by the relative dimension. -/
theorem ringKrullDim_localizationAtPrime_fiber_le_of_locally_standardSmoothOfRelativeDimension
    {R S : Type u} (n : ℕ) [CommRing R] [CommRing S] [Algebra R S]
    (hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap R S))
    (p : PrimeSpectrum R) (q : Ideal (p.asIdeal.Fiber S)) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime q) ≤ n := by
  letI : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.leftAlgebra
  have hfiber : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) :=
    (RingHom.locally_isStableUnderBaseChange
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n)).tensorProduct
        p.asIdeal.ResidueField hlocal
  exact
    ringKrullDim_localizationAtPrime_le_of_locally_standardSmoothOfRelativeDimension_of_field
      (K := p.asIdeal.ResidueField) (A := p.asIdeal.Fiber S) n hfiber q

/-- A regular principal neighborhood supplies a regular localization at each prime in it. -/
theorem isRegularLocalRing_atPrime_of_regular_away (q : Ideal S) [q.IsPrime]
    (g : S) (hg : g ∉ q) [IsRegularRing (Localization.Away g)] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let q' := q.map (algebraMap S (Localization.Away g))
  have hdisj : Disjoint (Submonoid.powers g : Set S) (q : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := q) g).mpr hg
  have : q'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) (Localization.Away g)
      q inferInstance hdisj
  have : IsLocalization.AtPrime (Localization.AtPrime q') q := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers g) (Localization.AtPrime q') q' using 1
    exact (IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g)
      (Localization.Away g) inferInstance hdisj).symm
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q')
      (Localization.AtPrime q)).toRingEquiv

/-- Every prime localization of an algebra which is locally standard smooth
over a field is regular local.  The proof chooses a standard-smooth
neighborhood of the prime, proves that neighborhood regular, and transports
regularity through the localization comparison. -/
theorem
    isRegularLocalRing_localizationAtPrime_of_locally_standardSmoothOfRelativeDimension_of_field
    {K A : Type u} (n : ℕ) [Field K] [CommRing A] [Algebra K A]
    (hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap K A))
    (q : Ideal A) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  obtain ⟨s, hs, hstd⟩ := hlocal
  have hnot : ∃ t ∈ s, t ∉ q := by
    by_contra h
    push Not at h
    have hle : Ideal.span s ≤ q := Ideal.span_le.mpr fun x hx => h x hx
    have hq : q = ⊤ := by
      apply top_unique
      rw [← hs]
      exact hle
    exact (Ideal.IsPrime.ne_top' (I := q)) hq
  obtain ⟨t, ht, htq⟩ := hnot
  let Aₜ := Localization.Away t
  letI : Algebra K Aₜ := ((algebraMap A Aₜ).comp (algebraMap K A)).toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension n K Aₜ := hstd t ht
  letI : Algebra.IsStandardSmooth K Aₜ :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  letI : IsRegularRing Aₜ := isRegularRing_of_standardSmooth K Aₜ
  exact isRegularLocalRing_atPrime_of_regular_away A q t htq

/-- The prime localizations of every residue fibre of a locally
standard-smooth family over a field are regular local. -/
theorem
    isRegularLocalRing_localizationAtPrime_fiber_of_locally_standardSmoothOfRelativeDimension
    {R S : Type u} (n : ℕ) [CommRing R] [CommRing S] [Algebra R S]
    (hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap R S))
    (p : PrimeSpectrum R) (q : Ideal (p.asIdeal.Fiber S)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  letI : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.leftAlgebra
  have hfiber : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) :=
    (RingHom.locally_isStableUnderBaseChange
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n)).tensorProduct
        p.asIdeal.ResidueField hlocal
  exact
    isRegularLocalRing_localizationAtPrime_of_locally_standardSmoothOfRelativeDimension_of_field
      (K := p.asIdeal.ResidueField) (A := p.asIdeal.Fiber S) n hfiber q

/-- Every smooth algebra over a regular ring is regular. -/
theorem isRegularRing_of_smooth [IsRegularRing R] [Algebra.Smooth R S] :
    IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply isRegularRing_iff.mpr
  intro q hq
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R q
  have : IsRegularRing (Localization.Away g) :=
    isRegularRing_of_standardSmooth R (Localization.Away g)
  exact isRegularLocalRing_atPrime_of_regular_away S q g hg

end AllCharacteristics
