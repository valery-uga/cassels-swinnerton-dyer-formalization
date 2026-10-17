import PfaffianDescent.CorayHomogeneousMinimalPrimeReducedComponent
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Actual component minimality on its OWN affine chart

The canonical chart square and genuine irreducible-component maximality
derive minimality in the literal chart ring. Empty charts give the top
kernel. No affine minimal-prime or prime-kernel certificate is supplied.
SOURCE ONLY / UNVERIFIED; root owns all compiler and audit checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual chart quotient image is the inverse image of the actual
projective quotient image. Both maps are canonical, with no image premise. -/
theorem homogeneousQuotient_nativeChart_preimage_range
    (I C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIC : I.toIdeal ≤ C.toIdeal) (j : Fin 4) :
    (chartι I j) ⁻¹' Set.range (schemeQuotientMap I C hIC) =
      Set.range (Spec.map (CommRingCat.ofHom (chartQuotientMap I C hIC j))) := by
  let i := schemeQuotientMap I C hIC
  let g := Spec.map (CommRingCat.ofHom (chartQuotientMap I C hIC j))
  have hcomm (b : Spec (.of (ChartRing C j))) :
      i (chartι C j b) = chartι I j (g b) := by
    exact congrArg (fun f => f b) (chartι_schemeQuotientMap I C hIC j)
  ext x
  constructor
  · rintro ⟨a, ha⟩
    have hac : a ∈ (chartι C j).opensRange := by
      rw [← schemeQuotientMap_preimage_chart I C hIC j]
      change i a ∈ (chartι I j).opensRange
      rw [ha]
      exact ⟨x, rfl⟩
    change a ∈ Set.range (chartι C j) at hac
    obtain ⟨b, hb⟩ := hac
    refine ⟨b, (chartι I j).isOpenEmbedding.injective ?_⟩
    exact (hcomm b).symm.trans ((congrArg i hb).trans ha)
  · rintro ⟨b, hb⟩
    exact ⟨chartι C j b, (hcomm b).trans (congrArg (chartι I j) hb)⟩

/-- A homogeneous minimal component restricts to either the empty chart,
or an actual minimal prime of the SAME chart of the original quotient. -/
theorem homogeneousMinimalPrime_nativeChartKernel_top_or_minimalPrime
    (I C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ I.toIdeal.minimalPrimes)
    (hrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C)
    (j : Fin 4) :
    let f := chartQuotientMap I C hmin.le j
    RingHom.ker f = ⊤ ∨
      ((RingHom.ker f).IsPrime ∧ RingHom.ker f ∈ minimalPrimes (ChartRing I j)) := by
  classical
  let f := chartQuotientMap I C hmin.le j
  rcases subsingleton_or_nontrivial (ChartRing C j) with hsub | hnontriv
  · letI : Subsingleton (ChartRing C j) := hsub
    exact Or.inl (RingHom.ker_eq_top_of_subsingleton f)
  · letI : Nontrivial (ChartRing C j) := hnontriv
    letI : Nonempty (Spec (.of (ChartRing C j))) := inferInstance
    have hcomponent := homogeneousMinimalPrime_projective_reducedComponent I C hmin hrel
    letI : IsIntegral (scheme C) := hcomponent.2.1
    letI : IsIntegral (Spec (.of (ChartRing C j))) :=
      isIntegral_of_isOpenImmersion (chartι C j)
    letI : IsDomain (ChartRing C j) :=
      (affine_isIntegral_iff (.of (ChartRing C j))).mp inferInstance
    have hprime : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    let i := schemeQuotientMap I C hmin.le
    let g := Spec.map (CommRingCat.ofHom f)
    let b : Spec (.of (ChartRing C j)) := Classical.choice inferInstance
    have hmeet : (Set.range i ∩ Set.range (chartι I j)).Nonempty := by
      refine ⟨i (chartι C j b), ⟨chartι C j b, rfl⟩, g b, ?_⟩
      exact (congrArg (fun f => f b) (chartι_schemeQuotientMap I C hmin.le j)).symm
    have hchartComponent := preimage_mem_irreducibleComponents hcomponent.1
      (chartι I j).isOpenEmbedding hmeet
    rw [homogeneousQuotient_nativeChart_preimage_range I C hmin.le j] at hchartComponent
    have hzeroLocus : PrimeSpectrum.zeroLocus (RingHom.ker f) ∈
        irreducibleComponents (PrimeSpectrum (ChartRing I j)) := by
      change Set.range (PrimeSpectrum.comap f) ∈
        irreducibleComponents (PrimeSpectrum (ChartRing I j)) at hchartComponent
      rw [_root_.range_comap_of_surjective _ _ (chartQuotientMap_surjective I C hmin.le j)]
        at hchartComponent
      exact hchartComponent
    have hminChart := PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mp hzeroLocus
    rw [hprime.isRadical.radical] at hminChart
    exact Or.inr ⟨hprime, hminChart⟩

end PfaffianDescent.Coray
