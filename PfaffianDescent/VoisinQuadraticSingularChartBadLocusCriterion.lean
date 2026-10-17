import PfaffianDescent.VoisinSingularChartBadLocusCriterion
import PfaffianDescent.VoisinQuadraticRestrictionKernelUniversalFamily

/-!
# Detecting a good quadratic parameter from its specialized singular fibre

For the final cubic--quadric--quadric residual, an empty singular fibre at one
field-valued parameter proves that the full quadratic restriction-kernel bad
locus is proper. Coordinate-power ideal memberships give a finite algebraic
certificate of that emptiness.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicTwoQuadricUniversalSingularChart_not_mem_range_of_fiber_isEmpty
    {K L : Type u} [Field K] [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (hEmpty : ∀ _z : scheme
      (cubicTwoQuadricUniversalSingularChartFiberIdeal
        p q hp hq v i g), False) :
    Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L) ∉
      Set.range (toBase
        (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal
          p q hp hq v i)) := by
  let J := cubicTwoQuadricUniversalSingularChartHomogeneousIdeal p q hp hq v i
  let J' := cubicTwoQuadricUniversalSingularChartFiberIdeal p q hp hq v i g
  let b : Spec (.of L) ⟶ Spec (.of
      (ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) :=
    Spec.map (CommRingCat.ofHom g)
  have hsq : IsPullback
      (cubicTwoQuadricUniversalSingularChartFiberToFamily p q hp hq v i g)
      (toBase J') (toBase J) b :=
    isPullback_projectiveCoefficientMap g J J'
      (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal_map_eq_fiber
        p q hp hq v i g)
  exact not_mem_range_of_isEmpty_isPullback (toBase J) b
    (cubicTwoQuadricUniversalSingularChartFiberToFamily p q hp hq v i g)
    (toBase J') hsq (IsLocalRing.closedPoint L) hEmpty

theorem cubicTwoQuadricUniversalSingularChartBadLocus_eq_range
    {K : Type u} [Field K] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n) :
    cubicTwoQuadricUniversalSingularChartBadLocus p q hp hq v i =
      Set.range (toBase
        (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal
          p q hp hq v i)) := by
  simp only [cubicTwoQuadricUniversalSingularChartBadLocus,
    cubicTwoQuadricUniversalSingularChartFamilyToBase]

theorem cubicTwoQuadricUniversalSingularParameterLocus_ne_univ_of_fiber_isEmpty
    {K L : Type u} [Field K] [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (hEmpty : ∀ _z : scheme
      (cubicTwoQuadricUniversalSingularChartFiberIdeal
        p q hp hq v i g), False) :
    cubicTwoQuadricUniversalSingularParameterLocus p q hp hq v ≠ Set.univ := by
  let y : Spec (.of
      (ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) :=
    Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L)
  have hy : y ∉ cubicTwoQuadricUniversalSingularChartBadLocus p q hp hq v i := by
    rw [cubicTwoQuadricUniversalSingularChartBadLocus_eq_range]
    exact cubicTwoQuadricUniversalSingularChart_not_mem_range_of_fiber_isEmpty
      p q hp hq v i g hEmpty
  have hgood :
      chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i y ∈
        cubicTwoQuadricUniversalNonsingularParameterLocus p q hp hq v := by
    simp only [cubicTwoQuadricUniversalNonsingularParameterLocus, Set.mem_iUnion]
    exact ⟨i, y, hy, rfl⟩
  intro hbad
  have hsing : chartι
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i y ∈
        cubicTwoQuadricUniversalSingularParameterLocus p q hp hq v := by
    rw [hbad]
    trivial
  exact (by simpa only
    [cubicTwoQuadricUniversalSingularParameterLocus, Set.mem_compl_iff] using hsing :
      chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i y ∉
        cubicTwoQuadricUniversalNonsingularParameterLocus p q hp hq v) hgood

/-- Four coordinate-power memberships in one specialized mixed-degree
singular ideal certify properness of the full quadratic restriction-kernel
bad locus. -/
theorem cubicTwoQuadricRestrictionKernelSingularParameterLocus_ne_univ_of_coordinate_powers_mem
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (x : Fin 4 → A)
    (i : Fin (finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2))))
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule
        (Fin (finrank K
          (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)))) K)) i →+* L)
    (hcert :
      let I := cubicTwoQuadricUniversalSingularChartFiberIdeal
        p q hp hq (quadraticRestrictionKernelFrame (K := K) x) i g
      ∀ j : Fin 4,
        ∃ n : ℕ, (MvPolynomial.X j : MvPolynomial (Fin 4) L) ^ n ∈ I.toIdeal) :
    cubicTwoQuadricRestrictionKernelSingularParameterLocus p q hp hq x ≠ Set.univ := by
  let I := cubicTwoQuadricUniversalSingularChartFiberIdeal
    p q hp hq (quadraticRestrictionKernelFrame (K := K) x) i g
  have hEmpty : IsEmpty (scheme I) :=
    isEmpty_projectiveScheme_of_coordinate_powers_mem I hcert
  exact cubicTwoQuadricUniversalSingularParameterLocus_ne_univ_of_fiber_isEmpty
    p q hp hq (quadraticRestrictionKernelFrame (K := K) x) i g
    (fun z => isEmptyElim z)

/-- Over an infinite field, properness of the mixed singular-parameter locus
is exactly witnessed by four coordinate-power memberships in one specialized
singular fibre over a ground-field normalized parameter chart. -/
theorem cubicTwoQuadricUniversalSingularParameterLocus_ne_univ_iff_coordinateCertificate
    {K : Type u} [Field K] [Infinite K] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    cubicTwoQuadricUniversalSingularParameterLocus p q hp hq v ≠ Set.univ ↔
      ∃ (i : Fin n)
        (g : ChartRing
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* K),
        let I := cubicTwoQuadricUniversalSingularChartFiberIdeal
          p q hp hq v i g
        ∀ j : Fin 4,
          ∃ m : ℕ, (MvPolynomial.X j : MvPolynomial (Fin 4) K) ^ m ∈ I.toIdeal := by
  constructor
  · intro hproper
    let U : Scheme.Opens
        (projectiveLinearSystemParameters (K := K) (τ := Fin n)) :=
      ⟨cubicTwoQuadricUniversalNonsingularParameterLocus p q hp hq v,
        isOpen_cubicTwoQuadricUniversalNonsingularParameterLocus p q hp hq v⟩
    obtain ⟨x, hx⟩ :=
      (Set.ne_univ_iff_exists_notMem
        (cubicTwoQuadricUniversalSingularParameterLocus
          p q hp hq v)).mp hproper
    have hxU : x ∈ (U : Set
        (projectiveLinearSystemParameters (K := K) (τ := Fin n))) := by
      simpa [U, cubicTwoQuadricUniversalSingularParameterLocus,
        Set.mem_compl_iff] using hx
    obtain ⟨s, hs⟩ :=
      nonempty_open_projectiveSpace_has_rational_section U ⟨x, hxU⟩
    let t : Spec (.of K) ⟶
        projectiveLinearSystemParameters (K := K) (τ := Fin n) := s ≫ U.ι
    have ht : t ≫ toBase
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
          Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
      change t ≫ toBase
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
          Spec.map (𝟙 (CommRingCat.of K))
      rw [Spec.map_id]
      exact hs
    have hgood : t (IsLocalRing.closedPoint K) ∉
        cubicTwoQuadricUniversalSingularParameterLocus p q hp hq v := by
      change U.ι (s (IsLocalRing.closedPoint K)) ∉
        cubicTwoQuadricUniversalSingularParameterLocus p q hp hq v
      have hsU : U.ι (s (IsLocalRing.closedPoint K)) ∈ (U : Set
          (projectiveLinearSystemParameters (K := K) (τ := Fin n))) :=
        (s (IsLocalRing.closedPoint K)).property
      simpa [U, cubicTwoQuadricUniversalSingularParameterLocus,
        Set.mem_compl_iff] using hsU
    obtain ⟨i, g, _hgbase, _hgt, hempty⟩ :=
      exists_cubicTwoQuadric_parameterChartHom_empty_singularFiber_of_fieldPoint_not_mem_singularParameterLocus
        (RingHom.id K) p q hp hq v t ht hgood
    exact ⟨i, g,
      coordinate_powers_mem_of_isEmpty_projectiveScheme
        (cubicTwoQuadricUniversalSingularChartFiberIdeal p q hp hq v i g)
        hempty⟩
  · rintro ⟨i, g, hcert⟩
    have hempty : IsEmpty (scheme
        (cubicTwoQuadricUniversalSingularChartFiberIdeal
          p q hp hq v i g)) :=
      isEmpty_projectiveScheme_of_coordinate_powers_mem
        (cubicTwoQuadricUniversalSingularChartFiberIdeal p q hp hq v i g)
        hcert
    exact cubicTwoQuadricUniversalSingularParameterLocus_ne_univ_of_fiber_isEmpty
      p q hp hq v i g (fun z => isEmptyElim z)

/-- The same exact certificate criterion for the full quadratic restriction
kernel of an actual finite coefficient algebra. -/
theorem cubicTwoQuadricRestrictionKernelSingularParameterLocus_ne_univ_iff_coordinateCertificate
    {K A : Type u} [Field K] [Infinite K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (x : Fin 4 → A) :
    cubicTwoQuadricRestrictionKernelSingularParameterLocus p q hp hq x ≠ Set.univ ↔
      ∃ (i : Fin (finrank K
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2))))
        (g : ChartRing
          (⊥ : HomogeneousIdeal (homogeneousSubmodule
            (Fin (finrank K
              (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)))) K)) i →+* K),
        let I := cubicTwoQuadricUniversalSingularChartFiberIdeal
          p q hp hq (quadraticRestrictionKernelFrame (K := K) x) i g
        ∀ j : Fin 4,
          ∃ m : ℕ, (MvPolynomial.X j : MvPolynomial (Fin 4) K) ^ m ∈ I.toIdeal := by
  exact cubicTwoQuadricUniversalSingularParameterLocus_ne_univ_iff_coordinateCertificate
    p q hp hq (quadraticRestrictionKernelFrame (K := K) x)

end PfaffianDescent
