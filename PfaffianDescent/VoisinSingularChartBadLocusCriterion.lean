import PfaffianDescent.VoisinRestrictionKernelEtale
import PfaffianDescent.ProjectiveCoordinateNilpotentEmpty
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Detecting a good cubic parameter from its specialized singular fibre

The chart bad locus is the image of the universal simultaneous-zero
family.  The projective coefficient-change square is Cartesian, so a
point of that family over a field-valued parameter would give a point
of the specialized singular fibre.  Emptiness of that fibre therefore
certifies that the parameter is outside the bad locus.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An empty Cartesian base change certifies that its base point is outside
the image of the original family. -/
theorem not_mem_range_of_isEmpty_isPullback
    {X Y S Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ X) (k : Z ⟶ Y)
    (sq : IsPullback h k f g)
    (y : Y) (hEmpty : ∀ _z : Z, False) :
    g y ∉ Set.range f := by
  rintro ⟨x, hx⟩
  obtain ⟨w, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := g) x y hx
  exact hEmpty (sq.isoPullback.inv w)

theorem tripleCompleteIntersectionUniversalSingularChart_not_mem_range_of_fiber_isEmpty
    {K L : Type u} [Field K] [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (hEmpty : ∀ _z : scheme
      (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
        p q hp hq v i g), False) :
    Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L) ∉
      Set.range (toBase
        (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
          p q hp hq v i)) := by
  let J := tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
    p q hp hq v i
  let J' := tripleCompleteIntersectionUniversalSingularChartFiberIdeal
    p q hp hq v i g
  let b : Spec (.of L) ⟶ Spec (.of
      (ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) :=
    Spec.map (CommRingCat.ofHom g)
  have hsq : IsPullback
      (tripleCompleteIntersectionUniversalSingularChartFiberToFamily
        p q hp hq v i g) (toBase J') (toBase J) b :=
    isPullback_projectiveCoefficientMap g J J'
      (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal_map_eq_fiber
        p q hp hq v i g)
  exact not_mem_range_of_isEmpty_isPullback (toBase J) b
    (tripleCompleteIntersectionUniversalSingularChartFiberToFamily
      p q hp hq v i g) (toBase J') hsq
    (IsLocalRing.closedPoint L) hEmpty

theorem tripleCompleteIntersectionUniversalSingularChartBadLocus_eq_range
    {K : Type u} [Field K] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n) :
    tripleCompleteIntersectionUniversalSingularChartBadLocus p q hp hq v i =
      Set.range (toBase
        (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
          p q hp hq v i)) := by
  simp only [tripleCompleteIntersectionUniversalSingularChartBadLocus,
    tripleCompleteIntersectionUniversalSingularChartFamilyToBase]

/-- A field-valued parameter is outside the actual closed bad locus when
its specialized projective Jacobian fibre is empty. -/
theorem tripleCompleteIntersectionUniversalSingularChart_not_mem_badLocus_of_fiber_isEmpty
    {K L : Type u} [Field K] [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (hEmpty : ∀ _z : scheme
      (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
        p q hp hq v i g), False) :
    Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L) ∉
      tripleCompleteIntersectionUniversalSingularChartBadLocus
        p q hp hq v i := by
  rw [tripleCompleteIntersectionUniversalSingularChartBadLocus_eq_range]
  exact tripleCompleteIntersectionUniversalSingularChart_not_mem_range_of_fiber_isEmpty
    p q hp hq v i g hEmpty

/-- One field-valued parameter with empty specialized singular fibre proves
that the universal bad locus is a proper subset of the parameter space. -/
theorem tripleCompleteIntersectionUniversalSingularParameterLocus_ne_univ_of_fiber_isEmpty
    {K L : Type u} [Field K] [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (hEmpty : ∀ _z : scheme
      (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
        p q hp hq v i g), False) :
    tripleCompleteIntersectionUniversalSingularParameterLocus
      p q hp hq v ≠ Set.univ := by
  let y : Spec (.of
      (ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) :=
    Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L)
  have hy : y ∉ tripleCompleteIntersectionUniversalSingularChartBadLocus
      p q hp hq v i :=
    tripleCompleteIntersectionUniversalSingularChart_not_mem_badLocus_of_fiber_isEmpty
      p q hp hq v i g hEmpty
  have hgood :
      chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i y ∈
        tripleCompleteIntersectionUniversalNonsingularParameterLocus
          p q hp hq v := by
    simp only [tripleCompleteIntersectionUniversalNonsingularParameterLocus,
      Set.mem_iUnion]
    exact ⟨i, y, hy, rfl⟩
  intro hbad
  have hsing : chartι
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i y ∈
        tripleCompleteIntersectionUniversalSingularParameterLocus
          p q hp hq v := by
    rw [hbad]
    trivial
  exact (by simpa only
    [tripleCompleteIntersectionUniversalSingularParameterLocus,
      Set.mem_compl_iff] using hsing :
        chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i y ∉
          tripleCompleteIntersectionUniversalNonsingularParameterLocus
            p q hp hq v) hgood

/-- For the complete cubic restriction kernel, one field-valued cubic whose
specialized Jacobian singular fibre is empty discharges the properness
premise used by the degree-ten residual construction. -/
theorem tripleCompleteIntersectionRestrictionKernelSingularParameterLocus_ne_univ_of_fiber_isEmpty
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → A)
    (i : cubicRestrictionKernelParameterIndex (K := K) x)
    (g : cubicRestrictionKernelParameterChartRing (K := K) x i →+* L)
    (hEmpty : ∀ _z : scheme
      (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
        p q hp hq (cubicRestrictionKernelFrame (K := K) x) i g), False) :
    tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
      p q hp hq x ≠ Set.univ := by
  exact tripleCompleteIntersectionUniversalSingularParameterLocus_ne_univ_of_fiber_isEmpty
    p q hp hq (cubicRestrictionKernelFrame (K := K) x) i g hEmpty

/-- Four finite polynomial ideal-membership certificates, one power of each
projective coordinate, certify properness of the full restriction-kernel
singular locus. This is an algebraic target for a selected-cubic Jacobian
calculation. -/
theorem tripleCompleteIntersectionRestrictionKernelSingularParameterLocus_ne_univ_of_coordinate_powers_mem
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → A)
    (i : cubicRestrictionKernelParameterIndex (K := K) x)
    (g : cubicRestrictionKernelParameterChartRing (K := K) x i →+* L)
    (hcert :
      let I := tripleCompleteIntersectionUniversalSingularChartFiberIdeal
        p q hp hq (cubicRestrictionKernelFrame (K := K) x) i g
      ∀ j : Fin 4,
        ∃ n : ℕ, (MvPolynomial.X j : MvPolynomial (Fin 4) L) ^ n ∈ I.toIdeal) :
    tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
      p q hp hq x ≠ Set.univ := by
  let I := tripleCompleteIntersectionUniversalSingularChartFiberIdeal
    p q hp hq (cubicRestrictionKernelFrame (K := K) x) i g
  have hEmpty : IsEmpty (scheme I) :=
    isEmpty_projectiveScheme_of_coordinate_powers_mem I hcert
  exact tripleCompleteIntersectionRestrictionKernelSingularParameterLocus_ne_univ_of_fiber_isEmpty
    p q hp hq x i g (fun z => isEmptyElim z)

/-- Properness of the restriction-kernel singular-member locus produces a
ground-field chart whose specialized singular fiber has a finite algebraic
emptiness certificate: a power of each projective coordinate lies in the
fiber ideal. -/
theorem exists_groundFieldRestrictionKernel_parameterChart_coordinatePowers_of_singularLocus_ne_univ
    {K : Type u} [Field K] [Infinite K] {A : Type u} [CommRing A]
    [Algebra K A] [FiniteDimensional K A]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → A)
    (hproper : tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
      p q hp hq x ≠ Set.univ) :
    ∃ (i : cubicRestrictionKernelParameterIndex (K := K) x)
      (g : cubicRestrictionKernelParameterChartRing (K := K) x i →+* K),
      cubicRestrictionKernelSpecializedBaseMap (K := K) x i g = RingHom.id K ∧
      ∀ j : Fin 4, ∃ n : ℕ,
        (MvPolynomial.X j : MvPolynomial (Fin 4) K) ^ n ∈
          (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
            p q hp hq (cubicRestrictionKernelFrame (K := K) x) i g).toIdeal := by
  obtain ⟨i, g, hbase, hempty⟩ :=
    PfaffianDescent.exists_groundField_parameterChartHom_empty_singularFiber_of_singularParameterLocus_ne_univ
      p q hp hq (cubicRestrictionKernelFrame (K := K) x) hproper
  refine ⟨i, g, ?_, ?_⟩
  · simpa [cubicRestrictionKernelSpecializedBaseMap] using hbase
  · exact coordinate_powers_mem_of_isEmpty_projectiveScheme
      (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
        p q hp hq (cubicRestrictionKernelFrame (K := K) x) i g) hempty

end PfaffianDescent
