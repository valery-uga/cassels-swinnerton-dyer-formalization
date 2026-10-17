import PfaffianDescent.QuarticFourCycleQuadricBasis
import PfaffianDescent.FourTangentIntrinsicQuadraticSystem
import PfaffianDescent.IntrinsicFiniteCycle
import AllCharacteristics.AffineChartPresentation
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.AlgebraicGeometry.Artinian

/-! SOURCE ONLY, UNVERIFIED. The actual FULL four-cycle quadratic base is
finite. Field-valued chart support is used only to derive Artinian charts;
the actual homogeneous ideal and scheme retain their nilpotents. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem two_coordinates_zero_of_product_and_linear
    (a b y z : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : y * z = 0) (hl : a * y + b * z = 0) : y = 0 ∧ z = 0 := by
  rcases mul_eq_zero.mp hp with hy | hz
  · refine ⟨hy, ?_⟩
    have h : b * z = 0 := by simpa only [hy, mul_zero, zero_add] using hl
    exact (mul_eq_zero.mp h).resolve_left hb
  · refine ⟨?_, hz⟩
    have h : a * y = 0 := by simpa only [hz, mul_zero, add_zero] using hl
    exact (mul_eq_zero.mp h).resolve_left ha

theorem fourCycle_quadrics_normalized_common_zero
    (b c d e : K) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (x : Fin 4 → K) (j : Fin 4) (hxj : x j = 1)
    (hQ : ∀ n : Fin 3, aeval x (fourCycleScaledQuadricPolynomials b c d e n) = 0) :
    x = fun m => if m = j then 1 else 0 := by
  have h01 : x 0 * x 1 = 0 := by
    simpa [fourCycleScaledQuadricPolynomials, fourCycleScaledQuadrics,
      offDiagonalQuadric] using hQ 0
  have h23 : x 2 * x 3 = 0 := by
    simpa [fourCycleScaledQuadricPolynomials, fourCycleScaledQuadrics,
      offDiagonalQuadric] using hQ 1
  have hcross : c * d * e * x 0 * x 2 + (-b * d * e) * x 0 * x 3 +
      (-b * c * e) * x 1 * x 2 + b * c * d * x 1 * x 3 = 0 := by
    simpa [fourCycleScaledQuadricPolynomials, fourCycleScaledQuadrics,
      offDiagonalQuadric] using hQ 2
  fin_cases j
  · change x 0 = 1 at hxj
    have hx1 : x 1 = 0 := by simpa only [hxj, one_mul] using h01
    have hlin : (c * d * e) * x 2 + (-b * d * e) * x 3 = 0 := by
      simpa only [hxj, hx1, mul_one, mul_zero, zero_mul, add_zero] using hcross
    obtain ⟨hx2, hx3⟩ := two_coordinates_zero_of_product_and_linear _ _ _ _
      (mul_ne_zero (mul_ne_zero hc hd) he)
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hb) hd) he) h23 hlin
    funext m
    fin_cases m <;> simp [hxj, hx1, hx2, hx3]
  · change x 1 = 1 at hxj
    have hx0 : x 0 = 0 := by simpa only [hxj, mul_one] using h01
    have hlin : (-b * c * e) * x 2 + (b * c * d) * x 3 = 0 := by
      simpa only [hxj, hx0, mul_one, mul_zero, zero_mul, zero_add] using hcross
    obtain ⟨hx2, hx3⟩ := two_coordinates_zero_of_product_and_linear _ _ _ _
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hb) hc) he)
      (mul_ne_zero (mul_ne_zero hb hc) hd) h23 hlin
    funext m
    fin_cases m <;> simp [hxj, hx0, hx2, hx3]
  · change x 2 = 1 at hxj
    have hx3 : x 3 = 0 := by simpa only [hxj, one_mul] using h23
    have hlin : (c * d * e) * x 0 + (-b * c * e) * x 1 = 0 := by
      have hh : c * d * e * x 0 + -b * c * e * x 1 = 0 := by
        simpa only [hxj, hx3, mul_one, mul_zero, add_zero, zero_add] using hcross
      exact hh
    obtain ⟨hx0, hx1⟩ := two_coordinates_zero_of_product_and_linear _ _ _ _
      (mul_ne_zero (mul_ne_zero hc hd) he)
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hb) hc) he) h01 hlin
    funext m
    fin_cases m <;> simp [hxj, hx3, hx0, hx1]
  · change x 3 = 1 at hxj
    have hx2 : x 2 = 0 := by simpa only [hxj, mul_one] using h23
    have hlin : (-b * d * e) * x 0 + (b * c * d) * x 1 = 0 := by
      simpa only [hxj, hx2, mul_one, mul_zero, zero_add, add_zero] using hcross
    obtain ⟨hx0, hx1⟩ := two_coordinates_zero_of_product_and_linear _ _ _ _
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hb) hd) he)
      (mul_ne_zero (mul_ne_zero hb hc) hd) h01 hlin
    funext m
    fin_cases m <;> simp [hxj, hx2, hx0, hx1]

/-- Equality of the actual entire homogeneous ideals, not their radicals.
This is the literal three-equation description of the four-cycle full base. -/
theorem fourCycleFullQuadraticBaseIdeal_eq_scaled_ideal
    (b c d e : K) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    (fourTangentFullQuadraticBaseIdeal (skewTangentDirections 0 b c d e 0)).toIdeal =
      Ideal.span (Set.range (fourCycleScaledQuadricPolynomials b c d e)) := by
  change Ideal.span (homogeneousTangentQuadrics
    (skewTangentDirections 0 b c d e 0) : Set (MvPolynomial (Fin 4) K)) = _
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro p hp
    obtain ⟨hhom, hvan⟩ := (mem_homogeneousTangentQuadrics _ _).mp hp
    exact homogeneous_tangent_quadric_mem_fourCycleScaled_ideal
      b c d e hb hc hd he p hhom hvan
  · apply Ideal.span_le.mpr
    rintro p ⟨n, rfl⟩
    apply Ideal.subset_span
    exact (mem_homogeneousTangentQuadrics _ _).mpr
      ⟨fourCycleScaledQuadricPolynomials_homogeneous b c d e n,
        fourCycleScaledQuadricPolynomials_vanish b c d e n⟩

private theorem artinian_quotient_of_zeroLocus_subset_singleton
    (J : Ideal (MvPolynomial (Fin 4) K)) (x : Fin 4 → K)
    (hzero : MvPolynomial.zeroLocus K J ⊆ {x}) :
    IsArtinianRing (MvPolynomial (Fin 4) K ⧸ J) := by
  apply isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr
  refine ⟨inferInstance, ?_⟩
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro P hP
  have hV : MvPolynomial.vanishingIdeal K {x} ≤ J.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) J]
    exact MvPolynomial.vanishingIdeal_anti_mono hzero
  have hVP : MvPolynomial.vanishingIdeal K {x} ≤ P :=
    hV.trans (hP.isPrime.radical_le_iff.mpr hP.le)
  have hEq : MvPolynomial.vanishingIdeal K {x} = P :=
    (inferInstance : (MvPolynomial.vanishingIdeal K {x}).IsMaximal).eq_of_le
      hP.isPrime.ne_top hVP
  exact hEq ▸ inferInstance


/-- No chosen finite triple or finite-base certificate: the three explicit
four-cycle quadrics are actual members of the full nilpotent-sensitive ideal. -/
theorem fourCycle_intrinsicFullQuadraticBase_isFinite
    (b c d e : K) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
      (fourTangentDualToProjective (skewTangentDirections 0 b c d e 0) ≫
        quotientProjMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))))) := by
  let U := skewTangentDirections 0 b c d e 0
  let I := fourTangentFullQuadraticBaseIdeal U
  have hmem (n : Fin 3) : fourCycleScaledQuadricPolynomials b c d e n ∈ I.toIdeal := by
    apply Ideal.subset_span
    exact (mem_homogeneousTangentQuadrics U _).mpr
      ⟨fourCycleScaledQuadricPolynomials_homogeneous b c d e n,
        fourCycleScaledQuadricPolynomials_vanish b c d e n⟩
  have hcharts : ∀ j : Fin 4, IsArtinianRing (MvPolynomial (Fin 4) K ⧸ chartPresentationIdeal I j) := by
    intro j
    let vertex : Fin 4 → K := fun m => if m = j then 1 else 0
    apply artinian_quotient_of_zeroLocus_subset_singleton _ vertex
    intro x hx
    have hQ (n : Fin 3) : aeval x (fourCycleScaledQuadricPolynomials b c d e n) = 0 := by
      exact hx _ ((show I.toIdeal ≤ chartPresentationIdeal I j from le_sup_left) (hmem n))
    have hxj : x j = 1 := by
      have hz := hx (X j - 1)
        ((show Ideal.span {X j - 1} ≤ chartPresentationIdeal I j from le_sup_right)
          (Ideal.subset_span (Set.mem_singleton _)))
      simpa only [map_sub, aeval_X, map_one, sub_eq_zero] using hz
    exact Set.mem_singleton_iff.mpr
      (fourCycle_quadrics_normalized_common_zero b c d e hb hc hd he x j hxj hQ)
  have hArt : ∀ j : Fin 4, IsArtinianRing (ChartRing I j) := by
    intro j
    letI := hcharts j
    exact (chartPresentationEquiv I j).isArtinianRing
  letI : IsLocallyArtinian (scheme I) :=
    (isLocallyArtinian_iff_openCover (coordinateOpenCover I).openCover).mpr (by
      intro j
      letI := hArt j
      exact (Scheme.isLocallyArtinianScheme_Spec
        (R := CommRingCat.of (ChartRing I j))).mpr inferInstance)
  letI : CompactSpace (scheme I) := QuasiCompact.compactSpace_of_compactSpace (toBase I)
  letI : IsArtinianScheme (scheme I) := ⟨⟩
  have hfinite : IsFinite (toBase I) :=
    PfaffianDescent.isFinite_of_isArtinianScheme_of_locallyOfFiniteType (toBase I)
  have hI : intrinsicFullQuadraticBaseIdeal
      (fourTangentDualToProjective U ≫ quotientProjMap ⊥) = I :=
    fourTangent_intrinsicFullQuadraticBaseIdeal_eq U
      (skewTangentDirections_diagonal_zero 0 b c d e 0)
  change IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
    (fourTangentDualToProjective U ≫ quotientProjMap ⊥)))
  rw [hI]
  exact hfinite

end PfaffianDescent.QuarticNet
