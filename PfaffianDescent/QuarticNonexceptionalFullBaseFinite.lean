import PfaffianDescent.FourTangentDualCoordinates
import PfaffianDescent.IntrinsicFiniteCycle
import AllCharacteristics.AffineChartPresentation
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.AlgebraicGeometry.Artinian

/-! The finite branch as an actual finite SCHEME.  The field-valued support
calculation is used only to prove Artinian affine charts by Nullstellensatz;
the tangent subscheme and its length comparison retain the original nilpotents. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

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

private theorem scaled_quadric_eval_eq_cleared
    (a b c d e f : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (x : Fin 4 → K) :
    aeval x (scaledBaseLocusQuadricPolynomials a b c d e f 0) =
        a * b * offDiagonalQuadricEval (baseLocusQuadric1 a b c d e f) x ∧
    aeval x (scaledBaseLocusQuadricPolynomials a b c d e f 1) =
        a * c * offDiagonalQuadricEval (baseLocusQuadric2 a b c d e f) x ∧
    aeval x (scaledBaseLocusQuadricPolynomials a b c d e f 2) =
        b * c * offDiagonalQuadricEval (baseLocusQuadric3 a b c d e f) x := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [scaledBaseLocusQuadricPolynomials, scaledBaseLocusQuadrics,
      offDiagonalQuadric, offDiagonalQuadricEval, baseLocusQuadric1,
      baseLocusQuadric2, baseLocusQuadric3] <;>
    field_simp [ha, hb, hc] <;> ring

/-- The actual full quadratic base scheme is finite in the nonexceptional
branch of the literal geometric base-locus lemma. -/
theorem nonexceptional_fourTangentFullBase_isFinite
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f ≠ 0) :
    IsFinite (toBase (fourTangentFullQuadraticBaseIdeal (skewTangentDirections a b c d e f))) := by
  let U := skewTangentDirections a b c d e f
  let I := fourTangentFullQuadraticBaseIdeal U
  have hI : I.toIdeal = Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) :=
    fourTangentFullQuadraticBaseIdeal_eq_scaled_ideal a b c d e f ha hb hc
  have hcharts : ∀ j : Fin 4, IsArtinianRing (MvPolynomial (Fin 4) K ⧸ chartPresentationIdeal I j) := by
    intro j
    let vertex : Fin 4 → K := fun v => if v = j then 1 else 0
    apply artinian_quotient_of_zeroLocus_subset_singleton _ vertex
    intro x hx
    have hQ (n : Fin 3) : aeval x (scaledBaseLocusQuadricPolynomials a b c d e f n) = 0 := by
      apply hx
      apply (show I.toIdeal ≤ chartPresentationIdeal I j from le_sup_left)
      rw [hI]
      exact Ideal.subset_span (Set.mem_range_self n)
    obtain ⟨h₁, h₂, h₃⟩ := scaled_quadric_eval_eq_cleared a b c d e f ha hb hc x
    obtain ⟨v, hv⟩ := baseLocus_common_zero_is_coordinate_axis_of_delta_ne_zero
      a b c d e f ha hb hc hd he hdelta x
      ((mul_eq_zero.mp (h₁.symm.trans (hQ 0))).resolve_left (mul_ne_zero ha hb))
      ((mul_eq_zero.mp (h₂.symm.trans (hQ 1))).resolve_left (mul_ne_zero ha hc))
      ((mul_eq_zero.mp (h₃.symm.trans (hQ 2))).resolve_left (mul_ne_zero hb hc))
    have hxj : x j = 1 := by
      have hzero := hx (X j - 1)
        ((show Ideal.span {X j - 1} ≤ chartPresentationIdeal I j from le_sup_right)
          (Ideal.subset_span (Set.mem_singleton _)))
      simpa only [map_sub, aeval_X, map_one, sub_eq_zero] using hzero
    have hvj : v = j := by
      by_contra hne
      have hz := hv j (Ne.symm hne)
      exact one_ne_zero (hxj.symm.trans hz)
    subst v
    apply Set.mem_singleton_iff.mpr
    funext v
    by_cases hvj : v = j
    · simp [vertex, hvj, hxj]
    · simpa [vertex, hvj] using hv v hvj
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
  exact PfaffianDescent.isFinite_of_isArtinianScheme_of_locallyOfFiniteType (toBase I)

end PfaffianDescent.QuarticNet
