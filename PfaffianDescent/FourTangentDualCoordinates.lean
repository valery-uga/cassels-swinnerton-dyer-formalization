import PfaffianDescent.QuarticTangentQuadricBasis
import PfaffianDescent.HomogeneousVanishingLinearSystem
import PfaffianDescent.QuarticConjugateJets
import PfaffianDescent.QuarticHomogeneousJets
import PfaffianDescent.LinearNormalizedProjectivePoint
import PfaffianDescent.NormalizedProjectiveQuotientFactor
import PfaffianDescent.QuadraticFullBaseLocusFiniteTriple

/-! Four actual tangent double points.  The product dual algebra has rank
eight; the sum of the four coordinates is an explicit unit on all four
components, so its projective immersion uses a common chart over EVERY field.
The full quadratic series is the actual dual-algebra evaluation kernel. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev FourTangentDualAlgebra (K : Type u) [Field K] := Fin 4 → DualNumber K

instance fourTangentDualAlgebra_finiteDimensional :
    FiniteDimensional K (FourTangentDualAlgebra K) := by
  letI : Module.Finite K (DualNumber K) := dualNumber_moduleFinite (k := K) (L := K)
  infer_instance

theorem fourTangentDualAlgebra_finrank : Module.finrank K (FourTangentDualAlgebra K) = 8 := by
  change Module.finrank K (Fin 4 → K × K) = 8
  simp [Module.finrank_pi_fintype, Module.finrank_prod]

def fourTangentRawCoordinates (U : Fin 4 → Fin 4 → K) :
    Fin 4 → FourTangentDualAlgebra K := fun j i => tangentDualPoint U i j

def fourTangentChartScale (U : Fin 4 → Fin 4 → K) : FourTangentDualAlgebra K :=
  fun i => 1 - TrivSqZeroExt.inr (∑ j : Fin 4, U i j)

def fourTangentChartScaleInverse (U : Fin 4 → Fin 4 → K) : FourTangentDualAlgebra K :=
  fun i => 1 + TrivSqZeroExt.inr (∑ j : Fin 4, U i j)

theorem fourTangentChartScale_mul_inverse (U : Fin 4 → Fin 4 → K) :
    fourTangentChartScale U * fourTangentChartScaleInverse U = 1 := by
  funext i
  apply TrivSqZeroExt.ext <;>
    simp [fourTangentChartScale, fourTangentChartScaleInverse, DualNumber.snd_mul]

def fourTangentNormalizedCoordinates (U : Fin 4 → Fin 4 → K) :
    Fin 4 → FourTangentDualAlgebra K :=
  fun j => fourTangentChartScale U * fourTangentRawCoordinates U j

def fourTangentChartLinearForm : MvPolynomial (Fin 4) K := ∑ j : Fin 4, X j

theorem fourTangentChartLinearForm_homogeneous :
    (fourTangentChartLinearForm (K := K)).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_X K j

theorem fourTangentRawEvaluation_apply (U : Fin 4 → Fin 4 → K)
    (p : MvPolynomial (Fin 4) K) (i : Fin 4) :
    (aeval (R := K) (fourTangentRawCoordinates U) p) i = aeval (R := K) (tangentDualPoint U i) p := by
  exact comp_aeval_apply (fourTangentRawCoordinates U)
    (Pi.evalAlgHom K (fun _ : Fin 4 => DualNumber K) i) p

theorem fourTangentRawLinearForm_eval (U : Fin 4 → Fin 4 → K) :
    aeval (R := K) (fourTangentRawCoordinates U) (fourTangentChartLinearForm (K := K)) =
      fourTangentChartScaleInverse U := by
  funext i
  rw [fourTangentRawEvaluation_apply]
  apply TrivSqZeroExt.ext <;>
    simp [fourTangentChartLinearForm, tangentDualPoint, fourTangentChartScaleInverse,
      Finset.sum_add_distrib, TrivSqZeroExt.fst_sum, TrivSqZeroExt.snd_sum,
      TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, DualNumber.fst_eps,
      DualNumber.snd_eps]

/-- Explicit multiplication avoids the two different scalar actions on
the nested function spaces of coordinates and dual-point components. -/
theorem fourTangentNormalized_evaluation
    (U : Fin 4 → Fin 4 → K) (p : MvPolynomial (Fin 4) K)
    {d : ℕ} (hp : p.IsHomogeneous d) :
    aeval (R := K) (fourTangentNormalizedCoordinates U) p =
      fourTangentChartScale U ^ d * aeval (R := K) (fourTangentRawCoordinates U) p := by
  exact AllCharacteristics.eval₂_homogeneous_smul p hp
    (algebraMap K (FourTangentDualAlgebra K))
    (fourTangentRawCoordinates U) (fourTangentChartScale U)

theorem fourTangentNormalizedLinearForm_eval (U : Fin 4 → Fin 4 → K) :
    aeval (R := K) (fourTangentNormalizedCoordinates U) (fourTangentChartLinearForm (K := K)) = 1 := by
  rw [fourTangentNormalized_evaluation U _ (fourTangentChartLinearForm_homogeneous (K := K)),
    pow_one, fourTangentRawLinearForm_eval,
    fourTangentChartScale_mul_inverse]

theorem fourTangentNormalizedCoordinates_surjective
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ i, U i i = 0)
    (hn : ∀ i, ∃ j, U i j ≠ 0) :
    Function.Surjective (aeval (R := K) (fourTangentNormalizedCoordinates U)) := by
  intro w
  obtain ⟨p, hp⟩ := tangentCubicRestriction_surjective U hdiag hn
    ((fourTangentChartScaleInverse U) ^ 3 * w)
  refine ⟨p.val, ?_⟩
  have hraw : aeval (R := K) (fourTangentRawCoordinates U) p.val =
      (fourTangentChartScaleInverse U) ^ 3 * w := by
    funext i
    rw [fourTangentRawEvaluation_apply]
    exact congrFun hp i
  rw [fourTangentNormalized_evaluation U _ p.property,
    hraw, ← mul_assoc, ← mul_pow, fourTangentChartScale_mul_inverse, one_pow, one_mul]

/-- Unit normalization loses no homogeneous equation, including equations
which detect nilpotents in the four dual-number components. -/
theorem fourTangentNormalized_eval_zero_iff
    (U : Fin 4 → Fin 4 → K) (p : MvPolynomial (Fin 4) K)
    {d : ℕ} (hp : p.IsHomogeneous d) :
    aeval (R := K) (fourTangentNormalizedCoordinates U) p = 0 ↔
      ∀ i : Fin 4, aeval (R := K) (tangentDualPoint U i) p = 0 := by
  have hunit : IsUnit (fourTangentChartScale U) :=
    isUnit_iff_exists_inv.mpr ⟨fourTangentChartScaleInverse U,
      fourTangentChartScale_mul_inverse U⟩
  rw [fourTangentNormalized_evaluation U p hp]
  constructor
  · intro h
    have hraw : aeval (R := K) (fourTangentRawCoordinates U) p = 0 :=
      (hunit.pow d).mul_left_cancel (by simpa using h)
    intro i
    simpa only [fourTangentRawEvaluation_apply, Pi.zero_apply] using congrFun hraw i
  · intro h
    have hraw : aeval (R := K) (fourTangentRawCoordinates U) p = 0 := by
      funext i
      exact (fourTangentRawEvaluation_apply U p i).trans (h i)
    rw [hraw, mul_zero]

/-- The full homogeneous quadratic kernel of the actual normalized product
algebra is precisely the tangent-jet kernel; no reduction of the algebra is
used in this equality. -/
theorem fourTangentNormalized_quadratic_kernel
    (U : Fin 4 → Fin 4 → K) :
    homogeneousVanishingPolynomialSubmodule (fourTangentNormalizedCoordinates U) 2 =
      homogeneousTangentQuadrics U := by
  ext p
  rw [mem_homogeneousVanishingPolynomialSubmodule_iff,
    mem_homogeneousTangentQuadrics]
  constructor
  · rintro ⟨hp, he⟩
    exact ⟨hp, (fourTangentNormalized_eval_zero_iff U p hp).mp he⟩
  · rintro ⟨hp, he⟩
    exact ⟨hp, (fourTangentNormalized_eval_zero_iff U p hp).mpr he⟩

def fourTangentFullQuadraticBaseIdeal (U : Fin 4 → Fin 4 → K) :=
  quadraticSystemBaseLocusIdeal (homogeneousTangentQuadrics U)
    (fun p hp => (mem_homogeneousTangentQuadrics U p).mp hp |>.1)

theorem fourTangentFullQuadraticBaseIdeal_evaluation_zero
    (U : Fin 4 → Fin 4 → K) :
    ∀ p ∈ (fourTangentFullQuadraticBaseIdeal U).toIdeal,
      p.eval₂ (algebraMap K (FourTangentDualAlgebra K))
        (fourTangentNormalizedCoordinates U) = 0 := by
  have hle : (fourTangentFullQuadraticBaseIdeal U).toIdeal ≤
      RingHom.ker (aeval (R := K) (fourTangentNormalizedCoordinates U)).toRingHom := by
    apply Ideal.span_le.mpr
    intro p hp
    obtain ⟨hp2, heval⟩ := (mem_homogeneousTangentQuadrics U p).mp hp
    exact (fourTangentNormalized_eval_zero_iff U p hp2).mpr heval
  exact fun p hp => hle hp

def fourTangentNormalizedEquationPoint
    (U : Fin 4 → Fin 4 → K)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K (FourTangentDualAlgebra K))
      (fourTangentNormalizedCoordinates U) = 0) :
    Spec (.of (FourTangentDualAlgebra K)) ⟶ scheme I :=
  linearNormalizedPointAt I (fourTangentNormalizedCoordinates U) he
    (Ideal.Quotient.mk I.toIdeal (fourTangentChartLinearForm (K := K)))
    (polynomial_class_mem_grading I _ (fourTangentChartLinearForm_homogeneous (K := K)))
    (by exact fourTangentNormalizedLinearForm_eval U)

def fourTangentDualToFullBase (U : Fin 4 → Fin 4 → K) :=
  fourTangentNormalizedEquationPoint U (fourTangentFullQuadraticBaseIdeal U)
    (fourTangentFullQuadraticBaseIdeal_evaluation_zero U)

theorem fourTangentDualToFullBase_isClosedImmersion
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ i, U i i = 0)
    (hn : ∀ i, ∃ j, U i j ≠ 0) : IsClosedImmersion (fourTangentDualToFullBase U) := by
  exact linearNormalizedPointAt_isClosedImmersion _ _ _ _ _ _
    (fourTangentNormalizedCoordinates_surjective U hdiag hn)

theorem fourTangentDualToFullBase_toBase (U : Fin 4 → Fin 4 → K) :
    fourTangentDualToFullBase U ≫ toBase (fourTangentFullQuadraticBaseIdeal U) =
      Spec.map (CommRingCat.ofHom (algebraMap K (FourTangentDualAlgebra K))) :=
  linearNormalizedPointAt_toBase _ _ _ _ _ _

theorem fourTangentFullQuadraticBaseIdeal_eq_scaled_ideal
    (a b c d e f : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (fourTangentFullQuadraticBaseIdeal (skewTangentDirections a b c d e f)).toIdeal =
      Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro p hp
    obtain ⟨hp2, heval⟩ := (mem_homogeneousTangentQuadrics _ p).mp hp
    exact homogeneous_tangent_quadric_mem_scaledBaseLocus_ideal a b c d e f ha hb hc
      p hp2 heval
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    apply Ideal.subset_span
    exact (mem_homogeneousTangentQuadrics _ _).mpr
      ⟨scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f i,
        scaledBaseLocusQuadricPolynomials_vanish a b c d e f i⟩

end PfaffianDescent.QuarticNet
