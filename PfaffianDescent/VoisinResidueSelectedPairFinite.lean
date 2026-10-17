import PfaffianDescent.VoisinFiniteWitnessResidueCoordinates
import PfaffianDescent.VoisinResidueCommonLinearChart
import PfaffianDescent.VoisinSelectedPairFiniteDescent
import PfaffianDescent.VoisinNormalizedQuadraticMinor

/-!
# A finite selected pair over a residue field

Residue coordinates which become independent nonzero row scalings of a
geometric finite witness can be normalized in a common ground-field chart.
The resulting canonical selected pair is finite over the residue field.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem residueCoordinates_selectedQuadraticPair_isFinite
    {K Q L : Type u} [Field K] [Field Q] [Field L]
    [Algebra K Q] [Algebra K L] [Algebra Q L]
    [Infinite K]
    (htower : ∀ a : K,
      algebraMap Q L (algebraMap K Q a) = algebraMap K L a)
    (x₀ : Fin 8 → Fin 4 → Q) (j₀ : Fin 8 → Fin 4)
    (hxj : ∀ i, x₀ i (j₀ i) = 1)
    (y : Fin 8 → Fin 4 → L)
    (s : Fin 8 → L) (hs : ∀ i, s i ≠ 0)
    (hscale : ∀ i k, algebraMap Q L (x₀ i k) = s i * y i k)
    (q r : MvPolynomial (Fin 4) L)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hlin : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩])
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun k i => y i k : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ i, q.eval (y i) = 0 ∧ r.eval (y i) = 0)
    (p : MvPolynomial (Fin 4) Q) (hp : p.IsHomogeneous 3)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap Q L)) q r (hp.map (algebraMap Q L)) hq hr))] :
    ∃ (c : Fin 4 → K) (m : Fin 8 ↪ Monomials (Fin 4) 2),
      let cQ : Fin 4 → Q := fun k => algebraMap K Q (c k)
      let cL : Fin 4 → L := fun k => algebraMap K L (c k)
      let x : Fin 8 → Fin 4 → Q := fun i =>
        normalizedVectorInLinearChart cQ (x₀ i)
      ∃ hm : IsUnit (eightPointQuadraticEvaluationMinor m x).det,
        (∀ i, (homogeneousLinearForm cQ).eval (x₀ i) ≠ 0) ∧
        (∀ i, (homogeneousLinearForm cL).eval (y i) ≠ 0) ∧
        (∀ i k, algebraMap Q L (x i k) =
          normalizedVectorInLinearChart cL (y i) k) ∧
        let hid : IsUnit (eightPointQuadraticEvaluationMinor m
          (fun i k => (RingHom.id Q) (x i k))).det := by simpa using hm
        let b := quadraticSelectedOpenBasisSpecializedBasis
          m x (RingHom.id Q) hid
        IsFinite (relativeTripleIntersectionToBase p
          (quadraticPolynomialOfCoefficients (b 0).1)
          (quadraticPolynomialOfCoefficients (b 1).1) hp
          (quadraticPolynomialOfCoefficients_isHomogeneous (b 0).1)
          (quadraticPolynomialOfCoefficients_isHomogeneous (b 1).1)) := by
  obtain ⟨c, hc₀⟩ :=
    exists_groundField_common_linear_chart_for_normalized_vectors
      (K := K) (Q := Q) x₀ j₀ hxj
  let cQ : Fin 4 → Q := fun k => algebraMap K Q (c k)
  let cL : Fin 4 → L := fun k => algebraMap K L (c k)
  let x : Fin 8 → Fin 4 → Q := fun i =>
    normalizedVectorInLinearChart cQ (x₀ i)
  have hcQ : ∀ i, (homogeneousLinearForm cQ).eval (x₀ i) ≠ 0 := by
    intro i
    simpa only [cQ, homogeneousLinearForm, MvPolynomial.eval_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X] using hc₀ i
  have hmapEval (i : Fin 8) :
      algebraMap Q L ((homogeneousLinearForm cQ).eval (x₀ i)) =
        (homogeneousLinearForm cL).eval
          (fun k => algebraMap Q L (x₀ i k)) := by
    simp only [homogeneousLinearForm, MvPolynomial.eval_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show algebraMap Q L (cQ k) = cL k by
      dsimp only [cQ, cL]
      exact htower (c k)]
  have hcL : ∀ i, (homogeneousLinearForm cL).eval (y i) ≠ 0 := by
    intro i hzero
    have himage : (homogeneousLinearForm cL).eval
        (fun k => algebraMap Q L (x₀ i k)) ≠ 0 := by
      rw [← hmapEval i]
      exact (map_ne_zero (algebraMap Q L)).mpr (hcQ i)
    apply himage
    have hfun : (fun k => algebraMap Q L (x₀ i k)) = s i • y i := by
      funext k
      exact hscale i k
    rw [hfun]
    simp only [homogeneousLinearForm, MvPolynomial.eval_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Pi.smul_apply, smul_eq_mul]
    rw [show (∑ k, cL k * (s i * y i k)) =
        s i * ∑ k, cL k * y i k by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring]
    have hzero' : (∑ k, cL k * y i k) = 0 := by
      simpa only [homogeneousLinearForm, MvPolynomial.eval_sum,
        MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_X] using hzero
    rw [hzero', mul_zero]
  have hxy : ∀ i k, algebraMap Q L (x i k) =
      normalizedVectorInLinearChart cL (y i) k := by
    intro i k
    have hmap := congrFun
      (normalizedVectorInLinearChart_map (algebraMap Q L) cQ (x₀ i)) k
    have hcmap : (fun k => algebraMap Q L (cQ k)) = cL := by
      funext t
      dsimp only [cQ, cL]
      exact htower (c t)
    have hxmap : (fun k => algebraMap Q L (x₀ i k)) = s i • y i := by
      funext t
      exact hscale i t
    change algebraMap Q L (normalizedVectorInLinearChart cQ (x₀ i) k) = _
    rw [hmap, hcmap, hxmap,
      normalizedVectorInLinearChart_smul cL (y i) (s i) (hs i)]
  obtain ⟨m, hmY⟩ :=
    exists_unit_eightPointQuadraticEvaluationMinor_of_surjective y
      (eightPointQuadraticEvaluationMatrix_surjective_of_restriction y hsurj)
  have hmNorm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i => normalizedVectorInLinearChart cL (y i))).det :=
    eightPointQuadraticEvaluationMinor_isUnit_det_normalized y cL hcL m hmY
  have hmQ : IsUnit (eightPointQuadraticEvaluationMinor m x).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    have hmapZero : algebraMap Q L
        (eightPointQuadraticEvaluationMinor m x).det = 0 := by
      rw [hzero, map_zero]
    have hmatrix : (eightPointQuadraticEvaluationMinor m x).map
        (algebraMap Q L) =
        eightPointQuadraticEvaluationMinor m
          (fun i => normalizedVectorInLinearChart cL (y i)) := by
      rw [eightPointQuadraticEvaluationMinor_map]
      congr 2
      funext i k
      exact hxy i k
    have : (eightPointQuadraticEvaluationMinor m
        (fun i => normalizedVectorInLinearChart cL (y i))).det = 0 := by
      rw [← hmatrix]
      have hdetmap := RingHom.map_det (algebraMap Q L)
        (eightPointQuadraticEvaluationMinor m x)
      change algebraMap Q L (eightPointQuadraticEvaluationMinor m x).det =
        ((eightPointQuadraticEvaluationMinor m x).map
          (algebraMap Q L)).det at hdetmap
      rw [← hdetmap]
      exact hmapZero
    exact (isUnit_iff_ne_zero.mp hmNorm) this
  refine ⟨c, m, hmQ, hcQ, hcL, hxy, ?_⟩
  exact selectedQuadraticPair_isFinite_of_extension_specialization
    x m hmQ y cL hcL hxy q r hq hr hlin hsurj hquad p hp

end PfaffianDescent
