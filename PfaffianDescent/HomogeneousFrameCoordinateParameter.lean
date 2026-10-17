import PfaffianDescent.ProjectiveLinearSystem
import PfaffianDescent.LinearNormalizedProjectivePoint

/-!
# Exact projective parameters from frame coefficient vectors

A nonzero coefficient vector in an independent homogeneous frame determines
an actual point of the frame's projective parameter space.  This file keeps
track of the normalized specialized equation and its scalar relation to the
original coefficient combination.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero coefficient vector in an independent homogeneous frame gives
an exact projective linear-system point.  Its image in the full equation
space classifies a nonzero scalar multiple of the original frame
combination. -/
theorem exists_homogeneousFrame_parameter_of_nonzero_coordinates
    {K L : Type u} [Field K] [Field L]
    {σ : Type} [Finite σ] {d m n : ℕ}
    (f : K →+* L) (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q)
    (c : Fin n → L) (hc : c ≠ 0) :
    ∃ (t : Spec (.of L) ⟶
        projectiveLinearSystemParameters (K := K) (τ := Fin n))
      (p : MvPolynomial σ L) (hp : p.IsHomogeneous d) (hne : p ≠ 0)
      (α : L),
      α ≠ 0 ∧
      p = MvPolynomial.C α *
        (∑ j, MvPolynomial.C (c j) * (q j).1.map f) ∧
      t ≫ toBase
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (CommRingCat.ofHom f) ∧
      t ≫ homogeneousFrameToParameters d e q hqli =
        projectiveClassifyingMap p hp hne f := by
  classical
  letI : Algebra K L := f.toAlgebra
  let P : MvPolynomial σ L :=
    ∑ j, MvPolynomial.C (c j) * (q j).1.map f
  have hP : P.IsHomogeneous d := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact ((q j).2.map f).C_mul _
  have hPne : P ≠ 0 :=
    homogeneousFrameCombination_map_ne_zero_of_ne_zero d f e q hqli c hc
  let k : Monomials σ d := chosenEquationCoefficient P hP hPne
  have hk : P.coeff k.1 ≠ 0 :=
    chosenEquationCoefficient_ne_zero P hP hPne
  let i : Fin m := e.symm k
  have hei : e i = k := e.apply_symm_apply k
  let α : L := (P.coeff k.1)⁻¹
  have hα : α ≠ 0 := inv_ne_zero hk
  let y : Fin n → L := fun j ↦ α * c j
  have hy : y ≠ 0 := by
    intro hy0
    apply hc
    funext j
    have hj : α * c j = 0 := congrFun hy0 j
    exact (mul_eq_zero.mp hj).resolve_left hα
  let M := homogeneousFrameCoefficientMatrix d e q
  let F := polynomialQuotientGradingMap (ParameterIdeal K σ d) (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    (projectiveLinearSystemMatrixSubstitution d e M) bot_le
    (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
  let z : CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) := F (coordinate (ParameterIdeal K σ d) (e i))
  have hz : z ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1 :=
    F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))
  let he₀ : ∀ r ∈ (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)).toIdeal,
      (eval₂Hom (algebraMap K L) y) r = 0 := by
    intro r hr
    have hr0 : r = 0 := Ideal.mem_bot.mp hr
    subst r
    exact map_zero _
  have hmulVec : (M.map f).mulVec y i = 1 := by
    calc
      (M.map f).mulVec y i = α * (M.map f).mulVec c i := by
        simp only [Matrix.mulVec, dotProduct, y]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = α * P.coeff (e i).1 := by
        rw [homogeneousFrameCombination_map_coeff d f e q c i]
      _ = 1 := by
        rw [hei]
        exact inv_mul_cancel₀ hk
  have hzOne : (Ideal.Quotient.lift (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)).toIdeal
      (eval₂Hom (algebraMap K L) y) he₀) z = 1 := by
    dsimp only [z]
    rw [projectiveLinearSystemMatrix_gradingMap_coordinate]
    rw [Ideal.Quotient.lift_mk]
    change (rectangularLinearCoordinate M i).eval₂ f y = 1
    rw [eval₂_rectangularLinearCoordinate]
    exact hmulVec
  let g : Away (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) z →+* L :=
    linearNormalizedPointChartMapAt (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) y he₀ z hz hzOne
  have hgbase : g.comp
      (AllCharacteristics.GradedChart.baseMap (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) (z := z)) = f := by
    ext r
    exact linearNormalizedPointChartMapAt_base (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) y he₀ z hz hzOne r
  let p : MvPolynomial σ L :=
    ∑ j, MvPolynomial.C
      (g (linearChartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) z hz j)) * (q j).1.map f
  let hp : p.IsHomogeneous d := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact ((q j).2.map f).C_mul _
  let hne : p ≠ 0 :=
    homogeneousFrame_awayMap_combination_ne_zero d e q hqli i g f hgbase
  let t : Spec (.of L) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n) :=
    linearNormalizedPointAt (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) y he₀ z hz hzOne
  have htbase : t ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) = Spec.map (CommRingCat.ofHom f) := by
    exact linearNormalizedPointAt_toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) y he₀ z hz hzOne
  have htclass : t ≫ homogeneousFrameToParameters d e q hqli =
      projectiveClassifyingMap p hp hne f := by
    have h := homogeneousFrame_chartPoint_toParameters_eq_classifying
      d e q hqli i g f hgbase
    have htdef : t = Spec.map (CommRingCat.ofHom g) ≫
        Proj.awayι
          (grading (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin n) K))) z hz
          (by decide : 0 < 1) := by rfl
    rw [htdef]
    convert h using 1 <;>
      simp only [M, F, z, p, hp, hne]
    exact Category.assoc _ _ _
  have hpScale : p = MvPolynomial.C α * P := by
    dsimp only [p, P]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [linearNormalizedPointChartMapAt_coordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) y he₀ z hz hzOne]
    dsimp only [y]
    simp only [map_mul, MvPolynomial.map_C]
    ring
  exact ⟨t, p, hp, hne, α, hα, hpScale, htbase, htclass⟩

end PfaffianDescent
