import PfaffianDescent.SmoothCubicFieldPointChartGradient
import PfaffianDescent.QuarticHomogeneousJets
import Mathlib.Data.Fin.SuccPred

/-! Move the actual selected coordinate chart to coordinate zero internally.
Its nonzero affine differential comes from the original smooth cubic's
retained partial, without a new smoothness certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace QuarticNet

theorem pderiv_dehomogenizeAtZero
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (i : Fin 3) :
    pderiv i (dehomogenizeAtZero p) = dehomogenizeAtZero (pderiv i.succ p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [dehomogenizeAtZero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, pderiv_mul, pderiv_mul, map_add, map_mul, map_mul, hp]
    fin_cases i <;> fin_cases j <;> simp [dehomogenizeAtZero, pderiv_X]

theorem aeval_dehomogenizeAtZero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (b : Fin 4 → L) (hb : b 0 = 1) :
    aeval (fun i : Fin 3 => b i.succ) (dehomogenizeAtZero p) = aeval b p := by
  have h : (aeval (fun i : Fin 3 => b i.succ)).comp
      (dehomogenizeAtZero (k := K)) = aeval b := by
    ext i : 1
    fin_cases i <;> simp [dehomogenizeAtZero, hb]
  exact AlgHom.congr_fun h p

end QuarticNet

theorem smoothCubic_actualChart_swapped_affineDifferential_ne_zero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (j : Fin 4) (g : ChartRing (equationIdeal p hp) j →+* L)
    (hbase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K L)
    (b : Fin 4 → L) (hb : ∀ a, b a = g (chartCoordinate (equationIdeal p hp) j a)) :
    QuarticNet.affineDifferential
      (fun i : Fin 3 => b ((Equiv.swap (0 : Fin 4) j) i.succ))
      (QuarticNet.dehomogenizeAtZero (rename (Equiv.swap (0 : Fin 4) j) p)) ≠ 0 := by
  classical
  let σ := Equiv.swap (0 : Fin 4) j
  let b' : Fin 4 → L := fun a => b (σ a)
  have hb0 : b' 0 = 1 := by
    simp only [b', σ, Equiv.swap_apply_left]
    rw [hb, chartCoordinate_self, map_one]
  obtain ⟨a, ha⟩ := smoothCubic_fieldPoint_chart_exists_nonzero_retained_partial p hp hp0 j g hbase
  have hσa : σ a.1 ≠ 0 := by
    intro h
    have := congrArg σ h
    have ha0 : a.1 = j := by simpa [σ] using this
    exact a.2 ha0
  obtain ⟨r, hr⟩ := Fin.exists_succ_eq_of_ne_zero hσa
  have hderiv : aeval (fun i : Fin 3 => b' i.succ)
      (pderiv r (QuarticNet.dehomogenizeAtZero (rename σ p))) ≠ 0 := by
    rw [QuarticNet.pderiv_dehomogenizeAtZero, hr,
      pderiv_rename σ.injective,
      QuarticNet.aeval_dehomogenizeAtZero _ b' hb0, aeval_rename]
    have heq : b' ∘ σ = b := by
      funext i
      simp [Function.comp_def, b', σ]
    rw [heq]
    rw [show b = (fun a => g (chartCoordinate (equationIdeal p hp) j a)) from funext hb]
    simpa only [aeval_def] using ha
  intro hzero
  have h := congrArg (fun f : (Fin 3 → L) →ₗ[L] L => f (Pi.single r 1)) hzero
  have hval : QuarticNet.affineDifferential (fun i : Fin 3 => b' i.succ)
      (QuarticNet.dehomogenizeAtZero (rename σ p)) (Pi.single r 1) =
      aeval (fun i : Fin 3 => b' i.succ)
        (pderiv r (QuarticNet.dehomogenizeAtZero (rename σ p))) := by
    simp [QuarticNet.affineDifferential, Pi.single_apply]
  apply hderiv
  change QuarticNet.affineDifferential (fun i : Fin 3 => b' i.succ)
      (QuarticNet.dehomogenizeAtZero (rename σ p)) (Pi.single r 1) = 0 at h
  rw [hval] at h
  exact h

end PfaffianDescent
