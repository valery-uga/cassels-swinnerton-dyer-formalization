import PfaffianDescent.QuotientChartKernel
import AllCharacteristics.NormalizedChartGeneration
import Mathlib.RingTheory.Localization.Basic

/-! SOURCE ONLY / UNVERIFIED153. A genuine homogeneous equation of a whole
closed subscheme which survives in an ambient graded domain survives on every
standard chart whose coordinate is nonzero. This is the native bridge for the
Hilbert-growth route to proving the ACTUAL whole finite-cut kernel nonzero.
Actual whole-ideal elimination and the actual surviving equation are still
to be constructed; neither is silently supplied to an actual Cartier caller. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial HomogeneousLocalization
open scoped nonZeroDivisors
open AllCharacteristics.HomogeneousProjective
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A surviving homogeneous numerator in an actual graded domain stays
nonzero after normalization by ANY surviving coordinate. -/
theorem homogeneousPolynomial_chartEvaluation_ne_zero
    (I : HomogeneousIdeal (homogeneousSubmodule σ R))
    [IsDomain (CoordinateRing I)] (j : σ) (hj : coordinate I j ≠ 0)
    (f : MvPolynomial σ R) {d : ℕ} (hf : f.IsHomogeneous d) (hfI : f ∉ I.toIdeal) :
    f.eval₂ (chartBaseMap I j) (chartCoordinate I j) ≠ 0 := by
  let A := CoordinateRing I
  let M := Submonoid.powers (coordinate I j)
  let L := Localization M
  have hM : M ≤ nonZeroDivisors A := by
    intro a ha
    obtain ⟨n, rfl⟩ := ha
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hj)
  have hinj : Function.Injective (algebraMap A L) := IsLocalization.injective L hM
  have hnum : Ideal.Quotient.mk I.toIdeal f ≠ 0 :=
    fun hzero => hfI (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  intro hzero
  have hval := congrArg HomogeneousLocalization.val hzero
  rw [eval₂_chartCoordinate_eq_fraction I j f hf, Away.val_mk, val_zero] at hval
  let den : M := ⟨coordinate I j ^ d, ⟨d, rfl⟩⟩
  have hfrac : IsLocalization.mk' L (Ideal.Quotient.mk I.toIdeal f) den = 0 := by
    simpa only [Localization.mk_eq_mk'] using hval
  have hspec := IsLocalization.mk'_spec L (Ideal.Quotient.mk I.toIdeal f) den
  rw [hfrac, zero_mul] at hspec
  exact hnum (hinj (by simpa only [map_zero] using hspec.symm))

end PfaffianDescent.Coray


noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual homogeneous member of the ENTIRE larger ideal which survives
in the ambient coordinate domain gives a nonzero actual chart kernel. -/
theorem chartQuotientMap_ker_ne_bot_of_surviving_homogeneous_member
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R))
    (hIJ : I.toIdeal ≤ J.toIdeal) [IsDomain (CoordinateRing I)]
    (j : σ) (hj : coordinate I j ≠ 0)
    (f : MvPolynomial σ R) {d : ℕ} (hf : f.IsHomogeneous d)
    (hfJ : f ∈ J.toIdeal) (hfI : f ∉ I.toIdeal) :
    RingHom.ker (PfaffianDescent.chartQuotientMap I J hIJ j) ≠ ⊥ := by
  let v := f.eval₂ (chartBaseMap I j) (chartCoordinate I j)
  have hv0 : v ≠ 0 := homogeneousPolynomial_chartEvaluation_ne_zero I j hj f hf hfI
  have hvker : v ∈ RingHom.ker (PfaffianDescent.chartQuotientMap I J hIJ j) := by
    change PfaffianDescent.chartQuotientMap I J hIJ j v = 0
    rw [PfaffianDescent.chartQuotientMap_eval₂]
    exact eval₂_chartCoordinate_eq_zero_of_mem J j f hfJ
  intro hbot
  rw [hbot] at hvker
  exact hv0 hvker

end PfaffianDescent.Coray
