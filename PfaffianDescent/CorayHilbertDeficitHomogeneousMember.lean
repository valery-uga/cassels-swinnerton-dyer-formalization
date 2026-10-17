import PfaffianDescent.HomogeneousQuotientMap
import PfaffianDescent.HomogeneousProjection

/- SOURCE ONLY154; no compiler/options/limit changes. -/

/- Source snapshot: /private/tmp/cassels-coray-plane-cubic-hilbert-surviving-equation-source154/new/PfaffianDescent/CorayHilbertDeficitHomogeneousMember.lean prefix through preceding bounded frontier -/
/-! SOURCE ONLY / UNVERIFIED154. A strict deficit of ACTUAL quotient-grade
ranks constructs a surviving homogeneous member of the ENTIRE larger ideal.
Actual pair growth then supplies that deficit from a bounded eventual target
Hilbert function. No prime/reduced/Cartier premise on the larger ideal. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual grade map for arbitrary finite variable sets. -/
def finiteVariableCoordinateQuotientGradeMap
    {σ : Type} (I J : HomogeneousIdeal (homogeneousSubmodule σ K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) : grading I d →ₗ[K] grading J d where
  toFun x := ⟨(Ideal.Quotient.factorₐ K hIJ) x.val,
    PfaffianDescent.coordinateQuotientMap_mem I J hIJ x.property⟩
  map_add' x y := Subtype.ext (map_add (Ideal.Quotient.factorₐ K hIJ) x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (Ideal.Quotient.factorₐ K hIJ) c x.val)

/-- Rank deficit cannot be represented by an injective actual quotient
map: extracting a homogeneous preimage gives a genuine surviving equation. -/
theorem homogeneousMember_of_strictCoordinateGrade_finrank
    {σ : Type} [Finite σ] (I J : HomogeneousIdeal (homogeneousSubmodule σ K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ)
    (hdeficit : finrank K (grading J d) < finrank K (grading I d)) :
    ∃ f : MvPolynomial σ K, f.IsHomogeneous d ∧ f ∈ J.toIdeal ∧ f ∉ I.toIdeal := by
  classical
  let q := finiteVariableCoordinateQuotientGradeMap I J hIJ d
  letI : Module.Finite K (grading J d) := by
    change Module.Finite K ((homogeneousSubmodule σ K d).map
      (Ideal.Quotient.mkₐ K J.toIdeal).toLinearMap)
    infer_instance
  by_contra hnone
  push Not at hnone
  have hinj : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    rw [Submodule.mem_bot]
    apply Subtype.ext
    obtain ⟨f, hfd, hf⟩ := x.property
    change Ideal.Quotient.mk I.toIdeal f = x.val at hf
    have hxzero := congrArg Subtype.val hx
    change (Ideal.Quotient.factorₐ K hIJ) x.val = 0 at hxzero
    have hfJ : f ∈ J.toIdeal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change (Ideal.Quotient.factorₐ K hIJ) (Ideal.Quotient.mk I.toIdeal f) = 0
      rw [hf]
      exact hxzero
    have hfI := hnone f hfd hfJ
    exact hf.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hfI)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  exact (not_lt_of_ge hle) hdeficit

end PfaffianDescent.Coray
