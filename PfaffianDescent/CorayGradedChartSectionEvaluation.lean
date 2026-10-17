import AllCharacteristics.GradedChartCoordinates
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Source-only / unverified. A degree-n section is divided by the
actual degree-one chart coordinate to the SAME power n. This is linear
for the existing graded-localization action. Domain hypotheses prove
injectivity; neither tangent rank nor a regular member is assumed. -/
noncomputable section
namespace PfaffianDescent.Coray
open HomogeneousLocalization
universe u v w

section
variable {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]
variable (G : ℕ → Submodule K A) [GradedRing G] {z : A} (hz : z ∈ G 1)

/-- The installed localization already has its original K scalar action.
Transport only the module LAWS through its injective valuation; the action
is retained, rather than reconstructed from an unpinned algebra instance.
This instance is scoped to the new Coray evaluation leaves. -/
scoped instance gradedChartNativeModule : Module K (Away G z) :=
  Function.Injective.module K
    (show Away G z →+ Localization (.powers z) from
      { toFun := HomogeneousLocalization.val
        map_zero' := val_zero
        map_add' := val_add })
    (val_injective (.powers z)) (val_smul (.powers z))

open scoped PfaffianDescent.Coray

/-- Actual degree-n sections as functions in the chart D_+(z). -/
def gradedChartSectionEvaluation (n : ℕ) : G n →ₗ[K] Away G z where
  toFun s := Away.mk G hz n s.1 (by simpa only [smul_eq_mul, mul_one] using s.2)
  map_add' s t := by
    apply val_injective (.powers z)
    simp only [Away.val_mk, val_add, Submodule.coe_add]
    exact (Localization.add_mk_self _ _ _).symm
  map_smul' c s := by
    apply val_injective (.powers z)
    simp only [Away.val_mk, val_smul, Submodule.coe_smul]
    rw [Localization.smul_mk]
    rfl

/-- Its numerator and denominator in the ordinary localization are
literally the original section and z^n. -/
theorem gradedChartSectionEvaluation_val (n : ℕ) (s : G n) :
    (gradedChartSectionEvaluation G hz n s).val =
      (Localization.mk s.1 ⟨z ^ n, by use n⟩ : Localization (.powers z)) := rfl

variable [IsDomain A]

/-- No nonzero SAME-degree section disappears in a nonempty chart of
an integral cone. This is a localization proof, not a rank input. -/
theorem gradedChartSectionEvaluation_injective (hz0 : z ≠ 0) (n : ℕ) :
    Function.Injective (gradedChartSectionEvaluation G hz n) := by
  intro s t h
  let L := Localization (.powers z)
  let d : Submonoid.powers z := ⟨z ^ n, by use n⟩
  have hv := congrArg HomogeneousLocalization.val h
  change (Localization.mk s.1 d : L) = Localization.mk t.1 d at hv
  have hm := congrArg (fun a : L => a * algebraMap A L (d : A)) hv
  rw [Localization.mk_eq_mk', IsLocalization.mk'_spec,
    IsLocalization.mk'_spec] at hm
  apply Subtype.ext
  exact IsLocalization.injective L
    (powers_le_nonZeroDivisors_of_noZeroDivisors hz0) hm

end

section
variable {K : Type u} {V : Type v} {B : Type w}
  [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup B] [Module K B]
variable {ι : Type} [Fintype ι]

/-- An injective evaluation preserves the original-K independence of
the section basis. This establishes absence of linear relations only. -/
theorem evaluatedBasis_linearIndependent (b : Module.Basis ι K V)
    (e : V →ₗ[K] B) (he : Function.Injective e) :
    LinearIndependent K (fun i => e (b i)) := by
  exact b.linearIndependent.map' e (LinearMap.ker_eq_bot.mpr he)

/-- The coordinate vector of a nonempty actual section basis is nonzero. -/
theorem evaluatedBasis_ne_zero [Nonempty ι] (b : Module.Basis ι K V)
    (e : V →ₗ[K] B) (he : Function.Injective e) :
    (fun i => e (b i)) ≠ 0 := by
  intro h
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  exact (evaluatedBasis_linearIndependent b e he).ne_zero i (congrFun h i)

/-- No nonzero original-K hyperplane equation vanishes at the generic
coordinate vector of an injectively evaluated basis. -/
theorem evaluatedBasis_relation_iff (b : Module.Basis ι K V)
    (e : V →ₗ[K] B) (he : Function.Injective e) (c : ι → K) :
    (∑ i, c i • e (b i) = 0) ↔ c = 0 := by
  constructor
  · intro h
    exact funext (Fintype.linearIndependent_iff.mp
      (evaluatedBasis_linearIndependent b e he) c h)
  · rintro rfl
    simp

end
end PfaffianDescent.Coray
end
