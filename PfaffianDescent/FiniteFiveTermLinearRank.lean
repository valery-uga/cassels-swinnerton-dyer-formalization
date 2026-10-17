import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Exact.Basic
import PfaffianDescent.SchemeModuleOpenTopConnectingLinearExact

/-! Finite middle terms and the genuine five-term Euler balance, for
actual linear maps. Geometry callers derive exactness/injectivity/surjectivity
and finite outer terms internally. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K]

/-- Exactness alone with finite outer terms makes the middle finite;
surjectivity onto the entire last term is not incorrectly presumed. -/
theorem moduleFinite_middle_of_exact
    {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (f : A →ₗ[K] B) (g : B →ₗ[K] C) (h : Function.Exact f g)
    [Module.Finite K A] [Module.Finite K C] : Module.Finite K B := by
  have h' : Function.Exact f g.rangeRestrict := by
    intro z
    constructor
    · intro hz
      apply (h z).mp
      exact congrArg Subtype.val hz
    · intro hz
      apply Subtype.ext
      exact (h z).mpr hz
  exact Module.Finite.of_exact h' g.surjective_rangeRestrict

/-- The exact five-term dimension balance keeps every actual image.
Finite B and E are derived, rather than supplied as certificates. -/
theorem finiteFiveTermLinearRank
    {A B C D E : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
    [Module K A] [Module K B] [Module K C] [Module K D] [Module K E]
    [Module.Finite K A] [Module.Finite K C] [Module.Finite K D]
    (f : A →ₗ[K] B) (g : B →ₗ[K] C) (h : C →ₗ[K] D) (j : D →ₗ[K] E)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hgh : Function.Exact g h) (hhj : Function.Exact h j) (hj : Function.Surjective j) :
    Module.Finite K B ∧ Module.Finite K E ∧
      Module.finrank K B + Module.finrank K D =
        Module.finrank K A + Module.finrank K C + Module.finrank K E := by
  letI : Module.Finite K B := moduleFinite_middle_of_exact f g hfg
  letI : Module.Finite K E := Module.Finite.of_surjective j hj
  have hdimG := g.finrank_range_add_finrank_ker
  rw [hfg.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf] at hdimG
  have hdimH := h.finrank_range_add_finrank_ker
  rw [hgh.linearMap_ker_eq] at hdimH
  have hdimJ := j.finrank_range_add_finrank_ker
  rw [hhj.linearMap_ker_eq, LinearMap.range_eq_top.mpr hj, finrank_top] at hdimJ
  exact ⟨inferInstance, inferInstance, by omega⟩

/-- The actual top-section coefficient map is injective when its actual
sheaf morphism is Mono. No section-injectivity premise is used. -/
theorem schemeModuleOpenTopCoefficientLinearMapOver_injective_of_mono
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    Function.Injective (schemeModuleOpenTopCoefficientLinearMapOver pi f) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let eM := schemeModuleUnitHomGroundLinearEquivOpenTop pi M
  let eN := schemeModuleUnitHomGroundLinearEquivOpenTop pi N
  intro s t hst
  have hhom : eM.symm s ≫ f = eM.symm t ≫ f := by
    apply eN.injective
    rw [schemeModuleUnitHomGroundLinearEquivOpenTop_naturality,
      schemeModuleUnitHomGroundLinearEquivOpenTop_naturality,
      eM.apply_symm_apply, eM.apply_symm_apply]
    exact hst
  exact eM.symm.injective ((cancel_mono f).mp hhom)

end PfaffianDescent.Coray
