import PfaffianDescent.SectionRepresenterCechRefinement
import PfaffianDescent.SectionRepresenterScalar

/-! # Restriction of a computed Cech coefficient -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent
universe u
variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
/-- Restrict a known component, using the actual refinement and restriction maps. -/
theorem sectionRepresenterCechRefinement_computed_coefficient
    {ι κ : Type u} (U : ι → C) (W : κ → C)
    (σ : κ → ι) (j : ∀ k, W k ⟶ U (σ k))
    (M : SheafOfModules.{u} R) (n : ℕ)
    (h : (sectionRepresenterCechChain R U).X n ⟶ M)
    (f : Fin (n + 1) → κ)
    (v : M.val.obj (op (∏ᶜ fun a : Fin (n + 1) => U (σ (f a)))))
    (hv : Sigma.ι (fun g : Fin (n + 1) → ι =>
        sectionRepresenter R (∏ᶜ fun a : Fin (n + 1) => U (g a))) (σ ∘ f) ≫ h =
      sectionRepresenterAugmentation R _ M v) :
    sectionRepresenterCechHomEquivPi R W M n
      ((sectionRepresenterCechRefinement R U W σ j).f n ≫ h) f =
      M.val.map (CategoryTheory.Limits.Pi.map (fun a : Fin (n + 1) => j (f a))).op v := by
  have hc : sectionRepresenterCechHomEquivPi R U M n h (σ ∘ f) = v :=
    (congrArg (sectionRepresenterHomEquiv R
      (∏ᶜ fun a : Fin (n + 1) => U (σ (f a))) M) hv).trans
        (sectionRepresenterHomEquiv_augmentation R _ M v)
  exact (sectionRepresenterCechHomEquivPi_refinement R U W σ j M n h f).trans
    (congrArg (M.val.map (CategoryTheory.Limits.Pi.map
      (fun a : Fin (n + 1) => j (f a))).op) hc)
end PfaffianDescent
