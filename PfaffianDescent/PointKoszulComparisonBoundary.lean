import PfaffianDescent.PointAdaptedCechKoszulComparison

/-!
# Explicit boundaries for changing point Koszul comparison lifts

Two first lifts of the same vertex map differ through the first Koszul
differential. Their degree-two coefficients therefore differ by an explicit
Cech boundary. Exactness and monicity come from the actual regular isolated
point parameters, rather than additional resolution hypotheses.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped nonZeroDivisors

namespace PfaffianDescent

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

set_option backward.isDefEq.respectTransparency false in
theorem pointKoszul_comparison_difference_boundary
    {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (hqreg : X.presheaf.germ U x hx q ∈ (X.presheaf.stalk x)⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U x hx q})
        (X.presheaf.germ U x hx f) ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hx q})⁰)
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (C : ChainComplex X.Modules ℕ)
    (a₀ : C.X 0 ⟶ sectionRepresenter X.ringCatSheaf U)
    (a₁ b₁ : C.X 1 ⟶ ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
    (a₂ b₂ : C.X 2 ⟶ sectionRepresenter X.ringCatSheaf U)
    (ha₁ : a₁ ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f = C.d 1 0 ≫ a₀)
    (hb₁ : b₁ ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f = C.d 1 0 ≫ a₀)
    (ha₂ : a₂ ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f = C.d 2 1 ≫ a₁)
    (hb₂ : b₂ ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f = C.d 2 1 ≫ b₁) :
    ∃ h : C.X 1 ⟶ sectionRepresenter X.ringCatSheaf U,
      h ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f = a₁ - b₁ ∧
      a₂ - b₂ = C.d 2 1 ≫ h ∧
      ∀ (Y : X.Modules) (y : Y.val.obj (op U)),
        a₂ ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y -
          b₂ ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y =
        C.d 2 1 ≫ (h ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y) := by
  let S := sectionRepresenterKoszulShortComplex X.ringCatSheaf U q f (Commute.all q f)
  have hex : S.Exact :=
    sectionRepresenterKoszul_exact_of_regularPairAtPoint X U q f x hx hqreg hfreg haway
  letI : Mono S.f :=
    sectionRepresenterKoszulFirst_mono_of_regularPairAtPoint X U q f x hx hqreg hfreg haway
  have hz : (a₁ - b₁) ≫ S.g = 0 := by
    change (a₁ - b₁) ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f = 0
    rw [Preadditive.sub_comp, ha₁, hb₁, sub_self]
  let h : C.X 1 ⟶ S.X₁ := hex.fIsKernel.lift (KernelFork.ofι (a₁ - b₁) hz)
  have hh : h ≫ S.f = a₁ - b₁ :=
    hex.fIsKernel.fac (KernelFork.ofι (a₁ - b₁) hz) WalkingParallelPair.zero
  have hsecond : a₂ - b₂ = C.d 2 1 ≫ h := by
    apply (cancel_mono S.f).1
    change (a₂ - b₂) ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
      (C.d 2 1 ≫ h) ≫ S.f
    rw [Preadditive.sub_comp, ha₂, hb₂, Category.assoc, hh, Preadditive.comp_sub]
  refine ⟨h, hh, hsecond, ?_⟩
  intro Y y
  rw [← Preadditive.sub_comp, hsecond, Category.assoc]

end PfaffianDescent
