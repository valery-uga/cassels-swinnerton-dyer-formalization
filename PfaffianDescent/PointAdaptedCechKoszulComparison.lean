import PfaffianDescent.PointAdaptedCechKoszulFirstLift
import PfaffianDescent.SectionRepresenterKoszulStalk

/-!
# The adapted-cover Cech comparison through degree two

The first lift is constructed geometrically. Koszul exactness and monicity
then provide the second lift by the kernel universal property, and the
Cech chain identity proves the second lift is a cocycle.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped nonZeroDivisors

namespace PfaffianDescent.PointAdaptedAffineCover

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Construct the actual Cech-to-Koszul comparison maps and all its
positive-degree squares, from a regular isolated parameter pair. -/
theorem exists_chain_comparison
    {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (hqreg : X.presheaf.germ U x hx q ∈ (X.presheaf.stalk x)⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U x hx q})
        (X.presheaf.germ U x hx f) ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hx q})⁰)
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤) :
    ∃ (a₁ : (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).X 1 ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
      (a₂ : (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).X 2 ⟶
        sectionRepresenter X.ringCatSheaf U),
      a₁ ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
        (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 1 0 ≫ onC₀ U x ∧
      a₂ ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
        (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 2 1 ≫ a₁ ∧
      (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 3 2 ≫ a₂ = 0 := by
  let C := sectionRepresenterCechChain X.ringCatSheaf (opens U x)
  let S := sectionRepresenterKoszulShortComplex X.ringCatSheaf U q f (Commute.all q f)
  have hex : S.Exact :=
    sectionRepresenterKoszul_exact_of_regularPairAtPoint X U q f x hx hqreg hfreg haway
  letI : Mono S.f :=
    sectionRepresenterKoszulFirst_mono_of_regularPairAtPoint X U q f x hx hqreg hfreg haway
  obtain ⟨a₁, h₁⟩ := exists_onC₁ U hU x q f haway
  have hz : (C.d 2 1 ≫ a₁) ≫ S.g = 0 := by
    change (C.d 2 1 ≫ a₁) ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f = 0
    rw [Category.assoc, h₁, ← Category.assoc, C.d_comp_d, zero_comp]
  let a₂ : C.X 2 ⟶ S.X₁ := hex.fIsKernel.lift (KernelFork.ofι (C.d 2 1 ≫ a₁) hz)
  have h₂ : a₂ ≫ S.f = C.d 2 1 ≫ a₁ :=
    hex.fIsKernel.fac (KernelFork.ofι (C.d 2 1 ≫ a₁) hz) WalkingParallelPair.zero
  refine ⟨a₁, a₂, h₁, h₂, ?_⟩
  apply (cancel_mono S.f).1
  rw [Category.assoc, h₂, ← Category.assoc, C.d_comp_d, zero_comp, zero_comp]

end PfaffianDescent.PointAdaptedAffineCover
