import PfaffianDescent.PointKoszulComparisonBoundary
import PfaffianDescent.SchemeCoverBoundaryInvariance

/-!
# Independence of point Koszul cohomology from the first lift

Actual point-parameter geometry gives an explicit boundary between two
comparison cocycles. The resulting intrinsic cohomology classes agree on
any covering family, including the common projective refinement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped nonZeroDivisors

namespace PfaffianDescent

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

set_option backward.isDefEq.respectTransparency false in
theorem pointKoszul_comparison_cohomology_independent
    {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (hqreg : X.presheaf.germ U x hx q ∈ (X.presheaf.stalk x)⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U x hx q})
        (X.presheaf.germ U x hx f) ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hx q})⁰)
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    {ι : Type u} (W : ι → X.Opens)
    (hW : (Opens.grothendieckTopology X).CoversTop W)
    [HasExt.{u} X.Modules] (Y : X.Modules) (y : Y.val.obj (op U))
    (a₀ : (sectionRepresenterCechChain X.ringCatSheaf W).X 0 ⟶
      sectionRepresenter X.ringCatSheaf U)
    (a₁ b₁ : (sectionRepresenterCechChain X.ringCatSheaf W).X 1 ⟶
      ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
    (a₂ b₂ : (sectionRepresenterCechChain X.ringCatSheaf W).X 2 ⟶
      sectionRepresenter X.ringCatSheaf U)
    (ha₁ : a₁ ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
      (sectionRepresenterCechChain X.ringCatSheaf W).d 1 0 ≫ a₀)
    (hb₁ : b₁ ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
      (sectionRepresenterCechChain X.ringCatSheaf W).d 1 0 ≫ a₀)
    (ha₂ : a₂ ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
      (sectionRepresenterCechChain X.ringCatSheaf W).d 2 1 ≫ a₁)
    (hb₂ : b₂ ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
      (sectionRepresenterCechChain X.ringCatSheaf W).d 2 1 ≫ b₁)
    (z z' : DegreeTwoCocycle ((sectionRepresenterCechChain X.ringCatSheaf W).d 3 2) (Y := Y))
    (hz : z.1 = a₂ ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y)
    (hz' : z'.1 = b₂ ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y) :
    schemeCoverDegreeTwoToCohomology W hW Y z =
      schemeCoverDegreeTwoToCohomology W hW Y z' := by
  obtain ⟨h, hh, hd, hc⟩ := pointKoszul_comparison_difference_boundary U x hx q f
    hqreg hfreg haway (sectionRepresenterCechChain X.ringCatSheaf W)
    a₀ a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂
  apply schemeCoverDegreeTwoToCohomology_eq_of_boundary_difference W hW Y z z'
    (h ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y)
  rw [hz, hz']
  exact (hc Y y).symm

end PfaffianDescent
