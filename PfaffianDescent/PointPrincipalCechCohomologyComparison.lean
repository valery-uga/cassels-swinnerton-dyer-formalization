import PfaffianDescent.PointPrincipalCechVertexRefinement
import PfaffianDescent.PointKoszulCohomologyIndependence

/-! # Intrinsic cohomology comparison with the original point cover -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped nonZeroDivisors
namespace PfaffianDescent.PointAdaptedAffineCover
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Actual principal and adapted comparisons represent the same intrinsic
class. The refinement squares are proved by chain-map commutation. -/
theorem principal_comparison_intrinsic_class_eq_adapted
    {X : Scheme.{u}} [hExt : HasExt.{u} X.Modules]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (hclosed : IsClosed ({x} : Set X)) (q f : Γ(X, U))
    (hq : X.presheaf.germ U x hx q ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hf : X.presheaf.germ U x hx f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hqreg : X.presheaf.germ U x hx q ∈ (X.presheaf.stalk x)⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U x hx q})
        (X.presheaf.germ U x hx f) ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hx q})⁰)
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (Y : X.Modules) (y : Y.val.obj (op U))
    (b₁ : (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).X 1 ⟶
      ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
    (b₂ : (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).X 2 ⟶
      sectionRepresenter X.ringCatSheaf U)
    (hb₁ : b₁ ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
      (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 1 0 ≫ onC₀ U x)
    (hb₂ : b₂ ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
      (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 2 1 ≫ b₁)
    (L : ∀ i j : PrincipalIndex X x,
      sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
    (a₂ : (sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)).X 2 ⟶
      sectionRepresenter X.ringCatSheaf U)
    (ha₁ : principalAssembleFirstLift U x q f L ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
      (sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)).d 1 0 ≫
        principalOnC₀ U x q f)
    (ha₂ : a₂ ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
      (sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)).d 2 1 ≫
        principalAssembleFirstLift U x q f L)
    (zold : DegreeTwoCocycle ((sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 3 2) (Y := Y))
    (znew : DegreeTwoCocycle ((sectionRepresenterCechChain X.ringCatSheaf
      (principalOpens U x q f)).d 3 2) (Y := Y))
    (hzold : zold.1 = b₂ ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y)
    (hznew : znew.1 = a₂ ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y) :
    schemeCoverDegreeTwoToCohomology (opens U x) (coversTop U x hx hclosed) Y zold =
      schemeCoverDegreeTwoToCohomology (principalOpens U x q f)
        (principalOpens_coversTop U x hx hclosed q f) Y znew := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let r := principalToAdaptedChain U hU x hx q f hq hf
  let C := sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)
  let D := sectionRepresenterCechChain X.ringCatSheaf (opens U x)
  let zr := DegreeTwoCocycle.precompAddHom _ _ (r.f 2) (r.f 3) (r.comm 3 2).symm zold
  have hzero : r.f 0 ≫ onC₀ U x = principalOnC₀ U x q f :=
    principalOnC₀_refinement U hU x hx q f hq hf
  have hr₁ : (r.f 1 ≫ b₁) ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
      C.d 1 0 ≫ principalOnC₀ U x q f := by
    rw [Category.assoc, hb₁, ← Category.assoc, r.comm 1 0, Category.assoc, hzero]
  have hr₂ : (r.f 2 ≫ b₂) ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
      C.d 2 1 ≫ (r.f 1 ≫ b₁) := by
    rw [Category.assoc, hb₂, ← Category.assoc, r.comm 2 1, Category.assoc]
  have hzr : zr.1 = (r.f 2 ≫ b₂) ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y := by
    change r.f 2 ≫ zold.1 = _
    rw [hzold, ← Category.assoc]
  have hind := pointKoszul_comparison_cohomology_independent U x hx q f hqreg hfreg haway
    (principalOpens U x q f) (principalOpens_coversTop U x hx hclosed q f) Y y
      (principalOnC₀ U x q f) (principalAssembleFirstLift U x q f L) (r.f 1 ≫ b₁)
        a₂ (r.f 2 ≫ b₂) ha₁ hr₁ ha₂ hr₂ znew zr hznew hzr
  have href := schemeCoverDegreeTwoToCohomology_refinement (opens U x) (principalOpens U x q f)
    (coversTop U x hx hclosed) (principalOpens_coversTop U x hx hclosed q f)
      (principalToAdaptedIndex U hU x hx q f hq hf)
      (fun i => homOfLE (le_of_eq (principalToAdaptedIndex_opens U hU x hx q f hq hf i).symm)) Y zold
  exact href.trans hind.symm
end PfaffianDescent.PointAdaptedAffineCover
