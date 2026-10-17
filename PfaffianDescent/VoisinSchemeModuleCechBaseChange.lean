import PfaffianDescent.SchemeModuleCoverEqualizer
import PfaffianDescent.SchemeModuleGlobalSectionsTop
import PfaffianDescent.VoisinGlobalSectionsBaseChange

/-!
# Cech assembly for module-section base change

This file combines the genuine sheaf equalizer presentation with flat
base change.  It reduces global-section base change to finite families of
local and pairwise-overlap section equivalences compatible with restriction.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

/-- Global sections commute with a field extension once this is known on a
finite cover and on its pairwise intersections, with compatibility for the
two Cech restriction maps. -/
noncomputable def schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCover
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (baseL : Y ⟶ Spec (.of L)) (M : X.Modules) (ML : Y.Modules)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (V : ι → X.Opens) (VL : ι → Y.Opens)
    (hcover : ⊤ ≤ ⨆ i, V i) (hcoverL : ⊤ ≤ ⨆ i, VL i)
    (localEquiv : ∀ i,
      (L ⊗[K] SchemeModuleOpenSectionsOver base M (V i)) ≃ₗ[L]
        SchemeModuleOpenSectionsOver baseL ML (VL i))
    (overlapEquiv : ∀ i j,
      (L ⊗[K] SchemeModuleOpenSectionsOver base M (V i ⊓ V j)) ≃ₗ[L]
        SchemeModuleOpenSectionsOver baseL ML (VL i ⊓ VL j))
    (hleft : ∀ x,
      schemeModuleCoverLeftRestrictionLinearMap baseL ML VL
          (tensorFinitePiLinearEquivOfFamily
            (fun i ↦ SchemeModuleOpenSectionsOver base M (V i))
            (fun i ↦ SchemeModuleOpenSectionsOver baseL ML (VL i))
            localEquiv x) =
        tensorFinitePiPiLinearEquivOfFamily
          (fun i j ↦ SchemeModuleOpenSectionsOver base M (V i ⊓ V j))
          (fun i j ↦ SchemeModuleOpenSectionsOver baseL ML (VL i ⊓ VL j))
          overlapEquiv
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleCoverLeftRestrictionLinearMap base M V) x))
    (hright : ∀ x,
      schemeModuleCoverRightRestrictionLinearMap baseL ML VL
          (tensorFinitePiLinearEquivOfFamily
            (fun i ↦ SchemeModuleOpenSectionsOver base M (V i))
            (fun i ↦ SchemeModuleOpenSectionsOver baseL ML (VL i))
            localEquiv x) =
        tensorFinitePiPiLinearEquivOfFamily
          (fun i j ↦ SchemeModuleOpenSectionsOver base M (V i ⊓ V j))
          (fun i j ↦ SchemeModuleOpenSectionsOver baseL ML (VL i ⊓ VL j))
          overlapEquiv
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleCoverRightRestrictionLinearMap base M V) x)) :
    (L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤) ≃ₗ[L]
      SchemeModuleOpenSectionsOver baseL ML ⊤ :=
  linearEquivBaseChangeOfCechPresentations
    (schemeModuleCoverLeftRestrictionLinearMap base M V)
    (schemeModuleCoverRightRestrictionLinearMap base M V)
    (schemeModuleCoverLeftRestrictionLinearMap baseL ML VL)
    (schemeModuleCoverRightRestrictionLinearMap baseL ML VL)
    (schemeModuleOpenSectionsLinearEquivCoverEqLocus
      M ⊤ V (fun _ ↦ le_top) hcover base)
    (tensorFinitePiLinearEquivOfFamily
      (fun i ↦ SchemeModuleOpenSectionsOver base M (V i))
      (fun i ↦ SchemeModuleOpenSectionsOver baseL ML (VL i))
      localEquiv)
    (tensorFinitePiPiLinearEquivOfFamily
      (fun i j ↦ SchemeModuleOpenSectionsOver base M (V i ⊓ V j))
      (fun i j ↦ SchemeModuleOpenSectionsOver baseL ML (VL i ⊓ VL j))
      overlapEquiv)
    hleft hright
    (schemeModuleOpenSectionsLinearEquivCoverEqLocus
      ML ⊤ VL (fun _ ↦ le_top) hcoverL baseL).symm

/-- Restricting the Čech-assembled base-change section to one member of the
cover recovers the prescribed local base-change equivalence. -/
theorem schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCover_restrict
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (baseL : Y ⟶ Spec (.of L)) (M : X.Modules) (ML : Y.Modules)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (V : ι → X.Opens) (VL : ι → Y.Opens)
    (hcover : ⊤ ≤ ⨆ i, V i) (hcoverL : ⊤ ≤ ⨆ i, VL i)
    (localEquiv : ∀ i,
      (L ⊗[K] SchemeModuleOpenSectionsOver base M (V i)) ≃ₗ[L]
        SchemeModuleOpenSectionsOver baseL ML (VL i))
    (overlapEquiv : ∀ i j,
      (L ⊗[K] SchemeModuleOpenSectionsOver base M (V i ⊓ V j)) ≃ₗ[L]
        SchemeModuleOpenSectionsOver baseL ML (VL i ⊓ VL j))
    (hleft : ∀ x,
      schemeModuleCoverLeftRestrictionLinearMap baseL ML VL
          (tensorFinitePiLinearEquivOfFamily
            (fun i ↦ SchemeModuleOpenSectionsOver base M (V i))
            (fun i ↦ SchemeModuleOpenSectionsOver baseL ML (VL i))
            localEquiv x) =
        tensorFinitePiPiLinearEquivOfFamily
          (fun i j ↦ SchemeModuleOpenSectionsOver base M (V i ⊓ V j))
          (fun i j ↦ SchemeModuleOpenSectionsOver baseL ML (VL i ⊓ VL j))
          overlapEquiv
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleCoverLeftRestrictionLinearMap base M V) x))
    (hright : ∀ x,
      schemeModuleCoverRightRestrictionLinearMap baseL ML VL
          (tensorFinitePiLinearEquivOfFamily
            (fun i ↦ SchemeModuleOpenSectionsOver base M (V i))
            (fun i ↦ SchemeModuleOpenSectionsOver baseL ML (VL i))
            localEquiv x) =
        tensorFinitePiPiLinearEquivOfFamily
          (fun i j ↦ SchemeModuleOpenSectionsOver base M (V i ⊓ V j))
          (fun i j ↦ SchemeModuleOpenSectionsOver baseL ML (VL i ⊓ VL j))
          overlapEquiv
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleCoverRightRestrictionLinearMap base M V) x))
    (i : ι) (x : L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤) :
    schemeModuleOpenSectionsRestrictionLinearMap baseL ML le_top
      (schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCover
        base baseL M ML V VL hcover hcoverL localEquiv overlapEquiv
          hleft hright x) =
    localEquiv i
      (TensorProduct.AlgebraTensorModule.lTensor L L
        (schemeModuleOpenSectionsRestrictionLinearMap base M le_top) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c s =>
      unfold schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCover
      unfold linearEquivBaseChangeOfCechPresentations
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
      change ((schemeModuleOpenSectionsLinearEquivCoverEqLocus
          ML ⊤ VL (fun _ ↦ le_top) hcoverL baseL)
        ((schemeModuleOpenSectionsLinearEquivCoverEqLocus
          ML ⊤ VL (fun _ ↦ le_top) hcoverL baseL).symm _)).1 i = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
      exact (map_add (localEquiv i) _ _).symm

/-- Componentwise form of the finite-cover theorem.  Compatibility need only
be checked on one chart restriction at a time; linearity and the finite
product tensor equivalences assemble those checks into the two Cech squares. -/
noncomputable def schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCoverOfComponents
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (baseL : Y ⟶ Spec (.of L)) (M : X.Modules) (ML : Y.Modules)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (V : ι → X.Opens) (VL : ι → Y.Opens)
    (hcover : ⊤ ≤ ⨆ i, V i) (hcoverL : ⊤ ≤ ⨆ i, VL i)
    (localEquiv : ∀ i,
      (L ⊗[K] SchemeModuleOpenSectionsOver base M (V i)) ≃ₗ[L]
        SchemeModuleOpenSectionsOver baseL ML (VL i))
    (overlapEquiv : ∀ i j,
      (L ⊗[K] SchemeModuleOpenSectionsOver base M (V i ⊓ V j)) ≃ₗ[L]
        SchemeModuleOpenSectionsOver baseL ML (VL i ⊓ VL j))
    (hleft : ∀ i j x,
      schemeModuleOpenSectionsRestrictionLinearMap baseL ML inf_le_left
          (localEquiv i x) =
        overlapEquiv i j
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleOpenSectionsRestrictionLinearMap base M inf_le_left) x))
    (hright : ∀ i j x,
      schemeModuleOpenSectionsRestrictionLinearMap baseL ML inf_le_right
          (localEquiv j x) =
        overlapEquiv i j
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleOpenSectionsRestrictionLinearMap base M inf_le_right) x)) :
    (L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤) ≃ₗ[L]
      SchemeModuleOpenSectionsOver baseL ML ⊤ :=
  schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCover
    base baseL M ML V VL hcover hcoverL localEquiv overlapEquiv
    (by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul c s =>
          ext i j
          simpa [tensorFinitePiLinearEquivOfFamily,
            tensorFinitePiPiLinearEquivOfFamily,
            schemeModuleCoverLeftRestrictionLinearMap] using
              hleft i j (c ⊗ₜ[K] s i)
      | add x y hx hy =>
          simpa only [map_add] using congrArg₂ (fun a b => a + b) hx hy)
    (by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul c s =>
          ext i j
          simpa [tensorFinitePiLinearEquivOfFamily,
            tensorFinitePiPiLinearEquivOfFamily,
            schemeModuleCoverRightRestrictionLinearMap] using
              hright i j (c ⊗ₜ[K] s j)
      | add x y hx hy =>
          simpa only [map_add] using congrArg₂ (fun a b => a + b) hx hy)

/-- Componentwise specialization of
`schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCover_restrict`. -/
theorem schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCoverOfComponents_restrict
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (baseL : Y ⟶ Spec (.of L)) (M : X.Modules) (ML : Y.Modules)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (V : ι → X.Opens) (VL : ι → Y.Opens)
    (hcover : ⊤ ≤ ⨆ i, V i) (hcoverL : ⊤ ≤ ⨆ i, VL i)
    (localEquiv : ∀ i,
      (L ⊗[K] SchemeModuleOpenSectionsOver base M (V i)) ≃ₗ[L]
        SchemeModuleOpenSectionsOver baseL ML (VL i))
    (overlapEquiv : ∀ i j,
      (L ⊗[K] SchemeModuleOpenSectionsOver base M (V i ⊓ V j)) ≃ₗ[L]
        SchemeModuleOpenSectionsOver baseL ML (VL i ⊓ VL j))
    (hleft : ∀ i j x,
      schemeModuleOpenSectionsRestrictionLinearMap baseL ML inf_le_left
          (localEquiv i x) =
        overlapEquiv i j
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleOpenSectionsRestrictionLinearMap base M inf_le_left) x))
    (hright : ∀ i j x,
      schemeModuleOpenSectionsRestrictionLinearMap baseL ML inf_le_right
          (localEquiv j x) =
        overlapEquiv i j
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleOpenSectionsRestrictionLinearMap base M inf_le_right) x))
    (i : ι) (x : L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤) :
    schemeModuleOpenSectionsRestrictionLinearMap baseL ML le_top
      (schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCoverOfComponents
        base baseL M ML V VL hcover hcoverL localEquiv overlapEquiv
          hleft hright x) =
    localEquiv i
      (TensorProduct.AlgebraTensorModule.lTensor L L
        (schemeModuleOpenSectionsRestrictionLinearMap base M le_top) x) := by
  unfold schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCoverOfComponents
  apply schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCover_restrict

/-- Morphism-valued global-section version of the componentwise finite-cover
base-change theorem.  This is the representation used by the fixed-linear-
system descent endpoint. -/
noncomputable def schemeModuleGlobalSectionsBaseChangeLinearEquivOfFiniteCoverOfComponents
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (baseL : Y ⟶ Spec (.of L)) (M : X.Modules) (ML : Y.Modules)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (V : ι → X.Opens) (VL : ι → Y.Opens)
    (hcover : ⊤ ≤ ⨆ i, V i) (hcoverL : ⊤ ≤ ⨆ i, VL i)
    (localEquiv : ∀ i,
      (L ⊗[K] SchemeModuleOpenSectionsOver base M (V i)) ≃ₗ[L]
        SchemeModuleOpenSectionsOver baseL ML (VL i))
    (overlapEquiv : ∀ i j,
      (L ⊗[K] SchemeModuleOpenSectionsOver base M (V i ⊓ V j)) ≃ₗ[L]
        SchemeModuleOpenSectionsOver baseL ML (VL i ⊓ VL j))
    (hleft : ∀ i j x,
      schemeModuleOpenSectionsRestrictionLinearMap baseL ML inf_le_left
          (localEquiv i x) =
        overlapEquiv i j
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleOpenSectionsRestrictionLinearMap base M inf_le_left) x))
    (hright : ∀ i j x,
      schemeModuleOpenSectionsRestrictionLinearMap baseL ML inf_le_right
          (localEquiv j x) =
        overlapEquiv i j
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleOpenSectionsRestrictionLinearMap base M inf_le_right) x)) :
    (L ⊗[K] SchemeModuleGlobalSectionsOver base M) ≃ₗ[L]
      SchemeModuleGlobalSectionsOver baseL ML :=
  (schemeModuleGlobalSectionsLinearEquivOpenTop base M).baseChange
      K L (SchemeModuleGlobalSectionsOver base M)
        (SchemeModuleOpenSectionsOver base M ⊤) ≪≫ₗ
    schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCoverOfComponents
      base baseL M ML V VL hcover hcoverL localEquiv overlapEquiv hleft hright ≪≫ₗ
        (schemeModuleGlobalSectionsLinearEquivOpenTop baseL ML).symm

end

end PfaffianDescent
