import PfaffianDescent.SchemeModuleSignedPointTensorOperations
import PfaffianDescent.SchemeModulePointIncrementFiniteEuler
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Finite iteration of ACTUAL signed point tensor operations. True means
right tensor by the constructed dual of SAME M_P; false means left tensor
by SAME M_P. This is an actual module-valued list fold, not a divisor or
pole module. Original pi-induced scalars remain independent at every step.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open IdealSheafDataModule
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K]

/-- The FULL original residue degree with the sign of the actual operation. -/
def schemeModuleSignedClosedPointTensorWeight
    (pi : X ⟶ Spec (CommRingCat.of K)) (op : closedPoints X × Bool) : ℤ :=
  match op with
  | (P, true) => (pi.residueDegree P.1 : ℤ)
  | (P, false) => -(pi.residueDegree P.1 : ℤ)

/-- Sum of full signed residue degrees of the actual specified operations. -/
def schemeModuleSignedClosedPointTensorWeightSum
    (pi : X ⟶ Spec (CommRingCat.of K)) (ops : List (closedPoints X × Bool)) : ℤ :=
  (ops.map (schemeModuleSignedClosedPointTensorWeight pi)).sum

variable [HasExt.{u} X.Modules]

/-- The actual one-step sign dispatch proves new geometry/finiteness and
its weighted H0-H1 change from the corresponding actual canonical sequence.
The only finiteness inputs are H0/H1 of the actual initial L. -/
theorem schemeModuleSignedClosedPointTensor_finite_and_h0_h1_change
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (op : closedPoints X × Bool) (L : X.Modules)
    (hM : ∀ P : closedPoints X,
      let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i))
    (hL : schemeModuleLocallyRankOne L) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi L ⊤) →
    Module.Finite K (schemeModuleCohomology X L 1) →
    let T := schemeModuleSignedClosedPointTensor op L
    schemeModuleLocallyRankOne T ∧
      Module.Finite K (SchemeModuleOpenSectionsOver pi T ⊤) ∧
      Module.Finite K (schemeModuleCohomology X T 1) ∧
      (Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology X T 1) =
        (Module.finrank K (SchemeModuleOpenSectionsOver pi L ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology X L 1) +
          schemeModuleSignedClosedPointTensorWeight pi op := by
  dsimp only
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro h0 h1
  rcases op with ⟨P, sign⟩
  cases sign
  · simpa only [schemeModuleSignedClosedPointTensor, schemeModuleSignedClosedPointTensorWeight,
      sub_eq_add_neg] using
      schemeModuleClosedPoint_negativeIncrement_finite_and_h0_h1_change pi P L (hM P) hL h0 h1
  · simpa only [schemeModuleSignedClosedPointTensor, schemeModuleSignedClosedPointTensorWeight] using
      schemeModuleClosedPoint_positiveIncrement_finite_and_h0_h1_change pi P L (hM P) hL h0 h1

/-- Actual finite signed tensor induction. Each intermediate coefficient
is built by the original point tensors, so every next finite/rank-one input
is discharged by the previous actual sequence; no final finiteness or
Euler-change certificate is a premise. Repeated points and both signs are
allowed, and the empty list retains the original L. -/
theorem schemeModuleIteratedSignedClosedPointTensor_finite_and_h0_h1_change
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (ops : List (closedPoints X × Bool)) (L : X.Modules)
    (hM : ∀ P : closedPoints X,
      let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i))
    (hL : schemeModuleLocallyRankOne L) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi L ⊤) →
    Module.Finite K (schemeModuleCohomology X L 1) →
    let T := schemeModuleIteratedSignedClosedPointTensor L ops
    schemeModuleLocallyRankOne T ∧
      Module.Finite K (SchemeModuleOpenSectionsOver pi T ⊤) ∧
      Module.Finite K (schemeModuleCohomology X T 1) ∧
      (Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology X T 1) =
        (Module.finrank K (SchemeModuleOpenSectionsOver pi L ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology X L 1) +
          schemeModuleSignedClosedPointTensorWeightSum pi ops := by
  dsimp only
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro h0 h1
  induction ops generalizing L with
  | nil =>
    simpa only [schemeModuleIteratedSignedClosedPointTensor, List.foldl_nil,
      schemeModuleSignedClosedPointTensorWeightSum, List.map_nil, List.sum_nil, add_zero] using
      (show schemeModuleLocallyRankOne L ∧
        Module.Finite K (SchemeModuleOpenSectionsOver pi L ⊤) ∧
        Module.Finite K (schemeModuleCohomology X L 1) ∧
        (Module.finrank K (SchemeModuleOpenSectionsOver pi L ⊤) : ℤ) -
            Module.finrank K (schemeModuleCohomology X L 1) =
          (Module.finrank K (SchemeModuleOpenSectionsOver pi L ⊤) : ℤ) -
            Module.finrank K (schemeModuleCohomology X L 1) from ⟨hL, h0, h1, rfl⟩)
  | cons op ops ih =>
    obtain ⟨hL', h0', h1', hstep⟩ :=
      schemeModuleSignedClosedPointTensor_finite_and_h0_h1_change pi op L hM hL h0 h1
    have h := ih (schemeModuleSignedClosedPointTensor op L) hL' h0' h1'
    simp only [schemeModuleIteratedSignedClosedPointTensor, List.foldl_cons] at h ⊢
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    have htail := h.2.2.2
    simp only [schemeModuleSignedClosedPointTensorWeightSum, List.map_cons, List.sum_cons] at htail ⊢
    omega

end PfaffianDescent.Coray
