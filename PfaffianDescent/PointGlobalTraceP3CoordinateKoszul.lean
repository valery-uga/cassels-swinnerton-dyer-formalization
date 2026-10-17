import PfaffianDescent.VoisinProjectiveCubicCohomology
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Actual coordinate-point Koszul differentials on projective three-space

The equations `X 1`, `X 2`, `X 3` cut out the standard coordinate point
`[1,0,0,0]`. We construct their Koszul differentials on actual twist sheaves,
with target the actual structure sheaf, and prove both consecutive
compositions zero. Exactness and identification of the point cokernel are
not asserted here.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Actual multiplication by a projective coordinate between consecutive twists. -/
def pointGlobalTraceP3CoordinateMul (i : Fin 4) (m : ℕ) :
    sheafOfModules PS (m + 1) ⟶ sheafOfModules PS m :=
  mulHomogeneous PS ⟨X i, isHomogeneous_X K i⟩ m

set_option backward.isDefEq.respectTransparency false in
/-- The actual coordinate multiplication morphisms commute across twists. -/
theorem pointGlobalTraceP3CoordinateMul_comm (i j : Fin 4) (m : ℕ) :
    pointGlobalTraceP3CoordinateMul K i (m + 1) ≫
        pointGlobalTraceP3CoordinateMul K j m =
      pointGlobalTraceP3CoordinateMul K j (m + 1) ≫
        pointGlobalTraceP3CoordinateMul K i m := by
  ext U z
  apply Subtype.ext
  funext x
  change algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) (X j) *
      (algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) (X i) * z.1 x) =
    algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) (X i) *
      (algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) (X j) * z.1 x)
  ring

/-- Three copies of an actual negative twist. -/
abbrev pointGlobalTraceP3CoordinateTriple (m : ℕ) : Fin 3 → (Proj PS).Modules :=
  fun _ => sheafOfModules PS m

/-- The actual leftmost coordinate Koszul differential `(X3,-X2,X1)`. -/
def pointGlobalTraceP3CoordinateKoszulFirst :
    sheafOfModules PS 3 ⟶ ⨁ pointGlobalTraceP3CoordinateTriple K 2 :=
  biproduct.lift ![pointGlobalTraceP3CoordinateMul K 3 2,
    -pointGlobalTraceP3CoordinateMul K 2 2, pointGlobalTraceP3CoordinateMul K 1 2]

/-- The actual coordinate Koszul matrix, with rows indexed by input summands. -/
def pointGlobalTraceP3CoordinateKoszulMiddle :
    (⨁ pointGlobalTraceP3CoordinateTriple K 2) ⟶
      ⨁ pointGlobalTraceP3CoordinateTriple K 1 :=
  biproduct.matrix
    ![![-pointGlobalTraceP3CoordinateMul K 2 1, pointGlobalTraceP3CoordinateMul K 1 1, 0],
      ![-pointGlobalTraceP3CoordinateMul K 3 1, 0, pointGlobalTraceP3CoordinateMul K 1 1],
      ![0, -pointGlobalTraceP3CoordinateMul K 3 1, pointGlobalTraceP3CoordinateMul K 2 1]]

/-- The actual last coordinate Koszul differential into the concrete zero twist. -/
def pointGlobalTraceP3CoordinateKoszulLastZeroTwist :
    (⨁ pointGlobalTraceP3CoordinateTriple K 1) ⟶ sheafOfModules PS 0 :=
  biproduct.desc ![pointGlobalTraceP3CoordinateMul K 1 0,
    pointGlobalTraceP3CoordinateMul K 2 0, pointGlobalTraceP3CoordinateMul K 3 0]

/-- The actual last differential into the structure sheaf. -/
def pointGlobalTraceP3CoordinateKoszulLast :
    (⨁ pointGlobalTraceP3CoordinateTriple K 1) ⟶
      SheafOfModules.unit (Proj PS).ringCatSheaf :=
  pointGlobalTraceP3CoordinateKoszulLastZeroTwist K ≫ (unitIsoZeroTwist PS).inv

/-- The first two actual sheaf differentials compose to zero. -/
theorem pointGlobalTraceP3CoordinateKoszul_first_middle_zero :
    pointGlobalTraceP3CoordinateKoszulFirst K ≫
      pointGlobalTraceP3CoordinateKoszulMiddle K = 0 := by
  rw [pointGlobalTraceP3CoordinateKoszulFirst,
    pointGlobalTraceP3CoordinateKoszulMiddle, biproduct.lift_matrix]
  apply biproduct.hom_ext
  intro j
  rw [biproduct.lift_π]
  fin_cases j <;>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Preadditive.comp_neg, Preadditive.neg_comp,
      zero_comp, comp_zero, add_zero, zero_add, neg_neg]
  all_goals try rw [pointGlobalTraceP3CoordinateMul_comm K 3 2 1]
  all_goals try rw [pointGlobalTraceP3CoordinateMul_comm K 3 1 1]
  all_goals try rw [pointGlobalTraceP3CoordinateMul_comm K 2 1 1]
  all_goals simp only [neg_add_cancel, add_neg_cancel]

/-- The last two actual sheaf differentials compose to zero into the zero twist. -/
theorem pointGlobalTraceP3CoordinateKoszul_middle_lastZeroTwist_zero :
    pointGlobalTraceP3CoordinateKoszulMiddle K ≫
      pointGlobalTraceP3CoordinateKoszulLastZeroTwist K = 0 := by
  rw [pointGlobalTraceP3CoordinateKoszulMiddle,
    pointGlobalTraceP3CoordinateKoszulLastZeroTwist, biproduct.matrix_desc]
  apply biproduct.hom_ext'
  intro j
  rw [biproduct.ι_desc]
  fin_cases j <;>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Preadditive.neg_comp,
      zero_comp, comp_zero, add_zero, zero_add]
  all_goals try rw [pointGlobalTraceP3CoordinateMul_comm K 2 1 0]
  all_goals try rw [pointGlobalTraceP3CoordinateMul_comm K 3 1 0]
  all_goals try rw [pointGlobalTraceP3CoordinateMul_comm K 3 2 0]
  all_goals simp only [neg_add_cancel]

set_option backward.isDefEq.respectTransparency false in
/-- The final consecutive composition is zero into the actual structure sheaf. -/
theorem pointGlobalTraceP3CoordinateKoszul_middle_last_zero :
    pointGlobalTraceP3CoordinateKoszulMiddle K ≫
      pointGlobalTraceP3CoordinateKoszulLast K = 0 := by
  rw [pointGlobalTraceP3CoordinateKoszulLast, ← Category.assoc,
    pointGlobalTraceP3CoordinateKoszul_middle_lastZeroTwist_zero, zero_comp]

end PfaffianDescent.ProjectiveNegativeTwist
