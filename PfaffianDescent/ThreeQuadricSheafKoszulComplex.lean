import PfaffianDescent.PointGlobalTraceP3CoordinateKoszul
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! SOURCE ONLY / UNVERIFIED. Actual arbitrary-quadric Koszul maps on P3.
This leaf proves the complex identities and left injectivity. It does NOT
assert exactness of its middle/last terms or identify its cokernel with an
original ideal sheaf. No regularity/exactness certificate is assumed. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Actual multiplication by a quadric between negative twists. -/
def threeQuadricSheafMul (q : PS 2) (m : ℕ) :
    sheafOfModules PS (m + 2) ⟶ sheafOfModules PS m :=
  mulHomogeneous PS q m

/-- The actual quadric multiplication morphisms commute across twists. -/
theorem threeQuadricSheafMul_comm (q r : PS 2) (m : ℕ) :
    threeQuadricSheafMul K q (m + 2) ≫ threeQuadricSheafMul K r m =
      threeQuadricSheafMul K r (m + 2) ≫ threeQuadricSheafMul K q m := by
  ext U z
  apply Subtype.ext
  funext x
  change algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) r.val *
      (algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) q.val * z.1 x) =
    algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) q.val *
      (algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) r.val * z.1 x)
  ring

/-- Three copies of an actual negative twist. -/
abbrev threeQuadricSheafTriple (m : ℕ) : Fin 3 → (Proj PS).Modules :=
  fun _ => sheafOfModules PS m

/-- The actual leftmost quadric Koszul differential `(h,-g,f)`. -/
def threeQuadricSheafKoszulFirst (f g h : PS 2) :
    sheafOfModules PS 6 ⟶ ⨁ threeQuadricSheafTriple K 4 :=
  biproduct.lift ![threeQuadricSheafMul K h 4,
    -threeQuadricSheafMul K g 4, threeQuadricSheafMul K f 4]

/-- The actual quadric Koszul matrix, with rows indexed by input summands. -/
def threeQuadricSheafKoszulMiddle (f g h : PS 2) :
    (⨁ threeQuadricSheafTriple K 4) ⟶
      ⨁ threeQuadricSheafTriple K 2 :=
  biproduct.matrix
    ![![-threeQuadricSheafMul K g 2, threeQuadricSheafMul K f 2, 0],
      ![-threeQuadricSheafMul K h 2, 0, threeQuadricSheafMul K f 2],
      ![0, -threeQuadricSheafMul K h 2, threeQuadricSheafMul K g 2]]

/-- The actual last quadric Koszul differential into the concrete zero twist. -/
def threeQuadricSheafKoszulLastZeroTwist (f g h : PS 2) :
    (⨁ threeQuadricSheafTriple K 2) ⟶ sheafOfModules PS 0 :=
  biproduct.desc ![threeQuadricSheafMul K f 0,
    threeQuadricSheafMul K g 0, threeQuadricSheafMul K h 0]

/-- The actual last differential into the structure sheaf. -/
def threeQuadricSheafKoszulLast (f g h : PS 2) :
    (⨁ threeQuadricSheafTriple K 2) ⟶
      SheafOfModules.unit (Proj PS).ringCatSheaf :=
  threeQuadricSheafKoszulLastZeroTwist K f g h ≫ (unitIsoZeroTwist PS).inv

/-- The first two actual sheaf differentials compose to zero. -/
theorem threeQuadricSheafKoszul_first_middle_zero (f g h : PS 2) :
    threeQuadricSheafKoszulFirst K f g h ≫
      threeQuadricSheafKoszulMiddle K f g h = 0 := by
  rw [threeQuadricSheafKoszulFirst,
    threeQuadricSheafKoszulMiddle, biproduct.lift_matrix]
  apply biproduct.hom_ext
  intro j
  rw [biproduct.lift_π]
  fin_cases j <;>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Preadditive.comp_neg, Preadditive.neg_comp,
      zero_comp, comp_zero, add_zero, zero_add, neg_neg]
  all_goals try rw [threeQuadricSheafMul_comm K h g 2]
  all_goals try rw [threeQuadricSheafMul_comm K h f 2]
  all_goals try rw [threeQuadricSheafMul_comm K g f 2]
  all_goals simp only [neg_add_cancel, add_neg_cancel]

/-- The last two actual sheaf differentials compose to zero into the zero twist. -/
theorem threeQuadricSheafKoszul_middle_lastZeroTwist_zero (f g h : PS 2) :
    threeQuadricSheafKoszulMiddle K f g h ≫
      threeQuadricSheafKoszulLastZeroTwist K f g h = 0 := by
  rw [threeQuadricSheafKoszulMiddle,
    threeQuadricSheafKoszulLastZeroTwist, biproduct.matrix_desc]
  apply biproduct.hom_ext'
  intro j
  rw [biproduct.ι_desc]
  fin_cases j <;>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Preadditive.neg_comp,
      zero_comp, comp_zero, add_zero, zero_add]
  all_goals try rw [threeQuadricSheafMul_comm K g f 0]
  all_goals try rw [threeQuadricSheafMul_comm K h f 0]
  all_goals try rw [threeQuadricSheafMul_comm K h g 0]
  all_goals simp only [neg_add_cancel]

set_option backward.isDefEq.respectTransparency false in
/-- The final consecutive composition is zero into the actual structure sheaf. -/
theorem threeQuadricSheafKoszul_middle_last_zero (f g h : PS 2) :
    threeQuadricSheafKoszulMiddle K f g h ≫
      threeQuadricSheafKoszulLast K f g h = 0 := by
  rw [threeQuadricSheafKoszulLast, ← Category.assoc,
    threeQuadricSheafKoszul_middle_lastZeroTwist_zero, zero_comp]

/-- The first map of the literal negative-twist quadric complex is mono,
using actual multiplication by the nonzero first quadric. -/
theorem threeQuadricSheafKoszulFirst_mono (f g h : PS 2) (hf : f.val ≠ 0) :
    Mono (threeQuadricSheafKoszulFirst K f g h) := by
  letI : Mono (threeQuadricSheafMul K f 4) := mulHomogeneous_mono PS f hf 4
  have hfac : threeQuadricSheafKoszulFirst K f g h ≫
      biproduct.π (threeQuadricSheafTriple K 4) 2 = threeQuadricSheafMul K f 4 := by
    simp [threeQuadricSheafKoszulFirst]
  exact mono_of_mono_fac hfac

end PfaffianDescent.ProjectiveNegativeTwist
