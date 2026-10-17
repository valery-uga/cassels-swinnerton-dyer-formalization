import PfaffianDescent.PointGlobalTraceP3CoordinateKoszul

/-! # Actual Koszul sheaf maps for three arbitrary degree-one equations

The four degree-one forms provide three equations (indices 1,2,3) and
a chart coordinate (index 0). The terms are the original native projective
twists; every matrix entry is actual homogeneous multiplication. No basis
or regularity premise is needed for the consecutive compositions to vanish.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
variable (f : Fin 4 → homogeneousSubmodule (Fin 4) K 1)

/-- Actual multiplication by a projective coordinate between consecutive twists. -/
def pointGlobalTraceP3BasisMul (i : Fin 4) (m : ℕ) :
    sheafOfModules PS (m + 1) ⟶ sheafOfModules PS m :=
  mulHomogeneous PS (f i) m

set_option backward.isDefEq.respectTransparency false in
/-- The actual degree-one multiplication morphisms commute across twists. -/
theorem pointGlobalTraceP3BasisMul_comm (i j : Fin 4) (m : ℕ) :
    pointGlobalTraceP3BasisMul K f i (m + 1) ≫
        pointGlobalTraceP3BasisMul K f j m =
      pointGlobalTraceP3BasisMul K f j (m + 1) ≫
        pointGlobalTraceP3BasisMul K f i m := by
  ext U z
  apply Subtype.ext
  funext x
  change algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) ((f j).val) *
      (algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) ((f i).val) * z.1 x) =
    algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) ((f i).val) *
      (algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) ((f j).val) * z.1 x)
  ring

/-- The actual leftmost degree-one Koszul differential `(f3,-f2,f1)`. -/
def pointGlobalTraceP3BasisKoszulFirst :
    sheafOfModules PS 3 ⟶ ⨁ pointGlobalTraceP3CoordinateTriple K 2 :=
  biproduct.lift ![pointGlobalTraceP3BasisMul K f 3 2,
    -pointGlobalTraceP3BasisMul K f 2 2, pointGlobalTraceP3BasisMul K f 1 2]

/-- The actual degree-one Koszul matrix, with rows indexed by input summands. -/
def pointGlobalTraceP3BasisKoszulMiddle :
    (⨁ pointGlobalTraceP3CoordinateTriple K 2) ⟶
      ⨁ pointGlobalTraceP3CoordinateTriple K 1 :=
  biproduct.matrix
    ![![-pointGlobalTraceP3BasisMul K f 2 1, pointGlobalTraceP3BasisMul K f 1 1, 0],
      ![-pointGlobalTraceP3BasisMul K f 3 1, 0, pointGlobalTraceP3BasisMul K f 1 1],
      ![0, -pointGlobalTraceP3BasisMul K f 3 1, pointGlobalTraceP3BasisMul K f 2 1]]

/-- The actual last degree-one Koszul differential into the concrete zero twist. -/
def pointGlobalTraceP3BasisKoszulLastZeroTwist :
    (⨁ pointGlobalTraceP3CoordinateTriple K 1) ⟶ sheafOfModules PS 0 :=
  biproduct.desc ![pointGlobalTraceP3BasisMul K f 1 0,
    pointGlobalTraceP3BasisMul K f 2 0, pointGlobalTraceP3BasisMul K f 3 0]

/-- The actual last differential into the structure sheaf. -/
def pointGlobalTraceP3BasisKoszulLast :
    (⨁ pointGlobalTraceP3CoordinateTriple K 1) ⟶
      SheafOfModules.unit (Proj PS).ringCatSheaf :=
  pointGlobalTraceP3BasisKoszulLastZeroTwist K f ≫ (unitIsoZeroTwist PS).inv

/-- The first two actual sheaf differentials compose to zero. -/
theorem pointGlobalTraceP3BasisKoszul_first_middle_zero :
    pointGlobalTraceP3BasisKoszulFirst K f ≫
      pointGlobalTraceP3BasisKoszulMiddle K f = 0 := by
  rw [pointGlobalTraceP3BasisKoszulFirst,
    pointGlobalTraceP3BasisKoszulMiddle, biproduct.lift_matrix]
  apply biproduct.hom_ext
  intro j
  rw [biproduct.lift_π]
  fin_cases j <;>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Preadditive.comp_neg, Preadditive.neg_comp,
      zero_comp, comp_zero, add_zero, zero_add, neg_neg]
  all_goals try rw [pointGlobalTraceP3BasisMul_comm K f 3 2 1]
  all_goals try rw [pointGlobalTraceP3BasisMul_comm K f 3 1 1]
  all_goals try rw [pointGlobalTraceP3BasisMul_comm K f 2 1 1]
  all_goals simp only [neg_add_cancel, add_neg_cancel]

/-- The last two actual sheaf differentials compose to zero into the zero twist. -/
theorem pointGlobalTraceP3BasisKoszul_middle_lastZeroTwist_zero :
    pointGlobalTraceP3BasisKoszulMiddle K f ≫
      pointGlobalTraceP3BasisKoszulLastZeroTwist K f = 0 := by
  rw [pointGlobalTraceP3BasisKoszulMiddle,
    pointGlobalTraceP3BasisKoszulLastZeroTwist, biproduct.matrix_desc]
  apply biproduct.hom_ext'
  intro j
  rw [biproduct.ι_desc]
  fin_cases j <;>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Preadditive.neg_comp,
      zero_comp, comp_zero, add_zero, zero_add]
  all_goals try rw [pointGlobalTraceP3BasisMul_comm K f 2 1 0]
  all_goals try rw [pointGlobalTraceP3BasisMul_comm K f 3 1 0]
  all_goals try rw [pointGlobalTraceP3BasisMul_comm K f 3 2 0]
  all_goals simp only [neg_add_cancel]

set_option backward.isDefEq.respectTransparency false in
/-- The final consecutive composition is zero into the actual structure sheaf. -/
theorem pointGlobalTraceP3BasisKoszul_middle_last_zero :
    pointGlobalTraceP3BasisKoszulMiddle K f ≫
      pointGlobalTraceP3BasisKoszulLast K f = 0 := by
  rw [pointGlobalTraceP3BasisKoszulLast, ← Category.assoc,
    pointGlobalTraceP3BasisKoszul_middle_lastZeroTwist_zero, zero_comp]

end PfaffianDescent.ProjectiveNegativeTwist
