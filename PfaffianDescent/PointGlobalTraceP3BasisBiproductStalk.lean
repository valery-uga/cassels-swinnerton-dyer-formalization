import PfaffianDescent.PointGlobalTraceP3BasisStalkCoordinates

/-! # Actual finite-sum stalk matrices for arbitrary degree-one Koszul equations

The finite-sum terms are the original native projective twists. In the
chosen degree-one stalk trivialization, each original sheaf differential
is precisely its three-generator Koszul matrix.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
variable (f : Fin 4 → homogeneousSubmodule (Fin 4) K 1)

local instance pointGlobalTraceP3Basis_biproductPointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

/-- A normalized coefficient of the actual basis Koszul stalk matrix. -/
def pointGlobalTraceP3Basis_stalkParameter
    (i j : Fin 4) (x : Proj PS) (hx : (f j).val ∈ (pointIdeal PS x).primeCompl) :
    AtPrime PS (pointIdeal PS x) :=
  localEquation PS (pointIdeal PS x) (f i) (f j) hx

private def finThreeAddEquiv (A : Type u) [AddCommGroup A] :
    (Fin 3 → A) ≃+ (A × A × A) where
  toFun z := (z 0, z 1, z 2)
  invFun z := ![z.1, z.2.1, z.2.2]
  left_inv z := by funext i; fin_cases i <;> rfl
  right_inv z := rfl
  map_add' z w := rfl

/-- The actual stalk of the rank-three twist term, as its three summand stalks. -/
def pointGlobalTraceP3Basis_stalkPiIso (x : Proj PS) (m : ℕ) :
    (schemeModuleStalkFunctor (Proj PS) x).obj
        (⨁ pointGlobalTraceP3CoordinateTriple K m) ≅
      AddCommGrpCat.of (Fin 3 →
        (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS m)) := by
  let F := schemeModuleStalkFunctor (Proj PS) x
  let P := pointGlobalTraceP3CoordinateTriple K m
  exact F.mapBiproduct P ≪≫ AddCommGrpCat.biproductIsoPi (F.obj ∘ P)

set_option backward.isDefEq.respectTransparency false in
private theorem piIso_hom_comp_eval (x : Proj PS) (m : ℕ) (i : Fin 3) :
    (pointGlobalTraceP3Basis_stalkPiIso K x m).hom ≫
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun _ : Fin 3 =>
        (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS m)) i) =
    (schemeModuleStalkFunctor (Proj PS) x).map
      (biproduct.π (pointGlobalTraceP3CoordinateTriple K m) i) := by
  let F := schemeModuleStalkFunctor (Proj PS) x
  let P := pointGlobalTraceP3CoordinateTriple K m
  let Q := F.obj ∘ P
  have h : (AddCommGrpCat.biproductIsoPi Q).hom ≫
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun i => Q i) i) = biproduct.π Q i := by
    rw [← cancel_epi (AddCommGrpCat.biproductIsoPi Q).inv]
    simp
  simp only [pointGlobalTraceP3Basis_stalkPiIso, Iso.trans_hom, Category.assoc]
  change (F.mapBiproduct P).hom ≫ (AddCommGrpCat.biproductIsoPi Q).hom ≫
    AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun i => Q i) i) = F.map (biproduct.π P i)
  rw [h]
  change (biproduct.lift fun i => F.map (biproduct.π P i)) ≫ biproduct.π Q i = _
  exact biproduct.lift_π _ i

/-- Coordinates of the actual finite-sum stalk, in the homogeneous local ring. -/
def pointGlobalTraceP3Basis_stalkTripleCoordinate
    (j : Fin 4) (x : Proj PS) (hx : (f j).val ∈ (pointIdeal PS x).primeCompl) (m : ℕ) :
    (↑((schemeModuleStalkFunctor (Proj PS) x).obj
        (⨁ pointGlobalTraceP3CoordinateTriple K m)) : Type u) ≃+
      (AtPrime PS (pointIdeal PS x) × AtPrime PS (pointIdeal PS x) ×
        AtPrime PS (pointIdeal PS x)) :=
  (pointGlobalTraceP3Basis_stalkPiIso K x m).addCommGroupIsoToAddEquiv.trans
    ((AddEquiv.piCongrRight fun _ : Fin 3 => pointGlobalTraceP3Basis_stalkCoordinate K f j x hx m).trans
      (finThreeAddEquiv _))

set_option backward.isDefEq.respectTransparency false in
theorem pointGlobalTraceP3Basis_stalkTripleCoordinate_apply
    (j : Fin 4) (x : Proj PS) (hx : (f j).val ∈ (pointIdeal PS x).primeCompl) (m : ℕ)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj
      (⨁ pointGlobalTraceP3CoordinateTriple K m)) :
    pointGlobalTraceP3Basis_stalkTripleCoordinate K f j x hx m z =
      (pointGlobalTraceP3Basis_stalkCoordinate K f j x hx m
        ((schemeModuleStalkFunctor (Proj PS) x).map
          (biproduct.π (pointGlobalTraceP3CoordinateTriple K m) 0) z),
       pointGlobalTraceP3Basis_stalkCoordinate K f j x hx m
        ((schemeModuleStalkFunctor (Proj PS) x).map
          (biproduct.π (pointGlobalTraceP3CoordinateTriple K m) 1) z),
       pointGlobalTraceP3Basis_stalkCoordinate K f j x hx m
        ((schemeModuleStalkFunctor (Proj PS) x).map
          (biproduct.π (pointGlobalTraceP3CoordinateTriple K m) 2) z)) := by
  have h (i : Fin 3) := ConcreteCategory.congr_hom (piIso_hom_comp_eval K x m i) z
  change (pointGlobalTraceP3Basis_stalkCoordinate K f j x hx m
        ((pointGlobalTraceP3Basis_stalkPiIso K x m).hom z 0),
      pointGlobalTraceP3Basis_stalkCoordinate K f j x hx m
        ((pointGlobalTraceP3Basis_stalkPiIso K x m).hom z 1),
      pointGlobalTraceP3Basis_stalkCoordinate K f j x hx m
        ((pointGlobalTraceP3Basis_stalkPiIso K x m).hom z 2)) = _
  rw [show (pointGlobalTraceP3Basis_stalkPiIso K x m).hom z 0 = _ from h 0,
    show (pointGlobalTraceP3Basis_stalkPiIso K x m).hom z 1 = _ from h 1,
    show (pointGlobalTraceP3Basis_stalkPiIso K x m).hom z 2 = _ from h 2]

set_option backward.isDefEq.respectTransparency false in
/-- The actual first differential becomes the explicit first Koszul matrix. -/
theorem pointGlobalTraceP3Basis_first_stalk_coordinates
    (j : Fin 4) (x : Proj PS) (hx : (f j).val ∈ (pointIdeal PS x).primeCompl)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 3)) :
    pointGlobalTraceP3Basis_stalkTripleCoordinate K f j x hx 2
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisKoszulFirst K f) z) =
    threeGeneratorFirst
      (pointGlobalTraceP3Basis_stalkParameter K f 1 j x hx)
      (pointGlobalTraceP3Basis_stalkParameter K f 2 j x hx)
      (pointGlobalTraceP3Basis_stalkParameter K f 3 j x hx)
      (pointGlobalTraceP3Basis_stalkCoordinate K f j x hx 3 z) := by
  rw [pointGlobalTraceP3Basis_stalkTripleCoordinate_apply]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    pointGlobalTraceP3BasisKoszulFirst, biproduct.lift_π,
    Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Functor.map_neg]
  simp [threeGeneratorFirst,
    pointGlobalTraceP3Basis_stalkParameter, neg_mul]
  refine ⟨pointGlobalTraceP3Basis_stalkCoordinate_mul K f 3 j x hx 2 z, ?_,
    pointGlobalTraceP3Basis_stalkCoordinate_mul K f 1 j x hx 2 z⟩
  change -(pointGlobalTraceP3Basis_stalkCoordinate K f j x hx 2
    ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisMul K f 2 2) z)) = _
  rw [pointGlobalTraceP3Basis_stalkCoordinate_mul]
  exact (neg_mul (pointGlobalTraceP3Basis_stalkParameter K f 2 j x hx)
    (pointGlobalTraceP3Basis_stalkCoordinate K f j x hx 3 z)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual middle differential becomes the explicit middle Koszul matrix. -/
theorem pointGlobalTraceP3Basis_middle_stalk_coordinates
    (j : Fin 4) (x : Proj PS) (hx : (f j).val ∈ (pointIdeal PS x).primeCompl)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj
      (⨁ pointGlobalTraceP3CoordinateTriple K 2)) :
    pointGlobalTraceP3Basis_stalkTripleCoordinate K f j x hx 1
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisKoszulMiddle K f) z) =
    threeGeneratorMiddle
      (pointGlobalTraceP3Basis_stalkParameter K f 1 j x hx)
      (pointGlobalTraceP3Basis_stalkParameter K f 2 j x hx)
      (pointGlobalTraceP3Basis_stalkParameter K f 3 j x hx)
      (pointGlobalTraceP3Basis_stalkTripleCoordinate K f j x hx 2 z) := by
  rw [pointGlobalTraceP3Basis_stalkTripleCoordinate_apply, pointGlobalTraceP3Basis_stalkTripleCoordinate_apply]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    pointGlobalTraceP3BasisKoszulMiddle, biproduct.matrix_π]
  simp only [biproduct.desc_eq, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    comp_zero, add_zero, zero_add, Functor.map_add, Functor.map_neg, Functor.map_comp]
  have hmul (i : Fin 4) (w : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 2)) :
      pointGlobalTraceP3Basis_stalkCoordinate K f j x hx 1
        (((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisMul K f i 1)).hom w) =
      pointGlobalTraceP3Basis_stalkParameter K f i j x hx * pointGlobalTraceP3Basis_stalkCoordinate K f j x hx 2 w :=
    pointGlobalTraceP3Basis_stalkCoordinate_mul K f i j x hx 1 w
  simp [AddCommGrpCat.hom_add_apply, hmul,
    threeGeneratorMiddle, pointGlobalTraceP3Basis_stalkParameter, sub_eq_add_neg, neg_mul]
  let v (i : Fin 3) : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 2) :=
    (schemeModuleStalkFunctor (Proj PS) x).map
      (biproduct.π (pointGlobalTraceP3CoordinateTriple K 2) i) z
  let a := pointGlobalTraceP3Basis_stalkCoordinate K f j x hx 2
  let p := pointGlobalTraceP3Basis_stalkParameter K f
  let add := fun (a b : AtPrime PS (pointIdeal PS x)) => a + b
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = -(p 2 j x hx * a (v 0)) + -(p 3 j x hx * a (v 1)) :=
        congrArg₂ add (congrArg Neg.neg (hmul 2 (v 0))) (congrArg Neg.neg (hmul 3 (v 1)))
      _ = _ := congrArg₂ add (neg_mul (p 2 j x hx) (a (v 0))).symm rfl
  · exact congrArg₂ add (hmul 1 (v 0)) (congrArg Neg.neg (hmul 3 (v 2)))
  · exact congrArg₂ add (hmul 1 (v 1)) (hmul 2 (v 2))

set_option backward.isDefEq.respectTransparency false in
/-- The actual final differential into the zero twist becomes the explicit
last Koszul matrix. -/
theorem pointGlobalTraceP3Basis_last_stalk_coordinates
    (j : Fin 4) (x : Proj PS) (hx : (f j).val ∈ (pointIdeal PS x).primeCompl)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj
      (⨁ pointGlobalTraceP3CoordinateTriple K 1)) :
    pointGlobalTraceP3Basis_stalkCoordinate K f j x hx 0
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisKoszulLastZeroTwist K f) z) =
    threeGeneratorLast
      (pointGlobalTraceP3Basis_stalkParameter K f 1 j x hx)
      (pointGlobalTraceP3Basis_stalkParameter K f 2 j x hx)
      (pointGlobalTraceP3Basis_stalkParameter K f 3 j x hx)
      (pointGlobalTraceP3Basis_stalkTripleCoordinate K f j x hx 1 z) := by
  rw [pointGlobalTraceP3Basis_stalkTripleCoordinate_apply]
  simp only [pointGlobalTraceP3BasisKoszulLastZeroTwist,
    biproduct.desc_eq, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Functor.map_add, Functor.map_comp]
  have hmul (i : Fin 4) (w : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 1)) :
      pointGlobalTraceP3Basis_stalkCoordinate K f j x hx 0
        (((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisMul K f i 0)).hom w) =
      pointGlobalTraceP3Basis_stalkParameter K f i j x hx * pointGlobalTraceP3Basis_stalkCoordinate K f j x hx 1 w :=
    pointGlobalTraceP3Basis_stalkCoordinate_mul K f i j x hx 0 w
  simp [AddCommGrpCat.hom_add_apply, hmul,
    threeGeneratorLast, pointGlobalTraceP3Basis_stalkParameter]
  let v (i : Fin 3) : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 1) :=
    (schemeModuleStalkFunctor (Proj PS) x).map
      (biproduct.π (pointGlobalTraceP3CoordinateTriple K 1) i) z
  let add := fun (a b : AtPrime PS (pointIdeal PS x)) => a + b
  exact congrArg₂ add (congrArg₂ add (hmul 1 (v 0)) (hmul 2 (v 1))) (hmul 3 (v 2))

end PfaffianDescent.ProjectiveNegativeTwist
