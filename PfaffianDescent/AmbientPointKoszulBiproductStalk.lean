import PfaffianDescent.AmbientPointKoszulStalkExactness
import Mathlib.Algebra.Category.Grp.Biproducts

/-! # Actual finite-sum stalk coordinates of the projective point Koszul complex -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

local instance ambientPointKoszul_biproductPointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

private def finThreeAddEquiv (A : Type u) [AddCommGroup A] :
    (Fin 3 → A) ≃+ (A × A × A) where
  toFun z := (z 0, z 1, z 2)
  invFun z := ![z.1, z.2.1, z.2.2]
  left_inv z := by funext i; fin_cases i <;> rfl
  right_inv z := rfl
  map_add' z w := rfl

/-- The actual stalk of the rank-three twist term, as its three summand stalks. -/
def ambientPointKoszul_stalkPiIso (x : Proj PS) (m : ℕ) :
    (schemeModuleStalkFunctor (Proj PS) x).obj
        (⨁ pointGlobalTraceP3CoordinateTriple K m) ≅
      AddCommGrpCat.of (Fin 3 →
        (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS m)) := by
  let F := schemeModuleStalkFunctor (Proj PS) x
  let P := pointGlobalTraceP3CoordinateTriple K m
  exact F.mapBiproduct P ≪≫ AddCommGrpCat.biproductIsoPi (F.obj ∘ P)

set_option backward.isDefEq.respectTransparency false in
private theorem piIso_hom_comp_eval (x : Proj PS) (m : ℕ) (i : Fin 3) :
    (ambientPointKoszul_stalkPiIso K x m).hom ≫
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
  simp only [ambientPointKoszul_stalkPiIso, Iso.trans_hom, Category.assoc]
  change (F.mapBiproduct P).hom ≫ (AddCommGrpCat.biproductIsoPi Q).hom ≫
    AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun i => Q i) i) = F.map (biproduct.π P i)
  rw [h]
  change (biproduct.lift fun i => F.map (biproduct.π P i)) ≫ biproduct.π Q i = _
  exact biproduct.lift_π _ i

/-- Coordinates of the actual finite-sum stalk, in the homogeneous local ring. -/
def ambientPointKoszul_stalkTripleCoordinate
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) (m : ℕ) :
    (↑((schemeModuleStalkFunctor (Proj PS) x).obj
        (⨁ pointGlobalTraceP3CoordinateTriple K m)) : Type u) ≃+
      (AtPrime PS (pointIdeal PS x) × AtPrime PS (pointIdeal PS x) ×
        AtPrime PS (pointIdeal PS x)) :=
  (ambientPointKoszul_stalkPiIso K x m).addCommGroupIsoToAddEquiv.trans
    ((AddEquiv.piCongrRight fun _ : Fin 3 => ambientPointKoszul_stalkCoordinate K j x hx m).trans
      (finThreeAddEquiv _))

set_option backward.isDefEq.respectTransparency false in
theorem ambientPointKoszul_stalkTripleCoordinate_apply
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) (m : ℕ)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj
      (⨁ pointGlobalTraceP3CoordinateTriple K m)) :
    ambientPointKoszul_stalkTripleCoordinate K j x hx m z =
      (ambientPointKoszul_stalkCoordinate K j x hx m
        ((schemeModuleStalkFunctor (Proj PS) x).map
          (biproduct.π (pointGlobalTraceP3CoordinateTriple K m) 0) z),
       ambientPointKoszul_stalkCoordinate K j x hx m
        ((schemeModuleStalkFunctor (Proj PS) x).map
          (biproduct.π (pointGlobalTraceP3CoordinateTriple K m) 1) z),
       ambientPointKoszul_stalkCoordinate K j x hx m
        ((schemeModuleStalkFunctor (Proj PS) x).map
          (biproduct.π (pointGlobalTraceP3CoordinateTriple K m) 2) z)) := by
  have h (i : Fin 3) := ConcreteCategory.congr_hom (piIso_hom_comp_eval K x m i) z
  change (ambientPointKoszul_stalkCoordinate K j x hx m
        ((ambientPointKoszul_stalkPiIso K x m).hom z 0),
      ambientPointKoszul_stalkCoordinate K j x hx m
        ((ambientPointKoszul_stalkPiIso K x m).hom z 1),
      ambientPointKoszul_stalkCoordinate K j x hx m
        ((ambientPointKoszul_stalkPiIso K x m).hom z 2)) = _
  rw [show (ambientPointKoszul_stalkPiIso K x m).hom z 0 = _ from h 0,
    show (ambientPointKoszul_stalkPiIso K x m).hom z 1 = _ from h 1,
    show (ambientPointKoszul_stalkPiIso K x m).hom z 2 = _ from h 2]

set_option backward.isDefEq.respectTransparency false in
/-- The actual first differential becomes the explicit first Koszul matrix. -/
theorem ambientPointKoszul_first_stalk_coordinates
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 3)) :
    ambientPointKoszul_stalkTripleCoordinate K j x hx 2
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateKoszulFirst K) z) =
    threeGeneratorFirst
      (ambientPointKoszul_stalkParameter K 1 j x hx)
      (ambientPointKoszul_stalkParameter K 2 j x hx)
      (ambientPointKoszul_stalkParameter K 3 j x hx)
      (ambientPointKoszul_stalkCoordinate K j x hx 3 z) := by
  rw [ambientPointKoszul_stalkTripleCoordinate_apply]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    pointGlobalTraceP3CoordinateKoszulFirst, biproduct.lift_π,
    Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Functor.map_neg]
  simp [threeGeneratorFirst,
    ambientPointKoszul_stalkParameter, neg_mul]
  refine ⟨ambientPointKoszul_stalkCoordinate_mul K 3 j x hx 2 z, ?_,
    ambientPointKoszul_stalkCoordinate_mul K 1 j x hx 2 z⟩
  change -(ambientPointKoszul_stalkCoordinate K j x hx 2
    ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateMul K 2 2) z)) = _
  rw [ambientPointKoszul_stalkCoordinate_mul]
  exact (neg_mul (ambientPointKoszul_stalkParameter K 2 j x hx)
    (ambientPointKoszul_stalkCoordinate K j x hx 3 z)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual middle differential becomes the explicit middle Koszul matrix. -/
theorem ambientPointKoszul_middle_stalk_coordinates
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj
      (⨁ pointGlobalTraceP3CoordinateTriple K 2)) :
    ambientPointKoszul_stalkTripleCoordinate K j x hx 1
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateKoszulMiddle K) z) =
    threeGeneratorMiddle
      (ambientPointKoszul_stalkParameter K 1 j x hx)
      (ambientPointKoszul_stalkParameter K 2 j x hx)
      (ambientPointKoszul_stalkParameter K 3 j x hx)
      (ambientPointKoszul_stalkTripleCoordinate K j x hx 2 z) := by
  rw [ambientPointKoszul_stalkTripleCoordinate_apply, ambientPointKoszul_stalkTripleCoordinate_apply]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    pointGlobalTraceP3CoordinateKoszulMiddle, biproduct.matrix_π]
  simp only [biproduct.desc_eq, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    comp_zero, add_zero, zero_add, Functor.map_add, Functor.map_neg, Functor.map_comp]
  have hmul (i : Fin 4) (w : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 2)) :
      ambientPointKoszul_stalkCoordinate K j x hx 1
        (((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateMul K i 1)).hom w) =
      ambientPointKoszul_stalkParameter K i j x hx * ambientPointKoszul_stalkCoordinate K j x hx 2 w :=
    ambientPointKoszul_stalkCoordinate_mul K i j x hx 1 w
  simp [AddCommGrpCat.hom_add_apply, hmul,
    threeGeneratorMiddle, ambientPointKoszul_stalkParameter, sub_eq_add_neg, neg_mul]
  let v (i : Fin 3) : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 2) :=
    (schemeModuleStalkFunctor (Proj PS) x).map
      (biproduct.π (pointGlobalTraceP3CoordinateTriple K 2) i) z
  let a := ambientPointKoszul_stalkCoordinate K j x hx 2
  let p := ambientPointKoszul_stalkParameter K
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
theorem ambientPointKoszul_last_stalk_coordinates
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj
      (⨁ pointGlobalTraceP3CoordinateTriple K 1)) :
    ambientPointKoszul_stalkCoordinate K j x hx 0
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateKoszulLastZeroTwist K) z) =
    threeGeneratorLast
      (ambientPointKoszul_stalkParameter K 1 j x hx)
      (ambientPointKoszul_stalkParameter K 2 j x hx)
      (ambientPointKoszul_stalkParameter K 3 j x hx)
      (ambientPointKoszul_stalkTripleCoordinate K j x hx 1 z) := by
  rw [ambientPointKoszul_stalkTripleCoordinate_apply]
  simp only [pointGlobalTraceP3CoordinateKoszulLastZeroTwist,
    biproduct.desc_eq, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Functor.map_add, Functor.map_comp]
  have hmul (i : Fin 4) (w : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 1)) :
      ambientPointKoszul_stalkCoordinate K j x hx 0
        (((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateMul K i 0)).hom w) =
      ambientPointKoszul_stalkParameter K i j x hx * ambientPointKoszul_stalkCoordinate K j x hx 1 w :=
    ambientPointKoszul_stalkCoordinate_mul K i j x hx 0 w
  simp [AddCommGrpCat.hom_add_apply, hmul,
    threeGeneratorLast, ambientPointKoszul_stalkParameter]
  let v (i : Fin 3) : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 1) :=
    (schemeModuleStalkFunctor (Proj PS) x).map
      (biproduct.π (pointGlobalTraceP3CoordinateTriple K 1) i) z
  let add := fun (a b : AtPrime PS (pointIdeal PS x)) => a + b
  exact congrArg₂ add (congrArg₂ add (hmul 1 (v 0)) (hmul 2 (v 1))) (hmul 3 (v 2))

end PfaffianDescent.ProjectiveNegativeTwist
