import PfaffianDescent.ThreeQuadricSheafKoszulComplex
import PfaffianDescent.HomogeneousKoszulFractionExactMiddle
import PfaffianDescent.AmbientPointKoszulBiproductStalk

/-! SOURCE ONLY / UNVERIFIED. Actual categorical stalk/fraction squares for
arbitrary quadric Koszul maps. The existing point provider is used ONLY for
its generic biproduct stalk Iso, never for point-equation regularity. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
local instance threeQuadricFraction_pointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

private def threeQuadricFractionFinThreeAddEquiv (A : Type u) [AddCommGroup A] :
    (Fin 3 → A) ≃+ (A × A × A) where
  toFun z := (z 0, z 1, z 2)
  invFun z := ![z.1, z.2.1, z.2.2]
  left_inv z := by funext i; fin_cases i <;> rfl
  right_inv z := rfl
  map_add' z w := rfl

/-- Existing actual generic finite-sum stalk Iso followed by actual fraction
models. No normalized coordinates or comparison certificate are input. -/
def threeQuadricFraction_stalkTripleCoordinate (x : Proj PS) (m : ℕ) :
    (↑((schemeModuleStalkFunctor (Proj PS) x).obj
      (⨁ threeQuadricSheafTriple K m)) : Type u) ≃+
      homogeneousKoszulFractionTriple (pointIdeal PS x) m :=
  (ambientPointKoszul_stalkPiIso K x m).addCommGroupIsoToAddEquiv.trans
    ((AddEquiv.piCongrRight fun _ : Fin 3 => stalkAddEquivFractionModule PS m x).trans
      (threeQuadricFractionFinThreeAddEquiv _))

private theorem threeQuadricFraction_piIso_projection (x : Proj PS) (m : ℕ) (i : Fin 3) :
    (ambientPointKoszul_stalkPiIso K x m).hom ≫
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun _ : Fin 3 =>
        (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS m)) i) =
    (schemeModuleStalkFunctor (Proj PS) x).map
      (biproduct.π (threeQuadricSheafTriple K m) i) := by
  let F := schemeModuleStalkFunctor (Proj PS) x
  let P := threeQuadricSheafTriple K m
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

theorem threeQuadricFraction_stalkTripleCoordinate_apply
    (x : Proj PS) (m : ℕ)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj (⨁ threeQuadricSheafTriple K m)) :
    threeQuadricFraction_stalkTripleCoordinate K x m z =
      (stalkAddEquivFractionModule PS m x ((schemeModuleStalkFunctor (Proj PS) x).map
        (biproduct.π (threeQuadricSheafTriple K m) 0) z),
       stalkAddEquivFractionModule PS m x ((schemeModuleStalkFunctor (Proj PS) x).map
        (biproduct.π (threeQuadricSheafTriple K m) 1) z),
       stalkAddEquivFractionModule PS m x ((schemeModuleStalkFunctor (Proj PS) x).map
        (biproduct.π (threeQuadricSheafTriple K m) 2) z)) := by
  have h (i : Fin 3) := ConcreteCategory.congr_hom
    (threeQuadricFraction_piIso_projection K x m i) z
  change (stalkAddEquivFractionModule PS m x ((ambientPointKoszul_stalkPiIso K x m).hom z 0),
    stalkAddEquivFractionModule PS m x ((ambientPointKoszul_stalkPiIso K x m).hom z 1),
    stalkAddEquivFractionModule PS m x ((ambientPointKoszul_stalkPiIso K x m).hom z 2)) = _
  rw [show (ambientPointKoszul_stalkPiIso K x m).hom z 0 = _ from h 0,
    show (ambientPointKoszul_stalkPiIso K x m).hom z 1 = _ from h 1,
    show (ambientPointKoszul_stalkPiIso K x m).hom z 2 = _ from h 2]

/-- Exact actual categorical multiplication/fraction square. -/
theorem threeQuadricFraction_stalkCoordinate_mul
    (q : PS 2) (x : Proj PS) (m : ℕ)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS (m + 2))) :
    stalkAddEquivFractionModule PS m x
      ((schemeModuleStalkFunctor (Proj PS) x).map (threeQuadricSheafMul K q m) z) =
    mulHomogeneousStalk PS (pointIdeal PS x) q m
      (stalkAddEquivFractionModule PS (m + 2) x z) :=
  stalkToFractionModule_stalkMap PS q m x z

-- Normalize the precise ConcreteCategory.hom projection occurring after
-- stalk-functor/biproduct computation, before using the fraction squares.
private theorem threeQuadricFraction_hom_add_apply
    {S T : AddCommGrpCat.{u}} (a b : S ⟶ T) (z : S) :
    ConcreteCategory.hom (a + b) z =
      ConcreteCategory.hom a z + ConcreteCategory.hom b z := rfl

private theorem threeQuadricFraction_hom_neg_apply
    {S T : AddCommGrpCat.{u}} (a : S ⟶ T) (z : S) :
    ConcreteCategory.hom (-a) z = -ConcreteCategory.hom a z := rfl

private theorem threeQuadricFraction_hom_comp_apply
    {S T V : AddCommGrpCat.{u}} (a : S ⟶ T) (b : T ⟶ V) (z : S) :
    ConcreteCategory.hom (a ≫ b) z =
      ConcreteCategory.hom b (ConcreteCategory.hom a z) := rfl

theorem threeQuadricFraction_first_stalk_coordinates
    (f g h : PS 2) (x : Proj PS)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 6)) :
    threeQuadricFraction_stalkTripleCoordinate K x 4
      ((schemeModuleStalkFunctor (Proj PS) x).map (threeQuadricSheafKoszulFirst K f g h) z) =
    homogeneousKoszulFractionFirst (pointIdeal PS x) f g h
      (stalkAddEquivFractionModule PS 6 x z) := by
  rw [threeQuadricFraction_stalkTripleCoordinate_apply]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    threeQuadricSheafKoszulFirst, biproduct.lift_π,
    Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Functor.map_neg]
  simp only [threeQuadricFraction_hom_neg_apply]
  have hmul (q : PS 2)
      (w : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 6)) :
      stalkAddEquivFractionModule PS 4 x
        (ConcreteCategory.hom ((schemeModuleStalkFunctor (Proj PS) x).map
          (threeQuadricSheafMul K q 4)) w) =
      mulHomogeneousStalk PS (pointIdeal PS x) q 4
        (stalkAddEquivFractionModule PS 6 x w) :=
    threeQuadricFraction_stalkCoordinate_mul K q x 4 w
  let A := stalkAddEquivFractionModule PS 4 x
  let T (q : PS 2) := ConcreteCategory.hom
    ((schemeModuleStalkFunctor (Proj PS) x).map (threeQuadricSheafMul K q 4)) z
  have hneg : A (-T g) =
      -mulHomogeneousStalk PS (pointIdeal PS x) g 4
        (stalkAddEquivFractionModule PS 6 x z) :=
    (A.map_neg (T g)).trans (congrArg (fun y => -y) (hmul g z))
  change (A (T h), A (-T g), A (T f)) = _
  exact Prod.ext (hmul h z) (Prod.ext hneg (hmul f z))

theorem threeQuadricFraction_middle_stalk_coordinates
    (f g h : PS 2) (x : Proj PS)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj (⨁ threeQuadricSheafTriple K 4)) :
    threeQuadricFraction_stalkTripleCoordinate K x 2
      ((schemeModuleStalkFunctor (Proj PS) x).map (threeQuadricSheafKoszulMiddle K f g h) z) =
    homogeneousKoszulFractionMiddle (pointIdeal PS x) f g h
      (threeQuadricFraction_stalkTripleCoordinate K x 4 z) := by
  rw [threeQuadricFraction_stalkTripleCoordinate_apply,
    threeQuadricFraction_stalkTripleCoordinate_apply]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    threeQuadricSheafKoszulMiddle, biproduct.matrix_π]
  simp only [biproduct.desc_eq, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    comp_zero, add_zero, zero_add, Functor.map_add, Functor.map_neg, Functor.map_comp]
  simp only [threeQuadricFraction_hom_add_apply,
    threeQuadricFraction_hom_comp_apply, threeQuadricFraction_hom_neg_apply]
  have hmul (q : PS 2)
      (w : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 4)) :
      stalkAddEquivFractionModule PS 2 x
        (ConcreteCategory.hom ((schemeModuleStalkFunctor (Proj PS) x).map
          (threeQuadricSheafMul K q 2)) w) =
      mulHomogeneousStalk PS (pointIdeal PS x) q 2
        (stalkAddEquivFractionModule PS 4 x w) :=
    threeQuadricFraction_stalkCoordinate_mul K q x 2 w
  let A := stalkAddEquivFractionModule PS 2 x
  let w (i : Fin 3) :
      (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 4) :=
    ConcreteCategory.hom ((schemeModuleStalkFunctor (Proj PS) x).map
      (biproduct.π (threeQuadricSheafTriple K 4) i)) z
  let T (q : PS 2) (i : Fin 3) := ConcreteCategory.hom
    ((schemeModuleStalkFunctor (Proj PS) x).map (threeQuadricSheafMul K q 2)) (w i)
  let B (q : PS 2) (i : Fin 3) :=
    mulHomogeneousStalk PS (pointIdeal PS x) q 2
      (stalkAddEquivFractionModule PS 4 x (w i))
  have hneg (q : PS 2) (i : Fin 3) : A (-T q i) = -B q i :=
    (A.map_neg (T q i)).trans
      (congrArg (fun y => -y) (hmul q (w i)))
  have h0 : A (-T g 0 + -T h 1) = -B g 0 + -B h 1 :=
    (A.map_add (-T g 0) (-T h 1)).trans
      (congrArg₂ (fun a b => a + b) (hneg g 0) (hneg h 1))
  have h1 : A (T f 0 + -T h 2) = B f 0 + -B h 2 :=
    (A.map_add (T f 0) (-T h 2)).trans
      (congrArg₂ (fun a b => a + b) (hmul f (w 0)) (hneg h 2))
  have h2 : A (T f 1 + T g 2) = B f 1 + B g 2 :=
    (A.map_add (T f 1) (T g 2)).trans
      (congrArg₂ (fun a b => a + b) (hmul f (w 1)) (hmul g (w 2)))
  change (A (-T g 0 + -T h 1), A (T f 0 + -T h 2), A (T f 1 + T g 2)) =
    (-B g 0 - B h 1, B f 0 - B h 2, B f 1 + B g 2)
  simpa only [sub_eq_add_neg] using Prod.ext h0 (Prod.ext h1 h2)

theorem threeQuadricFraction_last_stalk_coordinates
    (f g h : PS 2) (x : Proj PS)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj (⨁ threeQuadricSheafTriple K 2)) :
    stalkAddEquivFractionModule PS 0 x
      ((schemeModuleStalkFunctor (Proj PS) x).map (threeQuadricSheafKoszulLastZeroTwist K f g h) z) =
    homogeneousKoszulFractionLast (pointIdeal PS x) f g h
      (threeQuadricFraction_stalkTripleCoordinate K x 2 z) := by
  rw [threeQuadricFraction_stalkTripleCoordinate_apply]
  simp only [threeQuadricSheafKoszulLastZeroTwist,
    biproduct.desc_eq, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Functor.map_add, Functor.map_comp]
  simp only [threeQuadricFraction_hom_add_apply,
    threeQuadricFraction_hom_comp_apply]
  have hmul (q : PS 2)
      (w : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 2)) :
      stalkAddEquivFractionModule PS 0 x
        (ConcreteCategory.hom ((schemeModuleStalkFunctor (Proj PS) x).map
          (threeQuadricSheafMul K q 0)) w) =
      mulHomogeneousStalk PS (pointIdeal PS x) q 0
        (stalkAddEquivFractionModule PS 2 x w) :=
    threeQuadricFraction_stalkCoordinate_mul K q x 0 w
  let A := stalkAddEquivFractionModule PS 0 x
  let w (i : Fin 3) :
      (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS 2) :=
    ConcreteCategory.hom ((schemeModuleStalkFunctor (Proj PS) x).map
      (biproduct.π (threeQuadricSheafTriple K 2) i)) z
  let T (q : PS 2) (i : Fin 3) := ConcreteCategory.hom
    ((schemeModuleStalkFunctor (Proj PS) x).map (threeQuadricSheafMul K q 0)) (w i)
  let B (q : PS 2) (i : Fin 3) :=
    mulHomogeneousStalk PS (pointIdeal PS x) q 0
      (stalkAddEquivFractionModule PS 2 x (w i))
  have hfg : A (T f 0 + T g 1) = B f 0 + B g 1 :=
    (A.map_add (T f 0) (T g 1)).trans
      (congrArg₂ (fun a b => a + b) (hmul f (w 0)) (hmul g (w 1)))
  change A ((T f 0 + T g 1) + T h 2) = (B f 0 + B g 1) + B h 2
  exact (A.map_add (T f 0 + T g 1) (T h 2)).trans
    (congrArg₂ (fun a b => a + b) hfg (hmul h (w 2)))

end PfaffianDescent.ProjectiveNegativeTwist
