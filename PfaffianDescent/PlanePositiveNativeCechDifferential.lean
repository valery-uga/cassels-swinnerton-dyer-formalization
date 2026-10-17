import PfaffianDescent.PlanePositiveNativeCechTerms
import PfaffianDescent.VoisinTwistCechLaurentDifferential
import PfaffianDescent.PlaneLaurentCechCore

/-! Actual positive-sheaf Čech differential versus its actual Laurent map.
The compatibility is derived, never supplied. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open ProjectiveNegativeTwist PlaneLaurentLocalization PlaneLaurentCechCore PlaneTwistLaurent PlaneTwistCechTerms
open PlaneTwistCechTerms.GenericEvaluation
open scoped AddMonoidAlgebra BigOperators
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K

/-- The actual cosimplicial section object of the SAME positive sheaf. -/
def p2PositiveNativeCechCosimplicial (m : ℕ) : CosimplicialObject AddCommGrpCat :=
  (FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ (p2StandardOpen (K := K))).cech).obj
    (positiveSheafOfModules PS m).presheaf

private theorem p2PositiveNativeCech_coface_comp_projection
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3) :
    let E := (FormalCoproduct.mk _ (p2StandardOpen (K := K))).cech
    let P := (positiveSheafOfModules PS m).presheaf
    (p2PositiveNativeCechCosimplicial K m).δ i ≫
        Pi.π (p2PositiveNativeCechTermFamily K m (n + 1)) f =
      Pi.π (p2PositiveNativeCechTermFamily K m n) (deleteTuple i f) ≫
        P.map ((E.map (SimplexCategory.δ i).op).φ f).op := by
  dsimp only
  simp only [p2PositiveNativeCechCosimplicial, CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  exact Pi.lift_π _ f

private theorem p2PositiveNativeCechComponentIsoBasic_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3) :
    let E := (FormalCoproduct.mk _ (p2StandardOpen (K := K))).cech
    let P := (positiveSheafOfModules PS m).presheaf
    let hST : p2CechBasicOpen K (n + 1) f ≤ p2CechBasicOpen K n (deleteTuple i f) :=
      Proj.basicOpen_mono PS
        (p2CechDenominator (K := K) n (deleteTuple i f))
        (p2CechDenominator (K := K) (n + 1) f)
        ⟨_, p2CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f⟩
    P.map ((E.map (SimplexCategory.δ i).op).φ f).op ≫
        (p2PositiveNativeCechComponentIsoBasic K m (n + 1) f).hom =
      (p2PositiveNativeCechComponentIsoBasic K m n (deleteTuple i f)).hom ≫
        P.map (homOfLE hST).op := by
  dsimp only
  simp only [p2PositiveNativeCechComponentIsoBasic, Functor.mapIso_hom]
  let P := (positiveSheafOfModules PS m).presheaf
  let E := (FormalCoproduct.mk _ (p2StandardOpen (K := K))).cech
  let U : (Proj PS).Opens :=
    ∏ᶜ fun a : Fin (n + 1) => p2StandardOpen (K := K) (deleteTuple i f a)
  let V : (Proj PS).Opens :=
    ∏ᶜ fun a : Fin (n + 2) => p2StandardOpen (K := K) (f a)
  let B : (Proj PS).Opens := p2CechBasicOpen K n (deleteTuple i f)
  let C : (Proj PS).Opens := p2CechBasicOpen K (n + 1) f
  let c : op U ⟶ op V := ((E.map (SimplexCategory.δ i).op).φ f).op
  let qS : op U ⟶ op B :=
    (eqToIso ((p2CechProduct_eq_inf K n (deleteTuple i f)).trans
      (p2CechBasicOpen_eq_inf (K := K) n (deleteTuple i f)).symm)).op.symm.hom
  let qT : op V ⟶ op C :=
    (eqToIso ((p2CechProduct_eq_inf K (n + 1) f).trans
      (p2CechBasicOpen_eq_inf (K := K) (n + 1) f).symm)).op.symm.hom
  let hST : C ≤ B :=
    Proj.basicOpen_mono PS
      (p2CechDenominator (K := K) n (deleteTuple i f))
      (p2CechDenominator (K := K) (n + 1) f)
      ⟨_, p2CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f⟩
  let t : op B ⟶ op C := (homOfLE hST).op
  have hOpen : c ≫ qT = qS ≫ t := Subsingleton.elim _ _
  have hLeft : P.map c ≫ P.map qT = P.map (c ≫ qT) :=
    (P.map_comp c qT).symm
  have hMiddle : P.map (c ≫ qT) = P.map (qS ≫ t) :=
    congrArg (fun a : op U ⟶ op C => P.map a) hOpen
  have hRight : P.map (qS ≫ t) = P.map qS ≫ P.map t :=
    P.map_comp qS t
  change P.map c ≫ P.map qT = P.map qS ≫ P.map t
  exact hLeft.trans (hMiddle.trans hRight)

/-- The SAME actual native Laurent map commutes with every canonical coface. -/
theorem p2PositiveNativeCechTermToLaurent_coface
    (m n : ℕ) (i : Fin (n + 2))
    (x : (p2PositiveNativeCechComplex K m).X n) (f : Fin (n + 2) → Fin 3) :
    p2PositiveNativeCechTermToLaurent K m (n + 1)
        ((p2PositiveNativeCechCosimplicial K m).δ i x) f =
      p2PositiveNativeCechTermToLaurent K m n x (deleteTuple i f) := by
  let E := (FormalCoproduct.mk _ (p2StandardOpen (K := K))).cech
  let P := (positiveSheafOfModules PS m).presheaf
  let hST : p2CechBasicOpen K (n + 1) f ≤ p2CechBasicOpen K n (deleteTuple i f) :=
    Proj.basicOpen_mono PS
      (p2CechDenominator (K := K) n (deleteTuple i f))
      (p2CechDenominator (K := K) (n + 1) f)
      ⟨_, p2CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f⟩
  let s := (Pi.π (p2PositiveNativeCechTermFamily K m n) (deleteTuple i f)) x
  have hπ := ConcreteCategory.congr_hom
    (p2PositiveNativeCech_coface_comp_projection K m n i f) x
  have hπ' :
      (Pi.π (p2PositiveNativeCechTermFamily K m (n + 1)) f)
          ((p2PositiveNativeCechCosimplicial K m).δ i x) =
        P.map ((E.map (SimplexCategory.δ i).op).φ f).op s := by
    exact (ConcreteCategory.comp_apply
      ((p2PositiveNativeCechCosimplicial K m).δ i)
      (Pi.π (p2PositiveNativeCechTermFamily K m (n + 1)) f) x).symm.trans
      (hπ.trans (ConcreteCategory.comp_apply
        (Pi.π (p2PositiveNativeCechTermFamily K m n) (deleteTuple i f))
        (P.map ((E.map (SimplexCategory.δ i).op).φ f).op) x))
  have hbasic := ConcreteCategory.congr_hom
    (p2PositiveNativeCechComponentIsoBasic_face K m n i f) s
  have hbasic' :
      (p2PositiveNativeCechComponentIsoBasic K m (n + 1) f).hom
          (P.map ((E.map (SimplexCategory.δ i).op).φ f).op s) =
        P.map (homOfLE hST).op
          ((p2PositiveNativeCechComponentIsoBasic K m n (deleteTuple i f)).hom s) := by
    exact (ConcreteCategory.comp_apply
      (P.map ((E.map (SimplexCategory.δ i).op).φ f).op)
      (p2PositiveNativeCechComponentIsoBasic K m (n + 1) f).hom s).symm.trans
      (hbasic.trans (ConcreteCategory.comp_apply
        (p2PositiveNativeCechComponentIsoBasic K m n (deleteTuple i f)).hom
        (P.map (homOfLE hST).op) s))
  change p2PositiveNativeChartToLaurent K m (n + 1) f
    (p2PositiveNativeCechTermAddEquivSections K m (n + 1)
      ((p2PositiveNativeCechCosimplicial K m).δ i x) f) =
    p2PositiveNativeChartToLaurent K m n (deleteTuple i f)
      (p2PositiveNativeCechTermAddEquivSections K m n x (deleteTuple i f))
  calc
    _ = p2PositiveNativeChartToLaurent K m (n + 1) f
        ((p2PositiveNativeCechComponentIsoBasic K m (n + 1) f).hom
          ((Pi.π (p2PositiveNativeCechTermFamily K m (n + 1)) f)
            ((p2PositiveNativeCechCosimplicial K m).δ i x))) :=
      congrArg (p2PositiveNativeChartToLaurent K m (n + 1) f)
        (p2PositiveNativeCechTermAddEquivSections_apply K m (n + 1)
          ((p2PositiveNativeCechCosimplicial K m).δ i x) f)
    _ = p2PositiveNativeChartToLaurent K m (n + 1) f
        ((p2PositiveNativeCechComponentIsoBasic K m (n + 1) f).hom
          (P.map ((E.map (SimplexCategory.δ i).op).φ f).op s)) :=
      congrArg (fun z : p2PositiveNativeCechTermFamily K m (n + 1) f =>
        p2PositiveNativeChartToLaurent K m (n + 1) f
          ((p2PositiveNativeCechComponentIsoBasic K m (n + 1) f).hom z)) hπ'
    _ = p2PositiveNativeChartToLaurent K m (n + 1) f
        (P.map (homOfLE hST).op
          ((p2PositiveNativeCechComponentIsoBasic K m n (deleteTuple i f)).hom s)) :=
      congrArg (p2PositiveNativeChartToLaurent K m (n + 1) f) hbasic'
    _ = p2PositiveNativeChartToLaurent K m n (deleteTuple i f)
        ((p2PositiveNativeCechComponentIsoBasic K m n (deleteTuple i f)).hom s) :=
      p2PositiveNativeChartToLaurent_restrict_face K m n i f
        ((p2PositiveNativeCechComponentIsoBasic K m n (deleteTuple i f)).hom s)
    _ = _ := congrArg (p2PositiveNativeChartToLaurent K m n (deleteTuple i f))
      (p2PositiveNativeCechTermAddEquivSections_apply K m n x (deleteTuple i f)).symm

private theorem p2PositiveNativeCechComplex_d_succ (m n : ℕ) :
    (p2PositiveNativeCechComplex K m).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (p2PositiveNativeCechCosimplicial K m) n := by
  simp [p2PositiveNativeCechComplex, CategoryTheory.cechComplexFunctor,
    FormalCoproduct.cochainComplexFunctor, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, p2PositiveNativeCechCosimplicial]
  congr

/-- Differential compatibility holds for the actual native canonical
complex and map in every degree, with its actual alternating signs. -/
theorem p2PositiveNativeCechTermToLaurent_d
    (m n : ℕ) (x : (p2PositiveNativeCechComplex K m).X n) :
    p2PositiveNativeCechTermToLaurent K m (n + 1)
        ((p2PositiveNativeCechComplex K m).d n (n + 1) x) =
      fun f => ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        p2PositiveNativeCechTermToLaurent K m n x (deleteTuple i f) := by
  funext f
  rw [p2PositiveNativeCechComplex_d_succ, AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  calc
    _ = p2PositiveNativeCechTermToLaurent K m (n + 1)
        (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          ((p2PositiveNativeCechCosimplicial K m).δ i x)) f := by
      exact congrArg
        (fun q : (p2PositiveNativeCechComplex K m).X (n + 1) =>
          p2PositiveNativeCechTermToLaurent K m (n + 1) q f)
        (addCommGrp_finset_sum_zsmul_apply Finset.univ
          (fun i : Fin (n + 2) => (-1 : ℤ) ^ (i : ℕ))
          (fun i => (p2PositiveNativeCechCosimplicial K m).δ i) x)
    _ = (∑ i : Fin (n + 2),
        p2PositiveNativeCechTermToLaurent K m (n + 1)
          (((-1 : ℤ) ^ (i : ℕ)) •
            ((p2PositiveNativeCechCosimplicial K m).δ i x))) f := by
      exact congrFun (map_sum
        (p2PositiveNativeCechTermToLaurent K m (n + 1))
        (fun i : Fin (n + 2) => ((-1 : ℤ) ^ (i : ℕ)) •
          ((p2PositiveNativeCechCosimplicial K m).δ i x)) Finset.univ) f
    _ = _ := by
      rw [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      let v : (p2PositiveNativeCechComplex K m).X (n + 1) :=
        (p2PositiveNativeCechCosimplicial K m).δ i x
      change p2PositiveNativeCechTermToLaurent K m (n + 1)
        (((-1 : ℤ) ^ (i : ℕ)) • v) f = _
      have hz := map_zsmul (p2PositiveNativeCechTermToLaurent K m (n + 1))
        ((-1 : ℤ) ^ (i : ℕ)) v
      calc
        _ = (((-1 : ℤ) ^ (i : ℕ)) •
            p2PositiveNativeCechTermToLaurent K m (n + 1) v) f := congrFun hz f
        _ = ((-1 : ℤ) ^ (i : ℕ)) •
            p2PositiveNativeCechTermToLaurent K m (n + 1) v f := rfl
        _ = _ := congrArg (((-1 : ℤ) ^ (i : ℕ)) • ·)
          (p2PositiveNativeCechTermToLaurent_coface K m n i x f)

/-- Degree zero compatibility in the literal Laurent tuple notation. -/
theorem p2PositiveNativeCechTermToLaurent_d_zero
    (m : ℕ) (x : (p2PositiveNativeCechComplex K m).X 0) :
    p2PositiveNativeCechTermToLaurent K m 1 ((p2PositiveNativeCechComplex K m).d 0 1 x) =
      tupleD0 (p2PositiveNativeCechTermToLaurent K m 0 x) := by
  rw [p2PositiveNativeCechTermToLaurent_d]
  funext f
  have hdel0 : deleteTuple (n := 0) 0 f = ![f 1] := by
    funext j
    fin_cases j <;> rfl
  have hdel1 : deleteTuple (n := 0) 1 f = ![f 0] := by
    funext j
    fin_cases j <;> rfl
  simp [Fin.sum_univ_two, tupleD0, sub_eq_add_neg, hdel0, hdel1]

/-- Degree one compatibility in the literal Laurent tuple notation. -/
theorem p2PositiveNativeCechTermToLaurent_d_one
    (m : ℕ) (x : (p2PositiveNativeCechComplex K m).X 1) :
    p2PositiveNativeCechTermToLaurent K m 2 ((p2PositiveNativeCechComplex K m).d 1 2 x) =
      tupleD1 (p2PositiveNativeCechTermToLaurent K m 1 x) := by
  rw [p2PositiveNativeCechTermToLaurent_d]
  funext f
  have hdel0 : deleteTuple (n := 1) 0 f = ![f 1, f 2] := by
    funext j
    fin_cases j <;> rfl
  have hdel1 : deleteTuple (n := 1) 1 f = ![f 0, f 2] := by
    funext j
    fin_cases j <;> rfl
  have hdel2 : deleteTuple (n := 1) 2 f = ![f 0, f 1] := by
    funext j
    fin_cases j <;> rfl
  simp [Fin.sum_univ_three, tupleD1, sub_eq_add_neg, hdel0, hdel1, hdel2]

/-- Degree two compatibility in the literal Laurent tuple notation. -/
theorem p2PositiveNativeCechTermToLaurent_d_two
    (m : ℕ) (x : (p2PositiveNativeCechComplex K m).X 2) :
    p2PositiveNativeCechTermToLaurent K m 3 ((p2PositiveNativeCechComplex K m).d 2 3 x) =
      tupleD2 (p2PositiveNativeCechTermToLaurent K m 2 x) := by
  rw [p2PositiveNativeCechTermToLaurent_d]
  funext f
  have hdel0 : deleteTuple (n := 2) 0 f = ![f 1, f 2, f 3] := by
    funext j
    fin_cases j <;> rfl
  have hdel1 : deleteTuple (n := 2) 1 f = ![f 0, f 2, f 3] := by
    funext j
    fin_cases j <;> rfl
  have hdel2 : deleteTuple (n := 2) 2 f = ![f 0, f 1, f 3] := by
    funext j
    fin_cases j <;> rfl
  have hdel3 : deleteTuple (n := 2) 3 f = ![f 0, f 1, f 2] := by
    funext j
    fin_cases j <;> rfl
  simp [Fin.sum_univ_four, tupleD2, sub_eq_add_neg, hdel0, hdel1, hdel2, hdel3,
    pow_succ]

end PfaffianDescent.ProjectivePlaneNative
