import PfaffianDescent.CorayPositiveNativeCechTerms
import PfaffianDescent.VoisinP3TopCechDifferential

/-! Actual positive-sheaf Čech differential versus its actual Laurent map.
The compatibility is derived, never supplied. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open LaurentLocalization LaurentCechCore TwistLaurent TwistCechTerms
open TwistCechTerms.GenericEvaluation
open scoped AddMonoidAlgebra BigOperators
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The actual cosimplicial section object of the SAME positive sheaf. -/
def p3PositiveNativeCechCosimplicial (m : ℕ) : CosimplicialObject AddCommGrpCat :=
  (FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ (p3StandardOpen (K := K))).cech).obj
    (positiveSheafOfModules PS m).presheaf

private theorem p3PositiveNativeCech_coface_comp_projection
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4) :
    let E := (FormalCoproduct.mk _ (p3StandardOpen (K := K))).cech
    let P := (positiveSheafOfModules PS m).presheaf
    (p3PositiveNativeCechCosimplicial K m).δ i ≫
        Pi.π (p3PositiveNativeCechTermFamily K m (n + 1)) f =
      Pi.π (p3PositiveNativeCechTermFamily K m n) (deleteTuple i f) ≫
        P.map ((E.map (SimplexCategory.δ i).op).φ f).op := by
  dsimp only
  simp only [p3PositiveNativeCechCosimplicial, CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  exact Pi.lift_π _ f

private theorem p3PositiveNativeCechComponentIsoBasic_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4) :
    let E := (FormalCoproduct.mk _ (p3StandardOpen (K := K))).cech
    let P := (positiveSheafOfModules PS m).presheaf
    let hST : cechBasicOpen K (n + 1) f ≤ cechBasicOpen K n (deleteTuple i f) :=
      Proj.basicOpen_mono PS
        (p3CechDenominator (K := K) n (deleteTuple i f))
        (p3CechDenominator (K := K) (n + 1) f)
        ⟨_, p3CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f⟩
    P.map ((E.map (SimplexCategory.δ i).op).φ f).op ≫
        (p3PositiveNativeCechComponentIsoBasic K m (n + 1) f).hom =
      (p3PositiveNativeCechComponentIsoBasic K m n (deleteTuple i f)).hom ≫
        P.map (homOfLE hST).op := by
  dsimp only
  simp only [p3PositiveNativeCechComponentIsoBasic, Functor.mapIso_hom]
  let P := (positiveSheafOfModules PS m).presheaf
  let E := (FormalCoproduct.mk _ (p3StandardOpen (K := K))).cech
  let U : (Proj PS).Opens :=
    ∏ᶜ fun a : Fin (n + 1) => p3StandardOpen (K := K) (deleteTuple i f a)
  let V : (Proj PS).Opens :=
    ∏ᶜ fun a : Fin (n + 2) => p3StandardOpen (K := K) (f a)
  let B : (Proj PS).Opens := cechBasicOpen K n (deleteTuple i f)
  let C : (Proj PS).Opens := cechBasicOpen K (n + 1) f
  let c : op U ⟶ op V := ((E.map (SimplexCategory.δ i).op).φ f).op
  let qS : op U ⟶ op B :=
    (eqToIso ((p3CechProduct_eq_inf K n (deleteTuple i f)).trans
      (p3CechBasicOpen_eq_inf (K := K) n (deleteTuple i f)).symm)).op.symm.hom
  let qT : op V ⟶ op C :=
    (eqToIso ((p3CechProduct_eq_inf K (n + 1) f).trans
      (p3CechBasicOpen_eq_inf (K := K) (n + 1) f).symm)).op.symm.hom
  let hST : C ≤ B :=
    Proj.basicOpen_mono PS
      (p3CechDenominator (K := K) n (deleteTuple i f))
      (p3CechDenominator (K := K) (n + 1) f)
      ⟨_, p3CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f⟩
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
theorem p3PositiveNativeCechTermToLaurent_coface
    (m n : ℕ) (i : Fin (n + 2))
    (x : (p3PositiveNativeCechComplex K m).X n) (f : Fin (n + 2) → Fin 4) :
    p3PositiveNativeCechTermToLaurent K m (n + 1)
        ((p3PositiveNativeCechCosimplicial K m).δ i x) f =
      p3PositiveNativeCechTermToLaurent K m n x (deleteTuple i f) := by
  let E := (FormalCoproduct.mk _ (p3StandardOpen (K := K))).cech
  let P := (positiveSheafOfModules PS m).presheaf
  let hST : cechBasicOpen K (n + 1) f ≤ cechBasicOpen K n (deleteTuple i f) :=
    Proj.basicOpen_mono PS
      (p3CechDenominator (K := K) n (deleteTuple i f))
      (p3CechDenominator (K := K) (n + 1) f)
      ⟨_, p3CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f⟩
  let s := (Pi.π (p3PositiveNativeCechTermFamily K m n) (deleteTuple i f)) x
  have hπ := ConcreteCategory.congr_hom
    (p3PositiveNativeCech_coface_comp_projection K m n i f) x
  have hπ' :
      (Pi.π (p3PositiveNativeCechTermFamily K m (n + 1)) f)
          ((p3PositiveNativeCechCosimplicial K m).δ i x) =
        P.map ((E.map (SimplexCategory.δ i).op).φ f).op s := by
    exact (ConcreteCategory.comp_apply
      ((p3PositiveNativeCechCosimplicial K m).δ i)
      (Pi.π (p3PositiveNativeCechTermFamily K m (n + 1)) f) x).symm.trans
      (hπ.trans (ConcreteCategory.comp_apply
        (Pi.π (p3PositiveNativeCechTermFamily K m n) (deleteTuple i f))
        (P.map ((E.map (SimplexCategory.δ i).op).φ f).op) x))
  have hbasic := ConcreteCategory.congr_hom
    (p3PositiveNativeCechComponentIsoBasic_face K m n i f) s
  have hbasic' :
      (p3PositiveNativeCechComponentIsoBasic K m (n + 1) f).hom
          (P.map ((E.map (SimplexCategory.δ i).op).φ f).op s) =
        P.map (homOfLE hST).op
          ((p3PositiveNativeCechComponentIsoBasic K m n (deleteTuple i f)).hom s) := by
    exact (ConcreteCategory.comp_apply
      (P.map ((E.map (SimplexCategory.δ i).op).φ f).op)
      (p3PositiveNativeCechComponentIsoBasic K m (n + 1) f).hom s).symm.trans
      (hbasic.trans (ConcreteCategory.comp_apply
        (p3PositiveNativeCechComponentIsoBasic K m n (deleteTuple i f)).hom
        (P.map (homOfLE hST).op) s))
  change p3PositiveNativeChartToLaurent K m (n + 1) f
    (p3PositiveNativeCechTermAddEquivSections K m (n + 1)
      ((p3PositiveNativeCechCosimplicial K m).δ i x) f) =
    p3PositiveNativeChartToLaurent K m n (deleteTuple i f)
      (p3PositiveNativeCechTermAddEquivSections K m n x (deleteTuple i f))
  calc
    _ = p3PositiveNativeChartToLaurent K m (n + 1) f
        ((p3PositiveNativeCechComponentIsoBasic K m (n + 1) f).hom
          ((Pi.π (p3PositiveNativeCechTermFamily K m (n + 1)) f)
            ((p3PositiveNativeCechCosimplicial K m).δ i x))) :=
      congrArg (p3PositiveNativeChartToLaurent K m (n + 1) f)
        (p3PositiveNativeCechTermAddEquivSections_apply K m (n + 1)
          ((p3PositiveNativeCechCosimplicial K m).δ i x) f)
    _ = p3PositiveNativeChartToLaurent K m (n + 1) f
        ((p3PositiveNativeCechComponentIsoBasic K m (n + 1) f).hom
          (P.map ((E.map (SimplexCategory.δ i).op).φ f).op s)) :=
      congrArg (fun z : p3PositiveNativeCechTermFamily K m (n + 1) f =>
        p3PositiveNativeChartToLaurent K m (n + 1) f
          ((p3PositiveNativeCechComponentIsoBasic K m (n + 1) f).hom z)) hπ'
    _ = p3PositiveNativeChartToLaurent K m (n + 1) f
        (P.map (homOfLE hST).op
          ((p3PositiveNativeCechComponentIsoBasic K m n (deleteTuple i f)).hom s)) :=
      congrArg (p3PositiveNativeChartToLaurent K m (n + 1) f) hbasic'
    _ = p3PositiveNativeChartToLaurent K m n (deleteTuple i f)
        ((p3PositiveNativeCechComponentIsoBasic K m n (deleteTuple i f)).hom s) :=
      p3PositiveNativeChartToLaurent_restrict_face K m n i f
        ((p3PositiveNativeCechComponentIsoBasic K m n (deleteTuple i f)).hom s)
    _ = _ := congrArg (p3PositiveNativeChartToLaurent K m n (deleteTuple i f))
      (p3PositiveNativeCechTermAddEquivSections_apply K m n x (deleteTuple i f)).symm

private theorem p3PositiveNativeCechComplex_d_succ (m n : ℕ) :
    (p3PositiveNativeCechComplex K m).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (p3PositiveNativeCechCosimplicial K m) n := by
  simp [p3PositiveNativeCechComplex, CategoryTheory.cechComplexFunctor,
    FormalCoproduct.cochainComplexFunctor, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, p3PositiveNativeCechCosimplicial]
  congr

/-- Differential compatibility holds for the actual native canonical
complex and map in every degree, with its actual alternating signs. -/
theorem p3PositiveNativeCechTermToLaurent_d
    (m n : ℕ) (x : (p3PositiveNativeCechComplex K m).X n) :
    p3PositiveNativeCechTermToLaurent K m (n + 1)
        ((p3PositiveNativeCechComplex K m).d n (n + 1) x) =
      fun f => ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        p3PositiveNativeCechTermToLaurent K m n x (deleteTuple i f) := by
  funext f
  rw [p3PositiveNativeCechComplex_d_succ, AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  calc
    _ = p3PositiveNativeCechTermToLaurent K m (n + 1)
        (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          ((p3PositiveNativeCechCosimplicial K m).δ i x)) f := by
      exact congrArg
        (fun q : (p3PositiveNativeCechComplex K m).X (n + 1) =>
          p3PositiveNativeCechTermToLaurent K m (n + 1) q f)
        (addCommGrp_finset_sum_zsmul_apply Finset.univ
          (fun i : Fin (n + 2) => (-1 : ℤ) ^ (i : ℕ))
          (fun i => (p3PositiveNativeCechCosimplicial K m).δ i) x)
    _ = (∑ i : Fin (n + 2),
        p3PositiveNativeCechTermToLaurent K m (n + 1)
          (((-1 : ℤ) ^ (i : ℕ)) •
            ((p3PositiveNativeCechCosimplicial K m).δ i x))) f := by
      exact congrFun (map_sum
        (p3PositiveNativeCechTermToLaurent K m (n + 1))
        (fun i : Fin (n + 2) => ((-1 : ℤ) ^ (i : ℕ)) •
          ((p3PositiveNativeCechCosimplicial K m).δ i x)) Finset.univ) f
    _ = _ := by
      rw [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      let v : (p3PositiveNativeCechComplex K m).X (n + 1) :=
        (p3PositiveNativeCechCosimplicial K m).δ i x
      change p3PositiveNativeCechTermToLaurent K m (n + 1)
        (((-1 : ℤ) ^ (i : ℕ)) • v) f = _
      have hz := map_zsmul (p3PositiveNativeCechTermToLaurent K m (n + 1))
        ((-1 : ℤ) ^ (i : ℕ)) v
      calc
        _ = (((-1 : ℤ) ^ (i : ℕ)) •
            p3PositiveNativeCechTermToLaurent K m (n + 1) v) f := congrFun hz f
        _ = ((-1 : ℤ) ^ (i : ℕ)) •
            p3PositiveNativeCechTermToLaurent K m (n + 1) v f := rfl
        _ = _ := congrArg (((-1 : ℤ) ^ (i : ℕ)) • ·)
          (p3PositiveNativeCechTermToLaurent_coface K m n i x f)

/-- Degree zero compatibility in the literal Laurent tuple notation. -/
theorem p3PositiveNativeCechTermToLaurent_d_zero
    (m : ℕ) (x : (p3PositiveNativeCechComplex K m).X 0) :
    p3PositiveNativeCechTermToLaurent K m 1 ((p3PositiveNativeCechComplex K m).d 0 1 x) =
      tupleD0 (p3PositiveNativeCechTermToLaurent K m 0 x) := by
  rw [p3PositiveNativeCechTermToLaurent_d]
  funext f
  simp [Fin.sum_univ_two, tupleD0, sub_eq_add_neg]

/-- Degree one compatibility in the literal Laurent tuple notation. -/
theorem p3PositiveNativeCechTermToLaurent_d_one
    (m : ℕ) (x : (p3PositiveNativeCechComplex K m).X 1) :
    p3PositiveNativeCechTermToLaurent K m 2 ((p3PositiveNativeCechComplex K m).d 1 2 x) =
      tupleD1 (p3PositiveNativeCechTermToLaurent K m 1 x) := by
  rw [p3PositiveNativeCechTermToLaurent_d]
  funext f
  simp [Fin.sum_univ_three, tupleD1, sub_eq_add_neg]

/-- Degree two compatibility in the literal Laurent tuple notation. -/
theorem p3PositiveNativeCechTermToLaurent_d_two
    (m : ℕ) (x : (p3PositiveNativeCechComplex K m).X 2) :
    p3PositiveNativeCechTermToLaurent K m 3 ((p3PositiveNativeCechComplex K m).d 2 3 x) =
      tupleD2 (p3PositiveNativeCechTermToLaurent K m 2 x) := by
  rw [p3PositiveNativeCechTermToLaurent_d]
  funext f
  simp [Fin.sum_univ_four, tupleD2, sub_eq_add_neg]
  norm_num

/-- Degree three compatibility in the literal Laurent tuple notation. -/
theorem p3PositiveNativeCechTermToLaurent_d_three
    (m : ℕ) (x : (p3PositiveNativeCechComplex K m).X 3) :
    p3PositiveNativeCechTermToLaurent K m 4
        ((p3PositiveNativeCechComplex K m).d 3 4 x) =
      tupleD3 (p3PositiveNativeCechTermToLaurent K m 3 x) := by
  rw [p3PositiveNativeCechTermToLaurent_d K m 3 x]
  funext f
  have h0 : deleteTuple (0 : Fin 5) f = ![f 1, f 2, f 3, f 4] := by
    funext i
    fin_cases i <;> rfl
  have h1 : deleteTuple (1 : Fin 5) f = ![f 0, f 2, f 3, f 4] := by
    funext i
    fin_cases i <;> rfl
  have h2 : deleteTuple (2 : Fin 5) f = ![f 0, f 1, f 3, f 4] := by
    funext i
    fin_cases i <;> rfl
  have h3 : deleteTuple (3 : Fin 5) f = ![f 0, f 1, f 2, f 4] := by
    funext i
    fin_cases i <;> rfl
  have h4 : deleteTuple (4 : Fin 5) f = ![f 0, f 1, f 2, f 3] := by
    funext i
    fin_cases i <;> rfl
  simp [Fin.sum_univ_succ, tupleD3, sub_eq_add_neg, h0, h1, h2, h3, h4]
  norm_num
  simp only [add_assoc]

end PfaffianDescent.ProjectiveNegativeTwist
