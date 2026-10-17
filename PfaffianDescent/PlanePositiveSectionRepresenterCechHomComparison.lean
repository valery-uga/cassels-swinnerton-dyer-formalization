import PfaffianDescent.PlaneNativeCechExactness
import PfaffianDescent.VoisinSectionRepresenterCechDifferential

/-! The OWN positive-twist Čech complex versus the OWN section-representer
chain on the same standard coordinate cover. All comparison maps and
compatibilities are constructed here; none is a premise.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open scoped BigOperators
universe u
namespace PfaffianDescent.ProjectivePlaneNative
open ProjectiveNegativeTwist PlaneLaurentLocalization
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K

private def positiveHomComparisonIndexFunEquiv (n : ℕ) :
    (Fin (n + 1) → ULift.{u} (Fin 3)) ≃ (Fin (n + 1) → Fin 3) where
  toFun f i := (f i).down
  invFun f i := ⟨f i⟩
  left_inv f := by
    funext i
    cases h : f i
    simp [h]
  right_inv f := by funext i; rfl

private theorem positiveHomComparisonComplex_X (m n : ℕ) :
    (p2PositiveNativeCechComplex K m).X n =
      ∏ᶜ fun f : Fin (n + 1) → Fin 3 =>
        (positiveSheafOfModules PS m).presheaf.obj
          (op (∏ᶜ fun a : Fin (n + 1) => p2StandardOpen (K := K) (f a))) := rfl

private noncomputable def positiveHomComparisonTermEquivPi (m n : ℕ) :
    (p2PositiveNativeCechComplex K m).X n ≃
      (∀ f : Fin (n + 1) → Fin 3, p2PositiveNativeCechTermFamily K m n f) :=
  ((addCommGrpIsoAddEquiv
      (eqToIso (positiveHomComparisonComplex_X K m n))).trans
    (addCommGrpProductAddEquivPi (p2PositiveNativeCechTermFamily K m n))).toEquiv

noncomputable def p2PositiveSectionRepresenterCechHomEquiv (m n : ℕ) :
    ((p2SectionRepresenterCechChain K).X n ⟶ positiveSheafOfModules PS m) ≃
      (p2PositiveNativeCechComplex K m).X n :=
  ((sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
    (fun i : ULift.{u} (Fin 3) => p2StandardOpen (K := K) i.down)
    (positiveSheafOfModules PS m) n).trans
      (Equiv.piCongrLeft (fun f : Fin (n + 1) → Fin 3 =>
        p2PositiveNativeCechTermFamily K m n f) (positiveHomComparisonIndexFunEquiv n))).trans
      (positiveHomComparisonTermEquivPi K m n).symm

/-- Projection of a Cech coface onto one ordered intersection. -/
private lemma positiveHomComparison_coface_comp_projection (m n : ℕ) (i : Fin (n + 2))
    (f : Fin (n + 2) → Fin 3) :
    let E := (CategoryTheory.Limits.FormalCoproduct.mk _
      (p2StandardOpen (K := K))).cech
    let P := (positiveSheafOfModules PS m).presheaf
    (p2PositiveNativeCechCosimplicial K m).δ i ≫
        Pi.π (fun j : (E.obj (Opposite.op (SimplexCategory.mk (n + 1)))).I =>
          P.obj (Opposite.op ((E.obj (Opposite.op (SimplexCategory.mk (n + 1)))).obj j))) f =
      Pi.π (fun j : (E.obj (Opposite.op (SimplexCategory.mk n))).I =>
          P.obj (Opposite.op ((E.obj (Opposite.op (SimplexCategory.mk n))).obj j)))
        (deleteTuple i f) ≫
      P.map ((E.map (SimplexCategory.δ i).op).φ f).op := by
  dsimp only
  simp only [p2PositiveNativeCechCosimplicial, CosimplicialObject.δ,
    CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  exact Pi.lift_π _ f

set_option backward.isDefEq.respectTransparency false in
/-- Component formula for the differential of the raw Cech complex in every
nonnegative degree. -/
private lemma positiveHomComparison_objD_comp_projection (m n : ℕ) (f : Fin (n + 2) → Fin 3) :
    let E := (CategoryTheory.Limits.FormalCoproduct.mk _
      (p2StandardOpen (K := K))).cech
    let P := (positiveSheafOfModules PS m).presheaf
    AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (p2PositiveNativeCechCosimplicial K m) n ≫
        Pi.π (fun j : (E.obj (Opposite.op (SimplexCategory.mk (n + 1)))).I =>
          P.obj (Opposite.op ((E.obj
            (Opposite.op (SimplexCategory.mk (n + 1)))).obj j))) f =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (Pi.π (fun j : (E.obj (Opposite.op (SimplexCategory.mk n))).I =>
            P.obj (Opposite.op ((E.obj (Opposite.op (SimplexCategory.mk n))).obj j)))
          (deleteTuple i f) ≫
        P.map ((E.map (SimplexCategory.δ i).op).φ f).op) := by
  dsimp only
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Preadditive.zsmul_comp]
  exact congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
    (positiveHomComparison_coface_comp_projection K m n i f)

private lemma positiveHomComparisonComplex_d_succ (m n : ℕ) :
    (p2PositiveNativeCechComplex K m).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (p2PositiveNativeCechCosimplicial K m) n := by
  simp [p2PositiveNativeCechComplex, CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    p2PositiveNativeCechCosimplicial]
  congr

set_option backward.isDefEq.respectTransparency false in
private lemma p2PositiveSectionRepresenterCechHomEquiv_apply
    (m n : ℕ)
    (h : (p2SectionRepresenterCechChain K).X n ⟶ positiveSheafOfModules PS m)
    (f : Fin (n + 1) → Fin 3) :
    positiveHomComparisonTermEquivPi K m n
        (p2PositiveSectionRepresenterCechHomEquiv K m n h) f =
      sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
        (fun i : ULift.{u} (Fin 3) => p2StandardOpen (K := K) i.down)
        (positiveSheafOfModules PS m) n h (fun j => ULift.up (f j)) := by
  dsimp [positiveHomComparisonTermEquivPi,
    p2PositiveSectionRepresenterCechHomEquiv]
  rw [AddEquiv.apply_symm_apply]
  let x := fun g : Fin (n + 1) → Fin 3 =>
    sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
      (fun i : ULift.{u} (Fin 3) => p2StandardOpen (K := K) i.down)
      (positiveSheafOfModules PS m) n h (fun j => ULift.up (g j))
  change (addCommGrpProductAddEquivPi (p2PositiveNativeCechTermFamily K m n))
      ((addCommGrpProductAddEquivPi (p2PositiveNativeCechTermFamily K m n)).symm x) f = x f
  exact congrFun
    ((addCommGrpProductAddEquivPi (p2PositiveNativeCechTermFamily K m n)).apply_symm_apply x) f

set_option backward.isDefEq.respectTransparency false in
private lemma positiveHomComparisonTermEquivPi_apply
    (m n : ℕ) (x : (p2PositiveNativeCechComplex K m).X n)
    (f : Fin (n + 1) → Fin 3) :
    positiveHomComparisonTermEquivPi K m n x f =
      (Pi.π (p2PositiveNativeCechTermFamily K m n) f) x := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma p2PositiveSectionRepresenterCechHomEquiv_face_component
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3)
    (h : (p2SectionRepresenterCechChain K).X n ⟶ positiveSheafOfModules PS m) :
    let EU := (FormalCoproduct.mk _
      (fun j : ULift.{u} (Fin 3) => p2StandardOpen (K := K) j.down)).cech
    let E := (FormalCoproduct.mk _ (p2StandardOpen (K := K))).cech
    let P := (positiveSheafOfModules PS m).presheaf
    (positiveSheafOfModules PS m).val.map
        ((EU.map (SimplexCategory.δ i).op).φ
          (fun j => ULift.up (f j))).op
      (sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
        (fun j : ULift.{u} (Fin 3) => p2StandardOpen (K := K) j.down)
        (positiveSheafOfModules PS m) n h
        ((EU.map (SimplexCategory.δ i).op).f
          (fun j => ULift.up (f j)))) =
      (Pi.π (p2PositiveNativeCechTermFamily K m n)
          (PlaneLaurentLocalization.deleteTuple i f) ≫
        P.map ((E.map (SimplexCategory.δ i).op).φ f).op)
        (p2PositiveSectionRepresenterCechHomEquiv K m n h) := by
  dsimp only
  simp only [ConcreteCategory.comp_apply]
  have hcoord₀ :=
    (p2PositiveSectionRepresenterCechHomEquiv_apply K m n h
      (PlaneLaurentLocalization.deleteTuple i f)).symm
  have hcoord :
      sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
        (fun j : ULift.{u} (Fin 3) => p2StandardOpen (K := K) j.down)
        (positiveSheafOfModules PS m) n h
        (((FormalCoproduct.mk _
          (fun j : ULift.{u} (Fin 3) =>
            p2StandardOpen (K := K) j.down)).cech.map
              (SimplexCategory.δ i).op).f
          (fun j => ULift.up (f j))) =
        (Pi.π (p2PositiveNativeCechTermFamily K m n)
          (PlaneLaurentLocalization.deleteTuple i f))
          (p2PositiveSectionRepresenterCechHomEquiv K m n h) := by
    let g := ((FormalCoproduct.mk _
      (fun j : ULift.{u} (Fin 3) =>
        p2StandardOpen (K := K) j.down)).cech.map
          (SimplexCategory.δ i).op).f (fun j => ULift.up (f j))
    change sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
      (fun j : ULift.{u} (Fin 3) => p2StandardOpen (K := K) j.down)
      (positiveSheafOfModules PS m) n h g = _
    have hg : g = fun j => ULift.up (PlaneLaurentLocalization.deleteTuple i f j) := by
      rfl
    subst g
    rw [← positiveHomComparisonTermEquivPi_apply]
    exact hcoord₀
  rw [hcoord]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma p2PositiveSectionRepresenterCechHomEquiv_d
    (m n : ℕ)
    (h : (p2SectionRepresenterCechChain K).X n ⟶ positiveSheafOfModules PS m) :
    p2PositiveSectionRepresenterCechHomEquiv K m (n + 1)
        ((p2SectionRepresenterCechChain K).d (n + 1) n ≫ h) =
      (p2PositiveNativeCechComplex K m).d n (n + 1)
        (p2PositiveSectionRepresenterCechHomEquiv K m n h) := by
  apply (positiveHomComparisonTermEquivPi K m (n + 1)).injective
  funext f
  rw [p2PositiveSectionRepresenterCechHomEquiv_apply,
    positiveHomComparisonTermEquivPi_apply,
    positiveHomComparisonComplex_d_succ]
  have hleft := sectionRepresenterCechHomEquivPi_d
    (Proj PS).ringCatSheaf
    (fun i : ULift.{u} (Fin 3) => p2StandardOpen (K := K) i.down)
    (positiveSheafOfModules PS m) n h (fun j => ULift.up (f j))
  have hd : (p2SectionRepresenterCechChain K).d (n + 1) n =
      (sectionRepresenterCechChain (Proj PS).ringCatSheaf
        (fun i : ULift.{u} (Fin 3) => p2StandardOpen (K := K) i.down)).d
          (n + 1) n := by
    rfl
  rw [hd, hleft]
  have hπ := ConcreteCategory.congr_hom
    (positiveHomComparison_objD_comp_projection K m n f)
    (p2PositiveSectionRepresenterCechHomEquiv K m n h)
  simp only [ConcreteCategory.comp_apply] at hπ
  let E := (FormalCoproduct.mk _ (p2StandardOpen (K := K))).cech
  let P := (positiveSheafOfModules PS m).presheaf
  have hπ' :
      (Pi.π (p2PositiveNativeCechTermFamily K m (n + 1)) f)
          (AlgebraicTopology.AlternatingCofaceMapComplex.objD
            (p2PositiveNativeCechCosimplicial K m) n
            (p2PositiveSectionRepresenterCechHomEquiv K m n h)) =
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (Pi.π (p2PositiveNativeCechTermFamily K m n) (PlaneLaurentLocalization.deleteTuple i f) ≫
            P.map ((E.map (SimplexCategory.δ i).op).φ f).op))
          (p2PositiveSectionRepresenterCechHomEquiv K m n h) := by
    exact hπ
  refine Eq.trans ?_ hπ'.symm
  rw [addCommGrp_finset_sum_zsmul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (((-1 : ℤ) ^ (i : ℕ)) • ·)
    (p2PositiveSectionRepresenterCechHomEquiv_face_component K m n i f h)

set_option backward.isDefEq.respectTransparency false in
private lemma p2PositiveSectionRepresenterCechHomEquiv_zero (m n : ℕ) :
    p2PositiveSectionRepresenterCechHomEquiv K m n
      (0 : (p2SectionRepresenterCechChain K).X n ⟶ positiveSheafOfModules PS m) = 0 := by
  apply (positiveHomComparisonTermEquivPi K m n).injective
  funext f
  rw [p2PositiveSectionRepresenterCechHomEquiv_apply,
    positiveHomComparisonTermEquivPi_apply]
  change (sectionRepresenterCechHomAddEquivPi (Proj PS).ringCatSheaf
      (fun i : ULift.{u} (Fin 3) => p2StandardOpen (K := K) i.down)
      (positiveSheafOfModules PS m) n) 0 (fun j => ULift.up (f j)) = _
  rw [map_zero]
  change 0 = ((Pi.π (p2PositiveNativeCechTermFamily K m n) f).hom) 0
  rw [map_zero]

/-- Applying `Hom(-, O(m))` to the section-representer Cech chain is exact
in cochain degree one. -/
lemma p2PositiveSectionRepresenterCechHom_exact_one (m : ℕ) :
    Function.Exact
      (fun h : (p2SectionRepresenterCechChain K).X 0 ⟶ positiveSheafOfModules PS m =>
        (p2SectionRepresenterCechChain K).d 1 0 ≫ h)
      (fun h : (p2SectionRepresenterCechChain K).X 1 ⟶ positiveSheafOfModules PS m =>
        (p2SectionRepresenterCechChain K).d 2 1 ≫ h) := by
  intro y
  constructor
  · intro hy
    change (p2SectionRepresenterCechChain K).d 2 1 ≫ y = 0 at hy
    have hy' :
        (p2PositiveNativeCechComplex K m).d 1 2
          (p2PositiveSectionRepresenterCechHomEquiv K m 1 y) = 0 := by
      calc
        _ = p2PositiveSectionRepresenterCechHomEquiv K m 2
            ((p2SectionRepresenterCechChain K).d 2 1 ≫ y) :=
          (p2PositiveSectionRepresenterCechHomEquiv_d K m 1 y).symm
        _ = p2PositiveSectionRepresenterCechHomEquiv K m 2 0 :=
          congrArg (p2PositiveSectionRepresenterCechHomEquiv K m 2) hy
        _ = 0 := p2PositiveSectionRepresenterCechHomEquiv_zero K m 2
    obtain ⟨x, hx⟩ :=
      (p2PositiveNativeCech_exact_one K m
        (p2PositiveSectionRepresenterCechHomEquiv K m 1 y)).mp hy'
    let x' := (p2PositiveSectionRepresenterCechHomEquiv K m 0).symm x
    refine ⟨x', ?_⟩
    apply (p2PositiveSectionRepresenterCechHomEquiv K m 1).injective
    rw [p2PositiveSectionRepresenterCechHomEquiv_d]
    simpa only [x', Equiv.apply_symm_apply] using hx
  · rintro ⟨x, rfl⟩
    change (p2SectionRepresenterCechChain K).d 2 1 ≫
      ((p2SectionRepresenterCechChain K).d 1 0 ≫ x) = 0
    rw [← Category.assoc,
      (p2SectionRepresenterCechChain K).d_comp_d 2 1 0, zero_comp]

/-- Applying `Hom(-, O(m))` to the section-representer Cech chain is exact
in cochain degree two. -/
lemma p2PositiveSectionRepresenterCechHom_exact_two (m : ℕ) :
    Function.Exact
      (fun h : (p2SectionRepresenterCechChain K).X 1 ⟶ positiveSheafOfModules PS m =>
        (p2SectionRepresenterCechChain K).d 2 1 ≫ h)
      (fun h : (p2SectionRepresenterCechChain K).X 2 ⟶ positiveSheafOfModules PS m =>
        (p2SectionRepresenterCechChain K).d 3 2 ≫ h) := by
  intro z
  constructor
  · intro hz
    change (p2SectionRepresenterCechChain K).d 3 2 ≫ z = 0 at hz
    have hz' :
        (p2PositiveNativeCechComplex K m).d 2 3
          (p2PositiveSectionRepresenterCechHomEquiv K m 2 z) = 0 := by
      calc
        _ = p2PositiveSectionRepresenterCechHomEquiv K m 3
            ((p2SectionRepresenterCechChain K).d 3 2 ≫ z) :=
          (p2PositiveSectionRepresenterCechHomEquiv_d K m 2 z).symm
        _ = p2PositiveSectionRepresenterCechHomEquiv K m 3 0 :=
          congrArg (p2PositiveSectionRepresenterCechHomEquiv K m 3) hz
        _ = 0 := p2PositiveSectionRepresenterCechHomEquiv_zero K m 3
    obtain ⟨y, hy⟩ :=
      (p2PositiveNativeCech_exact_two K m
        (p2PositiveSectionRepresenterCechHomEquiv K m 2 z)).mp hz'
    let y' := (p2PositiveSectionRepresenterCechHomEquiv K m 1).symm y
    refine ⟨y', ?_⟩
    apply (p2PositiveSectionRepresenterCechHomEquiv K m 2).injective
    rw [p2PositiveSectionRepresenterCechHomEquiv_d]
    simpa only [y', Equiv.apply_symm_apply] using hy
  · rintro ⟨y, rfl⟩
    change (p2SectionRepresenterCechChain K).d 3 2 ≫
      ((p2SectionRepresenterCechChain K).d 2 1 ≫ y) = 0
    rw [← Category.assoc,
      (p2SectionRepresenterCechChain K).d_comp_d 3 2 1, zero_comp]

end PfaffianDescent.ProjectivePlaneNative
