import PfaffianDescent.CorayClosedSupportCechHomExact
import PfaffianDescent.FormalCoproductCechDifferential

/-! SOURCE ONLY / UNVERIFIED. A direct comparison with mathlib's actual
`cechComplexFunctor` for the same universe-sized open family. Both the Hom
complex and the additive categorical Čech complex become exact in degree
one from the actual closed-support contraction. No new acyclicity input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators
universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) {ι : Type u}

/-- The existing categorical Čech cochain complex of the actual module
presheaf, without replacing its coefficient sheaf or its chosen products. -/
def schemeModuleCategoricalCechComplex (V : ι → X.Opens) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  (CategoryTheory.cechComplexFunctor V).obj M.val.presheaf

abbrev schemeModuleCategoricalCechTermFamily (V : ι → X.Opens) (n : ℕ)
    (f : Fin (n + 1) → ι) : AddCommGrpCat.{u} :=
  M.val.presheaf.obj (op (∏ᶜ fun a : Fin (n + 1) => V (f a)))

def schemeModuleCategoricalCechTermAddEquivPi (V : ι → X.Opens) (n : ℕ) :
    (schemeModuleCategoricalCechComplex M V).X n ≃+
      (∀ f : Fin (n + 1) → ι,
        M.val.obj (op (∏ᶜ fun a : Fin (n + 1) => V (f a)))) :=
  (ProjectiveNegativeTwist.addCommGrpIsoAddEquiv
    (eqToIso (show (schemeModuleCategoricalCechComplex M V).X n =
      ∏ᶜ schemeModuleCategoricalCechTermFamily M V n from rfl))).trans
    (ProjectiveNegativeTwist.addCommGrpProductAddEquivPi
      (schemeModuleCategoricalCechTermFamily M V n))

theorem schemeModuleCategoricalCechTermAddEquivPi_apply (V : ι → X.Opens) (n : ℕ)
    (z : (schemeModuleCategoricalCechComplex M V).X n) (f : Fin (n + 1) → ι) :
    schemeModuleCategoricalCechTermAddEquivPi M V n z f =
      (Pi.π (schemeModuleCategoricalCechTermFamily M V n) f) z := by
  exact ProjectiveNegativeTwist.addCommGrpProductAddEquivPi_apply
    (schemeModuleCategoricalCechTermFamily M V n) z f

def schemeModuleCechHomAddEquivRaw (V : ι → X.Opens) (n : ℕ) :
    ((sectionRepresenterCechChain X.ringCatSheaf V).X n ⟶ M) ≃+
      (schemeModuleCategoricalCechComplex M V).X n :=
  (sectionRepresenterCechHomAddEquivPi X.ringCatSheaf V M n).trans
    (schemeModuleCategoricalCechTermAddEquivPi M V n).symm

theorem schemeModuleCechHomAddEquivRaw_apply (V : ι → X.Opens) (n : ℕ)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X n ⟶ M)
    (f : Fin (n + 1) → ι) :
    schemeModuleCategoricalCechTermAddEquivPi M V n
        (schemeModuleCechHomAddEquivRaw M V n h) f =
      sectionRepresenterCechHomEquivPi X.ringCatSheaf V M n h f := by
  change schemeModuleCategoricalCechTermAddEquivPi M V n
      ((schemeModuleCategoricalCechTermAddEquivPi M V n).symm
        (sectionRepresenterCechHomAddEquivPi X.ringCatSheaf V M n h)) f = _
  rw [AddEquiv.apply_symm_apply] <;> rfl

private theorem schemeModuleCategoricalCech_d_succ (V : ι → X.Opens) (n : ℕ) :
    (schemeModuleCategoricalCechComplex M V).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (formalCoproductCechCosimplicial V M.val.presheaf) n := by
  simp [schemeModuleCategoricalCechComplex, CategoryTheory.cechComplexFunctor,
    FormalCoproduct.cochainComplexFunctor,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, formalCoproductCechCosimplicial]

private theorem schemeModuleCechHomRaw_face_component (V : ι → X.Opens) (n : ℕ)
    (a : Fin (n + 2)) (f : Fin (n + 2) → ι)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X n ⟶ M) :
    let E := (FormalCoproduct.mk _ V).cech
    M.val.map ((E.map (SimplexCategory.δ a).op).φ f).op
        (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M n h
          ((E.map (SimplexCategory.δ a).op).f f)) =
      (Pi.π (schemeModuleCategoricalCechTermFamily M V n) (cechDeleteTuple a f) ≫
        M.val.presheaf.map ((E.map (SimplexCategory.δ a).op).φ f).op)
        (schemeModuleCechHomAddEquivRaw M V n h) := by
  dsimp only
  simp only [ConcreteCategory.comp_apply]
  rw [← schemeModuleCategoricalCechTermAddEquivPi_apply,
    schemeModuleCechHomAddEquivRaw_apply] <;> rfl

/-- The direct Hom-to-raw comparison commutes with the actual categorical
differential in every degree; it has no face-compatibility premise. -/
theorem schemeModuleCechHomAddEquivRaw_d (V : ι → X.Opens) (n : ℕ)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X n ⟶ M) :
    schemeModuleCechHomAddEquivRaw M V (n + 1)
        ((sectionRepresenterCechChain X.ringCatSheaf V).d (n + 1) n ≫ h) =
      (schemeModuleCategoricalCechComplex M V).d n (n + 1)
        (schemeModuleCechHomAddEquivRaw M V n h) := by
  apply (schemeModuleCategoricalCechTermAddEquivPi M V (n + 1)).injective
  funext f
  rw [schemeModuleCechHomAddEquivRaw_apply,
    schemeModuleCategoricalCechTermAddEquivPi_apply, schemeModuleCategoricalCech_d_succ]
  have hleft := sectionRepresenterCechHomEquivPi_d X.ringCatSheaf V M n h f
  rw [hleft]
  have hpi := ConcreteCategory.congr_hom
    (formalCoproductCech_objD_comp_π V M.val.presheaf n f)
    (schemeModuleCechHomAddEquivRaw M V n h)
  simp only [ConcreteCategory.comp_apply] at hpi
  refine Eq.trans ?_ hpi.symm
  rw [ProjectiveNegativeTwist.addCommGrp_finset_sum_zsmul_apply]
  apply Finset.sum_congr rfl
  intro a ha
  apply congrArg (((-1 : ℤ) ^ (a : ℕ)) • ·)
  exact schemeModuleCechHomRaw_face_component M V n a f h

def schemeModuleRawCechZeroAddEquiv (V : ι → X.Opens) :
    (schemeModuleCategoricalCechComplex M V).X 0 ≃+
      SchemeModuleCechZeroCoefficients pi M V :=
  (schemeModuleCechHomAddEquivRaw M V 0).symm.trans
    (schemeModuleCechHomZeroAddEquiv pi M V)

def schemeModuleRawCechOneAddEquiv (V : ι → X.Opens) :
    (schemeModuleCategoricalCechComplex M V).X 1 ≃+
      SchemeModuleCechOneCoefficients pi M V :=
  (schemeModuleCechHomAddEquivRaw M V 1).symm.trans
    (schemeModuleCechHomOneAddEquiv pi M V)

def schemeModuleRawCechTwoAddEquiv (V : ι → X.Opens) :
    (schemeModuleCategoricalCechComplex M V).X 2 ≃+
      SchemeModuleCechTwoCoefficients pi M V :=
  (schemeModuleCechHomAddEquivRaw M V 2).symm.trans
    (schemeModuleCechHomTwoAddEquiv pi M V)

theorem schemeModuleRawCechZeroAddEquiv_d (V : ι → X.Opens)
    (z : (schemeModuleCategoricalCechComplex M V).X 0) :
    schemeModuleRawCechOneAddEquiv pi M V
        ((schemeModuleCategoricalCechComplex M V).d 0 1 z) =
      schemeModuleCechZeroDifferential pi M V
        (schemeModuleRawCechZeroAddEquiv pi M V z) := by
  obtain ⟨h, rfl⟩ := (schemeModuleCechHomAddEquivRaw M V 0).surjective z
  rw [← schemeModuleCechHomAddEquivRaw_d]
  change schemeModuleCechHomOneAddEquiv pi M V
      ((schemeModuleCechHomAddEquivRaw M V 1).symm
        (schemeModuleCechHomAddEquivRaw M V 1
          ((sectionRepresenterCechChain X.ringCatSheaf V).d 1 0 ≫ h))) =
    schemeModuleCechZeroDifferential pi M V
      (schemeModuleCechHomZeroAddEquiv pi M V
        ((schemeModuleCechHomAddEquivRaw M V 0).symm
          (schemeModuleCechHomAddEquivRaw M V 0 h)))
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  exact schemeModuleCechHomZeroAddEquiv_d pi M V h

theorem schemeModuleRawCechOneAddEquiv_d (V : ι → X.Opens)
    (z : (schemeModuleCategoricalCechComplex M V).X 1) :
    schemeModuleRawCechTwoAddEquiv pi M V
        ((schemeModuleCategoricalCechComplex M V).d 1 2 z) =
      schemeModuleCechOneDifferential pi M V
        (schemeModuleRawCechOneAddEquiv pi M V z) := by
  obtain ⟨h, rfl⟩ := (schemeModuleCechHomAddEquivRaw M V 1).surjective z
  rw [← schemeModuleCechHomAddEquivRaw_d]
  change schemeModuleCechHomTwoAddEquiv pi M V
      ((schemeModuleCechHomAddEquivRaw M V 2).symm
        (schemeModuleCechHomAddEquivRaw M V 2
          ((sectionRepresenterCechChain X.ringCatSheaf V).d 2 1 ≫ h))) =
    schemeModuleCechOneDifferential pi M V
      (schemeModuleCechHomOneAddEquiv pi M V
        ((schemeModuleCechHomAddEquivRaw M V 1).symm
          (schemeModuleCechHomAddEquivRaw M V 1 h)))
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  exact schemeModuleCechHomOneAddEquiv_d pi M V h

include pi in
/-- Degree-one exactness for the actual additive categorical Čech complex.
Only genuine support containment is used, and the boundary is supplied by
the actual section contraction through the proved comparisons. -/
theorem schemeModule_augmentedRawCech_exact_one_of_closedSupport_subset
    (U : X.Opens) (V : ι → X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U) :
    Function.Exact
      ((schemeModuleCategoricalCechComplex M (supportAugmentedOpenFamily U V)).d 0 1)
      ((schemeModuleCategoricalCechComplex M (supportAugmentedOpenFamily U V)).d 1 2) := by
  let A := supportAugmentedOpenFamily U V
  intro z
  constructor
  · intro hz
    let h := (schemeModuleCechHomAddEquivRaw M A 1).symm z
    have hc : (sectionRepresenterCechChain X.ringCatSheaf A).d 2 1 ≫ h = 0 := by
      apply (schemeModuleCechHomAddEquivRaw M A 2).injective
      rw [schemeModuleCechHomAddEquivRaw_d, map_zero]
      change (schemeModuleCategoricalCechComplex M A).d 1 2
          ((schemeModuleCechHomAddEquivRaw M A 1)
            ((schemeModuleCechHomAddEquivRaw M A 1).symm z)) = 0
      rw [AddEquiv.apply_symm_apply]
      exact hz
    obtain ⟨a, ha⟩ :=
      (schemeModule_augmentedCechHom_exact_one_of_closedSupport_subset
        pi M U V C hC hsupport hCU h).mp hc
    refine ⟨schemeModuleCechHomAddEquivRaw M A 0 a, ?_⟩
    exact (schemeModuleCechHomAddEquivRaw_d M A 0 a).symm.trans
      ((congrArg (schemeModuleCechHomAddEquivRaw M A 1) ha).trans
        ((schemeModuleCechHomAddEquivRaw M A 1).apply_symm_apply z))
  · rintro ⟨s, rfl⟩
    exact ConcreteCategory.congr_hom
      ((schemeModuleCategoricalCechComplex M A).d_comp_d 0 1 2) s

end PfaffianDescent.Coray
