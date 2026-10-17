import PfaffianDescent.SectionRepresenterCechHomDifferential
import PfaffianDescent.VoisinSectionRepresenterCech
import PfaffianDescent.VoisinTwistCechLaurentDifferential

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open scoped BigOperators
universe u
namespace PfaffianDescent.ProjectiveNegativeTwist

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

lemma p3SectionRepresenterCechChain_eq :
    p3SectionRepresenterCechChain K =
      sectionRepresenterCechChain (Proj PS).ringCatSheaf
        (fun i : ULift.{u} (Fin 4) => p3StandardOpen (K := K) i.down) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma p3SectionRepresenterCechHomEquiv_apply
    (m n : ℕ)
    (h : (p3SectionRepresenterCechChain K).X n ⟶ sheafOfModules PS m)
    (f : Fin (n + 1) → Fin 4) :
    p3NegativeTwistCechTermEquivPi K m n
        (p3SectionRepresenterCechHomEquiv K m n h) f =
      sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
        (fun i : ULift.{u} (Fin 4) => p3StandardOpen (K := K) i.down)
        (sheafOfModules PS m) n h (fun j => ULift.up (f j)) := by
  dsimp [p3NegativeTwistCechTermEquivPi,
    p3SectionRepresenterCechHomEquiv]
  rw [AddEquiv.apply_symm_apply]
  let x := fun g : Fin (n + 1) → Fin 4 =>
    sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
      (fun i : ULift.{u} (Fin 4) => p3StandardOpen (K := K) i.down)
      (sheafOfModules PS m) n h (fun j => ULift.up (g j))
  change (addCommGrpProductAddEquivPi (p3CechTermFamily K m n))
      ((addCommGrpProductAddEquivPi (p3CechTermFamily K m n)).symm x) f = x f
  exact congrFun
    ((addCommGrpProductAddEquivPi (p3CechTermFamily K m n)).apply_symm_apply x) f

set_option backward.isDefEq.respectTransparency false in
lemma p3NegativeTwistCechTermEquivPi_apply
    (m n : ℕ) (x : (p3NegativeTwistCechComplex (K := K) m).X n)
    (f : Fin (n + 1) → Fin 4) :
    p3NegativeTwistCechTermEquivPi K m n x f =
      (Pi.π (p3CechTermFamily K m n) f) x := by
  rfl

lemma p3Cech_face_index_ulift
    (n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4) :
    let EU := (FormalCoproduct.mk _
      (fun j : ULift.{u} (Fin 4) => p3StandardOpen (K := K) j.down)).cech
    (EU.map (SimplexCategory.δ i).op).f (fun j => ULift.up (f j)) =
      fun j => ULift.up (LaurentLocalization.deleteTuple i f j) := by
  rfl

lemma p3Cech_face_openMap_ulift
    (n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4) :
    let EU := (FormalCoproduct.mk _
      (fun j : ULift.{u} (Fin 4) => p3StandardOpen (K := K) j.down)).cech
    let E := (FormalCoproduct.mk _ (p3StandardOpen (K := K))).cech
    (EU.map (SimplexCategory.δ i).op).φ (fun j => ULift.up (f j)) =
      (E.map (SimplexCategory.δ i).op).φ f := by
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma p3SectionRepresenterCechHomEquiv_face_component
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4)
    (h : (p3SectionRepresenterCechChain K).X n ⟶ sheafOfModules PS m) :
    let EU := (FormalCoproduct.mk _
      (fun j : ULift.{u} (Fin 4) => p3StandardOpen (K := K) j.down)).cech
    let E := (FormalCoproduct.mk _ (p3StandardOpen (K := K))).cech
    let P := (modulePresheaf PS m).presheaf
    (sheafOfModules PS m).val.map
        ((EU.map (SimplexCategory.δ i).op).φ
          (fun j => ULift.up (f j))).op
      (sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
        (fun j : ULift.{u} (Fin 4) => p3StandardOpen (K := K) j.down)
        (sheafOfModules PS m) n h
        ((EU.map (SimplexCategory.δ i).op).f
          (fun j => ULift.up (f j)))) =
      (Pi.π (p3CechTermFamily K m n)
          (LaurentLocalization.deleteTuple i f) ≫
        P.map ((E.map (SimplexCategory.δ i).op).φ f).op)
        (p3SectionRepresenterCechHomEquiv K m n h) := by
  dsimp only
  simp only [ConcreteCategory.comp_apply]
  have hcoord₀ :=
    (p3SectionRepresenterCechHomEquiv_apply K m n h
      (LaurentLocalization.deleteTuple i f)).symm
  have hcoord :
      sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
        (fun j : ULift.{u} (Fin 4) => p3StandardOpen (K := K) j.down)
        (sheafOfModules PS m) n h
        (((FormalCoproduct.mk _
          (fun j : ULift.{u} (Fin 4) =>
            p3StandardOpen (K := K) j.down)).cech.map
              (SimplexCategory.δ i).op).f
          (fun j => ULift.up (f j))) =
        (Pi.π (p3CechTermFamily K m n)
          (LaurentLocalization.deleteTuple i f))
          (p3SectionRepresenterCechHomEquiv K m n h) := by
    let g := ((FormalCoproduct.mk _
      (fun j : ULift.{u} (Fin 4) =>
        p3StandardOpen (K := K) j.down)).cech.map
          (SimplexCategory.δ i).op).f (fun j => ULift.up (f j))
    change sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
      (fun j : ULift.{u} (Fin 4) => p3StandardOpen (K := K) j.down)
      (sheafOfModules PS m) n h g = _
    have hg : g = fun j => ULift.up (LaurentLocalization.deleteTuple i f j) := by
      rfl
    subst g
    rw [← p3NegativeTwistCechTermEquivPi_apply]
    exact hcoord₀
  rw [hcoord]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma p3SectionRepresenterCechHomEquiv_d
    (m n : ℕ)
    (h : (p3SectionRepresenterCechChain K).X n ⟶ sheafOfModules PS m) :
    p3SectionRepresenterCechHomEquiv K m (n + 1)
        ((p3SectionRepresenterCechChain K).d (n + 1) n ≫ h) =
      (p3NegativeTwistCechComplex (K := K) m).d n (n + 1)
        (p3SectionRepresenterCechHomEquiv K m n h) := by
  apply (p3NegativeTwistCechTermEquivPi K m (n + 1)).injective
  funext f
  rw [p3SectionRepresenterCechHomEquiv_apply,
    p3NegativeTwistCechTermEquivPi_apply,
    p3NegativeTwistCechComplex_d_succ]
  have hleft := sectionRepresenterCechHomEquivPi_d
    (Proj PS).ringCatSheaf
    (fun i : ULift.{u} (Fin 4) => p3StandardOpen (K := K) i.down)
    (sheafOfModules PS m) n h (fun j => ULift.up (f j))
  have hd : (p3SectionRepresenterCechChain K).d (n + 1) n =
      (sectionRepresenterCechChain (Proj PS).ringCatSheaf
        (fun i : ULift.{u} (Fin 4) => p3StandardOpen (K := K) i.down)).d
          (n + 1) n := by
    rfl
  rw [hd, hleft]
  have hπ := ConcreteCategory.congr_hom
    (p3Cech_objD_comp_π K m n f)
    (p3SectionRepresenterCechHomEquiv K m n h)
  simp only [ConcreteCategory.comp_apply] at hπ
  let E := (FormalCoproduct.mk _ (p3StandardOpen (K := K))).cech
  let P := (modulePresheaf PS m).presheaf
  have hπ' :
      (Pi.π (p3CechTermFamily K m (n + 1)) f)
          (AlgebraicTopology.AlternatingCofaceMapComplex.objD
            (p3CechCosimplicial K m) n
            (p3SectionRepresenterCechHomEquiv K m n h)) =
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (Pi.π (p3CechTermFamily K m n) (LaurentLocalization.deleteTuple i f) ≫
            P.map ((E.map (SimplexCategory.δ i).op).φ f).op))
          (p3SectionRepresenterCechHomEquiv K m n h) := by
    exact hπ
  refine Eq.trans ?_ hπ'.symm
  rw [addCommGrp_finset_sum_zsmul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (((-1 : ℤ) ^ (i : ℕ)) • ·)
    (p3SectionRepresenterCechHomEquiv_face_component K m n i f h)

end PfaffianDescent.ProjectiveNegativeTwist
