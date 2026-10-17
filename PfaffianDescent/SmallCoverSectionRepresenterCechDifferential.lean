import PfaffianDescent.FormalCoproductCechDifferential
import PfaffianDescent.SectionRepresenterCechHomDifferential

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open AlgebraicTopology
open scoped BigOperators
namespace PfaffianDescent
universe u
variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {ι : Type}

noncomputable def smallCoverCechComplex (U : ι → C) (M : SheafOfModules.{u} R) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  (CategoryTheory.cechComplexFunctor U).obj M.val.presheaf

noncomputable abbrev smallCoverCechTermFamily (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ) (f : Fin (n+1) → ι) : AddCommGrpCat.{u} :=
  M.val.presheaf.obj (op (∏ᶜ fun a : Fin (n+1) => U (f a)))

noncomputable abbrev smallCoverSectionFamily (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ) (f : Fin (n+1) → ι) : Type u :=
  M.val.obj (op (∏ᶜ fun a : Fin (n+1) => U (f a)))

noncomputable def smallCoverCechTermEquivPi (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ) :
    (smallCoverCechComplex R U M).X n ≃
      (∀ f : Fin (n+1) → ι, smallCoverSectionFamily R U M n f) :=
  ((ProjectiveNegativeTwist.addCommGrpIsoAddEquiv
      (eqToIso (show (smallCoverCechComplex R U M).X n =
        ∏ᶜ fun f : Fin (n+1) → ι => smallCoverCechTermFamily R U M n f from rfl))).trans
    (ProjectiveNegativeTwist.addCommGrpProductAddEquivPi (smallCoverCechTermFamily R U M n))).toEquiv

lemma smallCoverCechTermEquivPi_apply (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ)
    (x : (smallCoverCechComplex R U M).X n) (f : Fin (n+1) → ι) :
    smallCoverCechTermEquivPi R U M n x f =
      (Pi.π (smallCoverCechTermFamily R U M n) f) x := by
  rfl

lemma smallCoverCechTermEquivPi_add (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ)
    (x y : (smallCoverCechComplex R U M).X n) :
    smallCoverCechTermEquivPi R U M n (x + y) =
      smallCoverCechTermEquivPi R U M n x +
        smallCoverCechTermEquivPi R U M n y := by
  unfold smallCoverCechTermEquivPi
  exact map_add
    ((ProjectiveNegativeTwist.addCommGrpIsoAddEquiv
      (eqToIso (show (smallCoverCechComplex R U M).X n =
        ∏ᶜ fun f : Fin (n + 1) → ι =>
          smallCoverCechTermFamily R U M n f from rfl))).trans
      (ProjectiveNegativeTwist.addCommGrpProductAddEquivPi
        (smallCoverCechTermFamily R U M n))) x y

private def smallCoverIndexEquiv (n : ℕ) :
    (Fin (n+1) → ULift.{u} ι) ≃ (Fin (n+1) → ι) where
  toFun f i := (f i).down
  invFun f i := ULift.up (f i)
  left_inv f := by
    funext i
    cases h : f i
    simp [h]
  right_inv f := by funext i; rfl

noncomputable def smallCoverSectionHomEquiv (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ) :
    ((sectionRepresenterCechChain R
      (fun j : ULift.{u} ι => U j.down)).X n ⟶ M) ≃
      (smallCoverCechComplex R U M).X n :=
  (((sectionRepresenterCechHomEquivPi R
      (fun j : ULift.{u} ι => U j.down) M n).trans
    (Equiv.piCongrLeft
      (fun f : Fin (n+1) → ι => smallCoverSectionFamily R U M n f)
      (smallCoverIndexEquiv n))).trans
    (smallCoverCechTermEquivPi R U M n).symm)

lemma smallCoverSectionHomEquiv_apply (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ)
    (h : (sectionRepresenterCechChain R
      (fun j : ULift.{u} ι => U j.down)).X n ⟶ M)
    (f : Fin (n+1) → ι) :
    smallCoverCechTermEquivPi R U M n
      (smallCoverSectionHomEquiv R U M n h) f =
    sectionRepresenterCechHomEquivPi R
      (fun j : ULift.{u} ι => U j.down) M n h
      (fun j => ULift.up (f j)) := by
  dsimp [smallCoverSectionHomEquiv]
  rw [Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma smallCoverSectionHomEquiv_zero (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ) :
    smallCoverSectionHomEquiv R U M n
      (0 : (sectionRepresenterCechChain R
        (fun j : ULift.{u} ι => U j.down)).X n ⟶ M) = 0 := by
  apply (smallCoverCechTermEquivPi R U M n).injective
  funext f
  rw [smallCoverSectionHomEquiv_apply, smallCoverCechTermEquivPi_apply]
  change (sectionRepresenterCechHomAddEquivPi R
      (fun j : ULift.{u} ι => U j.down) M n) 0
        (fun j => ULift.up (f j)) = _
  rw [map_zero]
  change 0 = ((Pi.π (smallCoverCechTermFamily R U M n) f).hom) 0
  rw [map_zero]

set_option backward.isDefEq.respectTransparency false in
lemma smallCoverSectionHomEquiv_add (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ)
    (x y : (sectionRepresenterCechChain R
      (fun j : ULift.{u} ι => U j.down)).X n ⟶ M) :
    smallCoverSectionHomEquiv R U M n (x + y) =
      smallCoverSectionHomEquiv R U M n x +
        smallCoverSectionHomEquiv R U M n y := by
  apply (smallCoverCechTermEquivPi R U M n).injective
  funext f
  calc
    smallCoverCechTermEquivPi R U M n
        (smallCoverSectionHomEquiv R U M n (x + y)) f =
      sectionRepresenterCechHomEquivPi R
        (fun j : ULift.{u} ι => U j.down) M n (x + y)
        (fun j => ULift.up (f j)) :=
      smallCoverSectionHomEquiv_apply R U M n (x + y) f
    _ = sectionRepresenterCechHomEquivPi R
          (fun j : ULift.{u} ι => U j.down) M n x
            (fun j => ULift.up (f j)) +
        sectionRepresenterCechHomEquivPi R
          (fun j : ULift.{u} ι => U j.down) M n y
            (fun j => ULift.up (f j)) := by
      exact congrFun (map_add
        (sectionRepresenterCechHomAddEquivPi R
          (fun j : ULift.{u} ι => U j.down) M n) x y)
        (fun j => ULift.up (f j))
    _ = smallCoverCechTermEquivPi R U M n
          (smallCoverSectionHomEquiv R U M n x) f +
        smallCoverCechTermEquivPi R U M n
          (smallCoverSectionHomEquiv R U M n y) f := by
      rw [smallCoverSectionHomEquiv_apply,
        smallCoverSectionHomEquiv_apply]
    _ = smallCoverCechTermEquivPi R U M n
          (smallCoverSectionHomEquiv R U M n x +
            smallCoverSectionHomEquiv R U M n y) f := by
      exact congrFun (smallCoverCechTermEquivPi_add R U M n
        (smallCoverSectionHomEquiv R U M n x)
        (smallCoverSectionHomEquiv R U M n y)).symm f

lemma smallCoverCechComplex_d_succ (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ) :
    (smallCoverCechComplex R U M).d n (n+1) =
      AlternatingCofaceMapComplex.objD (formalCoproductCechCosimplicial U M.val.presheaf) n := by
  simp [smallCoverCechComplex, CategoryTheory.cechComplexFunctor,
    FormalCoproduct.cochainComplexFunctor,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, formalCoproductCechCosimplicial]
  congr

set_option backward.isDefEq.respectTransparency false in
/-- A component of the small-cover Cech differential, expressed using the
named family of section groups. -/
lemma smallCoverCechComplex_d_succ_comp_π (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ)
    (f : Fin (n + 2) → ι) :
    let E := (FormalCoproduct.mk _ U).cech
    (smallCoverCechComplex R U M).d n (n + 1) ≫
        Pi.π (smallCoverCechTermFamily R U M (n + 1)) f =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (Pi.π (smallCoverCechTermFamily R U M n)
            (cechDeleteTuple i f) ≫
          M.val.presheaf.map ((E.map (SimplexCategory.δ i).op).φ f).op) := by
  dsimp only
  rw [smallCoverCechComplex_d_succ]
  exact formalCoproductCech_objD_comp_π U M.val.presheaf n f

set_option backward.isDefEq.respectTransparency false in
lemma smallCoverSectionHomEquiv_face_component (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ) (i : Fin (n+2))
    (f : Fin (n+2) → ι)
    (h : (sectionRepresenterCechChain R
      (fun j : ULift.{u} ι => U j.down)).X n ⟶ M) :
    let EU := (FormalCoproduct.mk _
      (fun j : ULift.{u} ι => U j.down)).cech
    let E := (FormalCoproduct.mk _ U).cech
    M.val.map ((EU.map (SimplexCategory.δ i).op).φ
        (fun j => ULift.up (f j))).op
      (sectionRepresenterCechHomEquivPi R
        (fun j : ULift.{u} ι => U j.down) M n h
        ((EU.map (SimplexCategory.δ i).op).f
          (fun j => ULift.up (f j)))) =
      (Pi.π (smallCoverCechTermFamily R U M n) (cechDeleteTuple i f) ≫
        M.val.presheaf.map ((E.map (SimplexCategory.δ i).op).φ f).op)
        (smallCoverSectionHomEquiv R U M n h) := by
  dsimp only
  simp only [ConcreteCategory.comp_apply]
  have hcoord₀ :=
    (smallCoverSectionHomEquiv_apply R U M n h (cechDeleteTuple i f)).symm
  have hcoord :
      sectionRepresenterCechHomEquivPi R
        (fun j : ULift.{u} ι => U j.down) M n h
        (((FormalCoproduct.mk _
          (fun j : ULift.{u} ι => U j.down)).cech.map
            (SimplexCategory.δ i).op).f
          (fun j => ULift.up (f j))) =
      (Pi.π (smallCoverCechTermFamily R U M n) (cechDeleteTuple i f))
        (smallCoverSectionHomEquiv R U M n h) := by
    let g := ((FormalCoproduct.mk _
      (fun j : ULift.{u} ι => U j.down)).cech.map
        (SimplexCategory.δ i).op).f (fun j => ULift.up (f j))
    change sectionRepresenterCechHomEquivPi R
      (fun j : ULift.{u} ι => U j.down) M n h g = _
    have hg : g = fun j => ULift.up (cechDeleteTuple i f j) := by rfl
    subst g
    rw [← smallCoverCechTermEquivPi_apply]
    exact hcoord₀
  rw [hcoord]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma smallCoverSectionHomEquiv_d (U : ι → C)
    (M : SheafOfModules.{u} R) (n : ℕ)
    (h : (sectionRepresenterCechChain R
      (fun j : ULift.{u} ι => U j.down)).X n ⟶ M) :
    smallCoverSectionHomEquiv R U M (n+1)
      ((sectionRepresenterCechChain R
        (fun j : ULift.{u} ι => U j.down)).d (n+1) n ≫ h) =
    (smallCoverCechComplex R U M).d n (n+1)
      (smallCoverSectionHomEquiv R U M n h) := by
  apply (smallCoverCechTermEquivPi R U M (n+1)).injective
  funext f
  rw [smallCoverSectionHomEquiv_apply, smallCoverCechTermEquivPi_apply,
    smallCoverCechComplex_d_succ]
  have hleft := sectionRepresenterCechHomEquivPi_d R
    (fun j : ULift.{u} ι => U j.down) M n h
    (fun j => ULift.up (f j))
  rw [hleft]
  have hpi := ConcreteCategory.congr_hom
    (formalCoproductCech_objD_comp_π U M.val.presheaf n f)
    (smallCoverSectionHomEquiv R U M n h)
  simp only [ConcreteCategory.comp_apply] at hpi
  refine Eq.trans ?_ hpi.symm
  rw [ProjectiveNegativeTwist.addCommGrp_finset_sum_zsmul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (((-1 : ℤ)^(i:ℕ)) • ·)
  exact smallCoverSectionHomEquiv_face_component R U M n i f h

end PfaffianDescent

namespace PfaffianDescent

universe u₁

variable {C₁ D₁ : Type u₁} [SmallCategory C₁] [SmallCategory D₁]
variable [HasFiniteProducts C₁] [HasFiniteProducts D₁]
variable {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology D₁}
variable (R₁ : Sheaf J₁ RingCat.{u₁}) (R₂ : Sheaf J₂ RingCat.{u₁})
variable [HasSheafify J₁ AddCommGrpCat.{u₁}]
variable [J₁.WEqualsLocallyBijective AddCommGrpCat.{u₁}]
variable [HasSheafify J₂ AddCommGrpCat.{u₁}]
variable [J₂.WEqualsLocallyBijective AddCommGrpCat.{u₁}]
variable {ι₁ : Type}

set_option backward.isDefEq.respectTransparency false in
/-- Componentwise isomorphisms that commute with every face restriction
intertwine the differentials of two small-cover Cech complexes. -/
lemma smallCoverCechPiMapIso_d_succ
    (U : ι₁ → C₁) (V : ι₁ → D₁)
    (M : SheafOfModules.{u₁} R₁) (N : SheafOfModules.{u₁} R₂)
    (e : ∀ (n : ℕ) (f : Fin (n + 1) → ι₁),
      smallCoverCechTermFamily R₁ U M n f ≅
        smallCoverCechTermFamily R₂ V N n f)
    (hface : ∀ (n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → ι₁),
      let EU := (FormalCoproduct.mk _ U).cech
      let EV := (FormalCoproduct.mk _ V).cech
      (e n (cechDeleteTuple i f)).hom ≫
          N.val.presheaf.map ((EV.map (SimplexCategory.δ i).op).φ f).op =
        M.val.presheaf.map ((EU.map (SimplexCategory.δ i).op).φ f).op ≫
          (e (n + 1) f).hom)
    (n : ℕ) :
    (Pi.mapIso (e n)).hom ≫ (smallCoverCechComplex R₂ V N).d n (n + 1) =
      (smallCoverCechComplex R₁ U M).d n (n + 1) ≫
        (Pi.mapIso (e (n + 1))).hom := by
  apply Pi.hom_ext
  intro f
  change (Fin (n + 2) → ι₁) at f
  change
    (Pi.mapIso (e n)).hom ≫
        (smallCoverCechComplex R₂ V N).d n (n + 1) ≫
        Pi.π (smallCoverCechTermFamily R₂ V N (n + 1)) f =
      ((smallCoverCechComplex R₁ U M).d n (n + 1) ≫
        (Pi.mapIso (e (n + 1))).hom) ≫
        Pi.π (smallCoverCechTermFamily R₂ V N (n + 1)) f
  rw [Category.assoc]
  rw [smallCoverCechComplex_d_succ_comp_π R₂ V N n f]
  rw [Preadditive.comp_sum]
  conv_rhs =>
    rw [Pi.mapIso_hom_π]
  conv_rhs => rw [← Category.assoc]
  rw [smallCoverCechComplex_d_succ_comp_π R₁ U M n f]
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply congrArg (((-1 : ℤ) ^ (i : ℕ)) • ·)
  conv_lhs =>
    rw [← Category.assoc, Pi.mapIso_hom_π]
  rw [Category.assoc, Category.assoc, hface n i f]

end PfaffianDescent
