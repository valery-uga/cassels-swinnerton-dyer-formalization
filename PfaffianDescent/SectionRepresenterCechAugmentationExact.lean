import PfaffianDescent.SectionRepresenterCechLocalExact

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
namespace PfaffianDescent
universe u
variable {C : Type u} [SmallCategory C] [HasFiniteLimits C]

noncomputable def formalCoproductStarCechAugmentedIso
    (X T : C) (hT : IsTerminal T)
    (U : FormalCoproduct.{u} C) :
    letI : HasFiniteProducts (Over X) :=
      CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
    let hTX : IsTerminal ((Over.star X).obj T) := hT.isTerminalObj (Over.star X)
    ((FormalCoproduct.mapFunctor (Over.star X)).obj U).cech.augmentOfIsTerminal
        (FormalCoproduct.isTerminalIncl ((Over.star X).obj T) hTX) ≅
      (SimplicialObject.Augmented.whiskeringObj
        (FormalCoproduct.{u} C) (FormalCoproduct.{u} (Over X))
        (FormalCoproduct.mapFunctor (Over.star X))).obj
          (U.cech.augmentOfIsTerminal (FormalCoproduct.isTerminalIncl T hT)) := by
  letI : HasFiniteProducts (Over X) :=
    CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  let hTX : IsTerminal ((Over.star X).obj T) := hT.isTerminalObj (Over.star X)
  refine Comma.isoMk (formalCoproductStarCechIso X U).symm (Iso.refl _) ?_
  apply NatTrans.ext
  funext n
  apply (FormalCoproduct.isTerminalIncl ((Over.star X).obj T) hTX).hom_ext

end PfaffianDescent

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
universe u
variable {C : Type u} [SmallCategory C] [HasFiniteLimits C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
noncomputable def augmentedWhiskeringCompIso
    {A B D : Type u} [Category A] [Category B] [Category D]
    (F : A ⥤ B) (G : B ⥤ D) (Z : SimplicialObject.Augmented A) :
    (SimplicialObject.Augmented.whiskeringObj B D G).obj
        ((SimplicialObject.Augmented.whiskeringObj A B F).obj Z) ≅
      (SimplicialObject.Augmented.whiskeringObj A D (F ⋙ G)).obj Z := by
  refine Comma.isoMk (Iso.refl _) (Iso.refl _) ?_
  ext n
  simp only [SimplicialObject.Augmented.whiskeringObj,
    SimplicialObject.Augmented.drop_obj, SimplicialObject.Augmented.point_obj,
    Iso.refl_hom, NatTrans.id_app, NatTrans.comp_app,
    Functor.id_map, Functor.whiskerRight_app, Functor.constComp_hom_app,
    Functor.const_map_app, Functor.comp_map, Functor.map_id,
    Category.id_comp, Category.comp_id]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

noncomputable def overSectionRepresenterCechAugmentedIso
    (X : C) {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T) :
    letI : HasFiniteProducts (Over X) :=
      CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
    sectionRepresenterCechAugmented (R.over X)
        (fun i => (Over.star X).obj (U i)) ((Over.star X).obj T)
        (hT.isTerminalObj (Over.star X)) ≅
      (SimplicialObject.Augmented.whiskeringObj
        (SheafOfModules.{u} R) (SheafOfModules.{u} (R.over X))
        (SheafOfModules.overFunctor R X)).obj
          (sectionRepresenterCechAugmented R U T hT) := by
  letI : HasFiniteProducts (Over X) :=
    CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  let Q := FormalCoproduct.mk ι U
  let A := Q.cech.augmentOfIsTerminal (FormalCoproduct.isTerminalIncl T hT)
  let e₁ := (SimplicialObject.Augmented.whiskeringObj
    (FormalCoproduct.{u} (Over X)) (SheafOfModules.{u} (R.over X))
    (sectionRepresenterFormalCoproductFunctor (R.over X))).mapIso
      (formalCoproductStarCechAugmentedIso X T hT Q)
  let e₂ := ((SimplicialObject.Augmented.whiskering
    (FormalCoproduct.{u} C) (SheafOfModules.{u} (R.over X))).mapIso
      (overSectionRepresenterFormalCoproductNatIso R X)).app A
  exact e₁ ≪≫
    augmentedWhiskeringCompIso
      (FormalCoproduct.mapFunctor (Over.star X))
      (sectionRepresenterFormalCoproductFunctor (R.over X)) A ≪≫
    e₂ ≪≫
    (augmentedWhiskeringCompIso
      (sectionRepresenterFormalCoproductFunctor R)
      (SheafOfModules.overFunctor R X) A).symm

end PfaffianDescent

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
universe u
variable {C : Type u} [SmallCategory C] [HasFiniteLimits C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

noncomputable def homologicalComplexIsoComponent
    {A : Type u} [Category A] [HasZeroMorphisms A]
    {ι : Type} {c : ComplexShape ι} {K L : HomologicalComplex A c}
    (e : K ≅ L) (n : ι) : K.X n ≅ L.X n where
  hom := e.hom.f n
  inv := e.inv.f n
  hom_inv_id := congrArg (fun f => f.f n) e.hom_inv_id
  inv_hom_id := congrArg (fun f => f.f n) e.inv_hom_id

noncomputable def sectionRepresenterCechAugmentationShortComplex
    {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T) :
    ShortComplex (SheafOfModules.{u} R) :=
  ShortComplex.mk
    ((sectionRepresenterCechChain R U).d 1 0)
    (sectionRepresenterCechAugmentation R U T hT)
    (sectionRepresenterCech_d_one_zero_comp_augmentation R U T hT)

set_option backward.isDefEq.respectTransparency false in
noncomputable def overSectionRepresenterCechAugmentationShortComplexIso
    (X : C) {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T) :
    letI : HasFiniteProducts (Over X) :=
      CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
    let hTX : IsTerminal ((Over.star X).obj T) :=
      hT.isTerminalObj (Over.star X)
    sectionRepresenterCechAugmentationShortComplex (R.over X)
        (fun i => (Over.star X).obj (U i)) ((Over.star X).obj T) hTX ≅
      (sectionRepresenterCechAugmentationShortComplex R U T hT).map
        (SheafOfModules.overFunctor R X) := by
  letI : HasFiniteProducts (Over X) :=
    CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  letI : (SheafOfModules.overFunctor R X).PreservesZeroMorphisms :=
    SheafOfModules.overFunctor_preservesZeroMorphisms R X
  letI := overFunctorAdditive R X
  let eA := overSectionRepresenterCechAugmentedIso R X U T hT
  let eLeft := (SimplicialObject.Augmented.drop
    (C := SheafOfModules (R.over X))).mapIso eA
  let eRight := (SimplicialObject.Augmented.point
    (C := SheafOfModules (R.over X))).mapIso eA
  let eC :=
    (AlgebraicTopology.alternatingFaceMapComplex
      (SheafOfModules (R.over X))).mapIso eLeft ≪≫
      alternatingFaceMapComplexWhiskerIso
        (SheafOfModules.overFunctor R X)
        (sectionRepresenterCechSimplicial R U)
  refine ShortComplex.isoMk (homologicalComplexIsoComponent eC 1)
    (homologicalComplexIsoComponent eC 0) eRight ?_ ?_
  · exact eC.hom.comm 1 0
  · have he0 : eC.hom.f 0 = eA.hom.left.app (op ⦋0⦌) := by
      dsimp [eC, alternatingFaceMapComplexWhiskerIso]
      exact Category.comp_id _
    change eC.hom.f 0 ≫
      (SheafOfModules.overFunctor R X).map
        ((sectionRepresenterCechAugmented R U T hT).hom.app (op ⦋0⦌)) =
      (sectionRepresenterCechAugmented (R.over X)
          (fun i => (Over.star X).obj (U i)) ((Over.star X).obj T)
          (hT.isTerminalObj (Over.star X))).hom.app (op ⦋0⦌) ≫ eA.hom.right
    rw [he0]
    exact SimplicialObject.Augmented.w₀ eA.hom

variable [∀ Y, HasSheafify (J.over Y) AddCommGrpCat.{u}]
variable [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- For a covering family, the first Cech differential is exact at degree zero
and the augmentation is an epimorphism. -/
lemma sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    {ι : Type u} (U : ι → C) (hU : J.CoversTop U)
    (T : C) (hT : IsTerminal T) :
    (sectionRepresenterCechAugmentationShortComplex R U T hT).Exact ∧
      Epi (sectionRepresenterCechAugmentation R U T hT) := by
  let F : ∀ i, SheafOfModules.{u} R ⥤ SheafOfModules.{u} (R.over (U i)) :=
    fun i => SheafOfModules.overFunctor R (U i)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U hU
  letI : ∀ i, (F i).IsLeftAdjoint := fun i => by
    dsimp [F]
    exact (SheafOfModules.overPushforwardOverAdj (R := R) (U i)).isLeftAdjoint
  letI : ∀ i, PreservesFiniteLimits (F i) := fun i => by
    dsimp [F]
    exact SheafOfModules.overFunctor_preservesFiniteLimits R (U i)
  letI : ∀ i, PreservesFiniteColimits (F i) := fun _ => by
    infer_instance
  letI : ∀ i, (F i).Additive := fun i => by
    dsimp [F]
    exact overFunctorAdditive R (U i)
  let S := sectionRepresenterCechAugmentationShortComplex R U T hT
  constructor
  · rw [hF.exact_iff]
    intro i
    letI : HasFiniteProducts (Over (U i)) :=
      CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
    let hTi : IsTerminal ((Over.star (U i)).obj T) :=
      hT.isTerminalObj (Over.star (U i))
    let Tid : Over (U i) := Over.mk (𝟙 (U i))
    let hTid : IsTerminal Tid := Over.mkIdTerminal
    let dSelf : Tid ⟶ (Over.star (U i)).obj (U i) :=
      (Over.forgetAdjStar (U i)).unit.app Tid
    let d : ((Over.star (U i)).obj T) ⟶ (Over.star (U i)).obj (U i) :=
      (hTi.uniqueUpToIso hTid).hom ≫ dSelf
    have hlocal := sectionRepresenterCech_augmentation_exact_and_epi_of_split
      (R.over (U i)) (fun j => (Over.star (U i)).obj (U j))
      ((Over.star (U i)).obj T) hTi d
    let e := overSectionRepresenterCechAugmentationShortComplexIso R (U i) U T hT
    exact (ShortComplex.exact_iff_of_iso e).mp hlocal.1
  · rw [(hF.jointlyReflectEpimorphisms).epi_iff]
    intro i
    letI : HasFiniteProducts (Over (U i)) :=
      CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
    let hTi : IsTerminal ((Over.star (U i)).obj T) :=
      hT.isTerminalObj (Over.star (U i))
    let Tid : Over (U i) := Over.mk (𝟙 (U i))
    let hTid : IsTerminal Tid := Over.mkIdTerminal
    let dSelf : Tid ⟶ (Over.star (U i)).obj (U i) :=
      (Over.forgetAdjStar (U i)).unit.app Tid
    let d : ((Over.star (U i)).obj T) ⟶ (Over.star (U i)).obj (U i) :=
      (hTi.uniqueUpToIso hTid).hom ≫ dSelf
    have hlocal := sectionRepresenterCech_augmentation_exact_and_epi_of_split
      (R.over (U i)) (fun j => (Over.star (U i)).obj (U j))
      ((Over.star (U i)).obj T) hTi d
    let Sloc := sectionRepresenterCechAugmentationShortComplex (R.over (U i))
      (fun j => (Over.star (U i)).obj (U j)) ((Over.star (U i)).obj T) hTi
    let e := overSectionRepresenterCechAugmentationShortComplexIso R (U i) U T hT
    haveI : Epi Sloc.g := hlocal.2
    haveI : Epi (Sloc.g ≫ e.hom.τ₃) := inferInstance
    haveI : Epi (e.hom.τ₂ ≫ (S.map (F i)).g) := by
      rw [e.hom.comm₂₃]
      infer_instance
    change Epi ((S.map (F i)).g)
    exact epi_of_epi e.hom.τ₂ (S.map (F i)).g

end PfaffianDescent
