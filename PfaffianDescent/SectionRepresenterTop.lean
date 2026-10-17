import PfaffianDescent.SectionRepresenterCechAugmentationExact

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
noncomputable def sectionRepresenterTopIsoUnit (X : Scheme.{u}) :
    (show X.Modules from sectionRepresenter X.ringCatSheaf (⊤ : X.Opens)) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  let A : X.Modules := sectionRepresenter X.ringCatSheaf (⊤ : X.Opens)
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let aO : O.val.obj (op (⊤ : X.Opens)) :=
    moduleSectionsEquivTop X O (O.unitHomEquiv (𝟙 O))
  let aA : A.val.obj (op (⊤ : X.Opens)) :=
    sectionRepresenterHomEquiv X.ringCatSheaf (⊤ : X.Opens) A (𝟙 A)
  let hom : A ⟶ O :=
    (sectionRepresenterHomEquiv X.ringCatSheaf (⊤ : X.Opens) O).symm aO
  let inv : O ⟶ A :=
    A.unitHomEquiv.symm ((moduleSectionsEquivTop X A).symm aA)
  refine ⟨hom, inv, ?_, ?_⟩
  · apply (sectionRepresenterHomEquiv X.ringCatSheaf
      (⊤ : X.Opens) A).injective
    change inv.val.app (op (⊤ : X.Opens))
        (sectionRepresenterHomEquiv X.ringCatSheaf
          (⊤ : X.Opens) O hom) =
      sectionRepresenterHomEquiv X.ringCatSheaf
        (⊤ : X.Opens) A (𝟙 A)
    rw [Equiv.apply_symm_apply]
    change inv.val.app (op (⊤ : X.Opens)) aO = aA
    rw [← moduleSectionsEquivTop_naturality X inv (O.unitHomEquiv (𝟙 O))]
    calc
      moduleSectionsEquivTop X A
          (SheafOfModules.sectionsMap inv (O.unitHomEquiv (𝟙 O))) =
          moduleSectionsEquivTop X A (A.unitHomEquiv ((𝟙 O) ≫ inv)) :=
        congrArg (moduleSectionsEquivTop X A)
          (SheafOfModules.unitHomEquiv_comp_apply (𝟙 O) inv).symm
      _ = moduleSectionsEquivTop X A (A.unitHomEquiv inv) :=
        congrArg (fun q => moduleSectionsEquivTop X A (A.unitHomEquiv q))
          (Category.id_comp inv)
      _ = aA := by
        dsimp [inv]
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · apply O.unitHomEquiv.injective
    rw [SheafOfModules.unitHomEquiv_comp_apply]
    apply (moduleSectionsEquivTop X O).injective
    rw [moduleSectionsEquivTop_naturality X hom (A.unitHomEquiv inv)]
    change hom.val.app (op (⊤ : X.Opens))
        (moduleSectionsEquivTop X A (A.unitHomEquiv inv)) =
      moduleSectionsEquivTop X O (O.unitHomEquiv (𝟙 O))
    dsimp [inv]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change sectionRepresenterHomEquiv X.ringCatSheaf
      (⊤ : X.Opens) O ((𝟙 A) ≫ hom) = aO
    calc
      sectionRepresenterHomEquiv X.ringCatSheaf
          (⊤ : X.Opens) O ((𝟙 A) ≫ hom) =
          sectionRepresenterHomEquiv X.ringCatSheaf
            (⊤ : X.Opens) O hom :=
        congrArg (sectionRepresenterHomEquiv X.ringCatSheaf
          (⊤ : X.Opens) O) (Category.id_comp hom)
      _ = aO := by
        dsimp [hom]
        rw [Equiv.apply_symm_apply]

end PfaffianDescent
