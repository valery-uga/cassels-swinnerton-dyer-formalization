import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSpecFibreCoordinates
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGlobalBasisCoordinates

/-! # Actual point fibre coordinates use the same actual surface chart functions -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidencePointChartModuleIso
    {X T : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (q : T ⟶ (U : Scheme.{u})) (r : T ⟶ X) (h : q ≫ U.ι = r) :
    (Scheme.Modules.pullback q).obj
        ((Scheme.Modules.overEquiv U).functor.obj (M.over U)) ≅
      (Scheme.Modules.pullback r).obj M :=
  (Scheme.Modules.pullback q).mapIso
      ((Scheme.Modules.overFunctorEquiv U).app M ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M) ≪≫
    ((Scheme.Modules.pullbackComp q U.ι).app M ≪≫
      (Scheme.Modules.pullbackCongr h).app M)

def serreIncidencePointChartFreeIso
    {X T : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (q : T ⟶ (U : Scheme.{u})) (r : T ⟶ X) (h : q ≫ U.ι = r) :
    SheafOfModules.free (R := T.ringCatSheaf) I ≅ (Scheme.Modules.pullback r).obj M :=
  pullbackFreeIso q I (localFreeIsoOfOver U I t) ≪≫
    serreIncidencePointChartModuleIso U M q r h

lemma serreIncidenceOverSection_hom
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) (s : M.sections) :
    let B := (Scheme.Modules.overFunctorEquiv U).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
    SheafOfModules.sectionsMap B.hom (restrictSectionToOpen U s) =
      pullbackSection U.ι M (isIso_pullbackUnitComparison U.ι) s := by
  dsimp only
  let B := (Scheme.Modules.overFunctorEquiv U).app M ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  rw [← serreIncidenceOverSection_pullback U M s, ← SheafOfModules.sectionsMap_comp,
    B.inv_hom_id, SheafOfModules.sectionsMap_id]

theorem serreIncidencePointChartModuleIso_section
    {X T : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (q : T ⟶ (U : Scheme.{u})) (r : T ⟶ X) (h : q ≫ U.ι = r) (s : M.sections) :
    SheafOfModules.sectionsMap (serreIncidencePointChartModuleIso U M q r h).hom
      (pullbackSection q ((Scheme.Modules.overEquiv U).functor.obj (M.over U))
        (isIso_pullbackUnitComparison q) (restrictSectionToOpen U s)) =
      pullbackSection r M (isIso_pullbackUnitComparison r) s := by
  let B := (Scheme.Modules.overFunctorEquiv U).app M ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  let V := (Scheme.Modules.pullbackComp q U.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr h).app M
  change SheafOfModules.sectionsMap V.hom
    (SheafOfModules.sectionsMap ((Scheme.Modules.pullback q).map B.hom)
      (pullbackSection q _ (isIso_pullbackUnitComparison q)
        (restrictSectionToOpen U s))) = _
  have hn := sectionsMap_pullbackSection q B.hom
    (isIso_pullbackUnitComparison q) (restrictSectionToOpen U s)
  have hb := serreIncidenceOverSection_hom U M s
  exact (congrArg (SheafOfModules.sectionsMap V.hom) hn).trans
    ((congrArg (fun z => SheafOfModules.sectionsMap V.hom
      (pullbackSection q _ (isIso_pullbackUnitComparison q) z)) hb).trans
      (sectionsMap_pullbackComp_pullbackCongr_pullbackSection q U.ι r h M
        (isIso_pullbackUnitComparison q) (isIso_pullbackUnitComparison U.ι)
        (isIso_pullbackUnitComparison (q ≫ U.ι)) (isIso_pullbackUnitComparison r) s))

lemma serreIncidenceSectionCoordinate_trans
    {X : Scheme.{u}} (I : Type u) {M N : X.Modules}
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M)
    (v : M ≅ N) (s : M.sections) (i : I) :
    sectionCoordinateOfFreeIso I (t ≪≫ v) (SheafOfModules.sectionsMap v.hom s) i =
      sectionCoordinateOfFreeIso I t s i := by
  change freeSectionCoordinate I (SheafOfModules.sectionsMap t.inv
    (SheafOfModules.sectionsMap v.inv (SheafOfModules.sectionsMap v.hom s))) i = _
  exact congrArg (fun z => freeSectionCoordinate I
    (SheafOfModules.sectionsMap t.inv z) i) (sectionsMap_hom_inv v.symm s)

theorem serreIncidencePointChartFreeIso_section_coordinate
    {X T : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (q : T ⟶ (U : Scheme.{u})) (r : T ⟶ X) (h : q ≫ U.ι = r) (s : M.sections) (i : I) :
    sectionCoordinateOfFreeIso I (serreIncidencePointChartFreeIso U M I t q r h)
      (pullbackSection r M (isIso_pullbackUnitComparison r) s) i =
    q.appTop (sectionCoordinateOfFreeIso I (localFreeIsoOfOver U I t)
      (restrictSectionToOpen U s) i) := by
  rw [← serreIncidencePointChartModuleIso_section U M q r h s]
  change sectionCoordinateOfFreeIso I
    (pullbackFreeIso q I (localFreeIsoOfOver U I t) ≪≫
      serreIncidencePointChartModuleIso U M q r h) _ i = _
  rw [serreIncidenceSectionCoordinate_trans]
  exact serreIncidenceSectionCoordinate_pullback q I _ _ _ i

theorem serreIncidencePointChartFreeIso_field_coordinate
    {E : Type u} [Field E] {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (q : Spec (.of E) ⟶ (U : Scheme.{u})) (r : Spec (.of E) ⟶ X)
    (h : q ≫ U.ι = r) (s : M.sections) (i : I) :
    serreIncidenceSpecFibreCoordinateEquiv E I ((Scheme.Modules.pullback r).obj M)
      (serreIncidencePointChartFreeIso U M I t q r h)
        ((pullbackSection r M (isIso_pullbackUnitComparison r) s).val (op ⊤)) i =
    fieldPointΓevaluation q (sectionCoordinateOfFreeIso I (localFreeIsoOfOver U I t)
      (restrictSectionToOpen U s) i) := by
  rw [serreIncidenceSpecFibreCoordinateEquiv_section,
    serreIncidencePointChartFreeIso_section_coordinate, fieldPointΓevaluation_eq_appTop]

end PfaffianDescent
