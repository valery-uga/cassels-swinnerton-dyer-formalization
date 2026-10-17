import PfaffianDescent.ActualNamedIdealTwistChartFactory
import PfaffianDescent.ActualClosedIdealSourceRestrictionIso
import PfaffianDescent.ActualRestrictedIdealTwistLocalBasisAction
import PfaffianDescent.BundleSectionZeroLocus

/- SOURCE ONLY / UNVERIFIED. A coherent package of the WHOLE original
chart Isos and their proved inclusion/local-section/coefficient laws.
The actual caller constructs this package once. It supplies no Iso,
whole-Iso comparison, inclusion or local-action certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every value and law concerns the SAME named chart map. Whole-Iso
fields retain the complete raw constructions, including their inverses. -/
structure ActualNamedIdealTwistChartData
    {X Y Z : Scheme.{u}} (U0 : X.Opens) (f : Y ⟶ (U0 : Scheme)) [IsIso f]
    (f0 : Y ⟶ X) [IsOpenImmersion f0] (hF : f0 = f ≫ U0.ι)
    (q : Z ⟶ X) [IsClosedImmersion q]
    (j : Z ⟶ Y) [IsClosedImmersion j]
    (hfac : (j ≫ f) ≫ U0.ι = q) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U0.ι).obj T ≅
      SheafOfModules.unit (U0 : Scheme).ringCatSheaf) where
  idealIso : (Scheme.Modules.restrictFunctor f0).obj
    (closedImmersionIdealTwist q T) ≅ closedImmersionModule j
  unitIso : (Scheme.Modules.restrictFunctor f0).obj T ≅ schemeModuleUnit Y
  untwistedIso : (Scheme.Modules.restrictFunctor f0).obj
    (closedImmersionModule q) ≅ closedImmersionModule j
  idealIso_eq_named : idealIso =
    actualNamedIdealTwistChartIso U0 f f0 hF q j hfac T p
  unitIso_eq_named : unitIso =
    actualNamedIdealTwistChartUnitIso U0 f f0 hF T p
  idealIso_eq_source : HEq idealIso
    (actualOriginalIdealTwistSourceRefinementIso U0 f q j hfac T p)
  unitIso_eq_source : HEq unitIso
    (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U0 f T p)
  untwistedIso_eq_source : untwistedIso =
    actualClosedIdealSourceRestrictionIso f0 q j
      (actualNamedIdealChartFactorization U0 f f0 hF q j hfac)
  inclusion : idealIso.hom ≫ closedImmersionModuleToUnit j =
    (Scheme.Modules.restrictFunctor f0).map (actualIdealTwistInclusion q T) ≫
      unitIso.hom
  localBasisAction : ∀ (v : schemeModuleUnit X ⟶ T),
    ((Scheme.Modules.restrictFunctor (f ≫ U0.ι)).map v ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U0 f T p).hom =
        (Scheme.Modules.restrictUnitIso (f ≫ U0.ι)).hom) →
    ∀ (U : X.Opens) (m : (closedImmersionModule q).val.obj (op U)),
      idealIso.hom.val.app (op (f0 ⁻¹ᵁ U))
        (((Scheme.Modules.restrictAdjunction f0).unit.app
          (schemeModuleTensor (closedImmersionModule q) T)).val.app (op U)
            (actualModuleLocalTensorSection (closedImmersionModule q) T U m
              (T.val.map (homOfLE (show U ≤ ⊤ from le_top)).op
                (v.val.app (op ⊤) (1 : Γ(X, ⊤)))))) =
      untwistedIso.hom.val.app (op (f0 ⁻¹ᵁ U))
        (((Scheme.Modules.restrictAdjunction f0).unit.app
          (closedImmersionModule q)).val.app (op U) m)
  unitCoefficient : ∀ (s : schemeModuleUnit X ⟶ T) (c : Γ(Y, ⊤)),
    (unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso (f ≫ U0.ι)).inv ≫
        (Scheme.Modules.restrictFunctor (f ≫ U0.ι)).map s ≫
        (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U0 f T p).hom) = c) →
    unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso f0).inv ≫
        (Scheme.Modules.restrictFunctor f0).map s ≫ unitIso.hom) = c

/-- The full local action is proved at abstract source data. In particular,
its ideal-inclusion/tensor-left-unit conversion is checked here. -/
private lemma actualRawIdealChartData_localBasisAction
    {X Y Z : Scheme.{u}} (U0 : X.Opens) (f : Y ⟶ (U0 : Scheme)) [IsIso f]
    (q : Z ⟶ X) [IsClosedImmersion q]
    (j : Z ⟶ Y) [IsClosedImmersion j]
    (hfac : (j ≫ f) ≫ U0.ι = q) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U0.ι).obj T ≅
      SheafOfModules.unit (U0 : Scheme).ringCatSheaf)
    (v : schemeModuleUnit X ⟶ T)
    (hb : (Scheme.Modules.restrictFunctor (f ≫ U0.ι)).map v ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U0 f T p).hom =
      (Scheme.Modules.restrictUnitIso (f ≫ U0.ι)).hom)
    (U : X.Opens) (m : (closedImmersionModule q).val.obj (op U)) :
    (actualOriginalIdealTwistSourceRefinementIso U0 f q j hfac T p).hom.val.app
      (op ((f ≫ U0.ι) ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction (f ≫ U0.ι)).unit.app
        (schemeModuleTensor (closedImmersionModule q) T)).val.app (op U)
          (actualModuleLocalTensorSection (closedImmersionModule q) T U m
            (v.val.app (op U) (1 : Γ(X, U))))) =
    (actualClosedIdealSourceRestrictionIso (f ≫ U0.ι) q j
      ((Category.assoc j f U0.ι).symm.trans hfac)).hom.val.app
      (op ((f ≫ U0.ι) ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction (f ≫ U0.ι)).unit.app
        (closedImmersionModule q)).val.app (op U) m) := by
  letI : Mono (closedImmersionModuleToUnit j) := by
    dsimp only [closedImmersionModuleToUnit]
    infer_instance
  exact actualRestrictedIdealTwistLocalBasisAction (f ≫ U0.ι)
    (closedImmersionModule q) T (closedImmersionModule j)
    (closedImmersionModuleToUnit q) (closedImmersionModuleToUnit j) v
    (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U0 f T p)
    (actualOriginalIdealTwistSourceRefinementIso U0 f q j hfac T p)
    (actualClosedIdealSourceRestrictionIso (f ≫ U0.ι) q j
      ((Category.assoc j f U0.ι).symm.trans hfac)) hb
    (actualOriginalIdealTwistSourceRefinementIso_toInclusion U0 f q j hfac T p)
    (actualClosedIdealSourceRestrictionIso_toUnit (f ≫ U0.ι) q j
      ((Category.assoc j f U0.ι).symm.trans hfac)) U m

/-- Natural restriction of the SAME top basis value is converted before
any original cubic, affine localization or chosen chart is inserted. -/
private lemma actualRawIdealChartData_restrictedTopAction
    {X Y Z : Scheme.{u}} (U0 : X.Opens) (f : Y ⟶ (U0 : Scheme)) [IsIso f]
    (q : Z ⟶ X) [IsClosedImmersion q]
    (j : Z ⟶ Y) [IsClosedImmersion j]
    (hfac : (j ≫ f) ≫ U0.ι = q) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U0.ι).obj T ≅
      SheafOfModules.unit (U0 : Scheme).ringCatSheaf)
    (v : schemeModuleUnit X ⟶ T)
    (hb : (Scheme.Modules.restrictFunctor (f ≫ U0.ι)).map v ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U0 f T p).hom =
      (Scheme.Modules.restrictUnitIso (f ≫ U0.ι)).hom)
    (U : X.Opens) (m : (closedImmersionModule q).val.obj (op U)) :
    (actualOriginalIdealTwistSourceRefinementIso U0 f q j hfac T p).hom.val.app
      (op ((f ≫ U0.ι) ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction (f ≫ U0.ι)).unit.app
        (schemeModuleTensor (closedImmersionModule q) T)).val.app (op U)
          (actualModuleLocalTensorSection (closedImmersionModule q) T U m
            (T.val.map (homOfLE (show U ≤ ⊤ from le_top)).op
              (v.val.app (op ⊤) (1 : Γ(X, ⊤)))))) =
    (actualClosedIdealSourceRestrictionIso (f ≫ U0.ι) q j
      ((Category.assoc j f U0.ι).symm.trans hfac)).hom.val.app
      (op ((f ≫ U0.ι) ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction (f ≫ U0.ι)).unit.app
        (closedImmersionModule q)).val.app (op U) m) := by
  exact (congrArg (fun t =>
    (actualOriginalIdealTwistSourceRefinementIso U0 f q j hfac T p).hom.val.app
      (op ((f ≫ U0.ι) ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction (f ≫ U0.ι)).unit.app
        (schemeModuleTensor (closedImmersionModule q) T)).val.app (op U)
          (actualModuleLocalTensorSection (closedImmersionModule q) T U m t)))
      (actualUnitHom_restrictedTopSection T v U)).trans
        (actualRawIdealChartData_localBasisAction U0 f q j hfac T p v hb U m)

/-- Transport only the abstract unit-basis square, before inserting the
ideal, its tensor section, or its local evaluation maps. -/
private lemma actualNamedIdealChartData_basisSquare
    {X Y : Scheme.{u}} (U0 : X.Opens) (f : Y ⟶ (U0 : Scheme)) [IsIso f]
    (f0 : Y ⟶ X) [IsOpenImmersion f0] (hF : f0 = f ≫ U0.ι)
    (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U0.ι).obj T ≅
      SheafOfModules.unit (U0 : Scheme).ringCatSheaf)
    (v : schemeModuleUnit X ⟶ T)
    (hb : (Scheme.Modules.restrictFunctor (f ≫ U0.ι)).map v ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U0 f T p).hom =
      (Scheme.Modules.restrictUnitIso (f ≫ U0.ι)).hom) :
    (Scheme.Modules.restrictFunctor f0).map v ≫
      (actualNamedIdealTwistChartUnitIso U0 f f0 hF T p).hom =
      (Scheme.Modules.restrictUnitIso f0).hom := by
  subst f0
  exact hb

/-- The SAME local action with named factory heads is checked as one
opaque proved field law. The raw action is reused before package assembly. -/
private lemma actualNamedIdealChartData_localBasisAction
    {X Y Z : Scheme.{u}} (U0 : X.Opens) (f : Y ⟶ (U0 : Scheme)) [IsIso f]
    (f0 : Y ⟶ X) [hf0 : IsOpenImmersion f0] (hF : f0 = f ≫ U0.ι)
    (q : Z ⟶ X) [IsClosedImmersion q]
    (j : Z ⟶ Y) [IsClosedImmersion j]
    (hfac : (j ≫ f) ≫ U0.ι = q) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U0.ι).obj T ≅
      SheafOfModules.unit (U0 : Scheme).ringCatSheaf) :
    ∀ (v : schemeModuleUnit X ⟶ T),
    ((Scheme.Modules.restrictFunctor (f ≫ U0.ι)).map v ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U0 f T p).hom =
        (Scheme.Modules.restrictUnitIso (f ≫ U0.ι)).hom) →
    ∀ (U : X.Opens) (m : (closedImmersionModule q).val.obj (op U)),
      (actualNamedIdealTwistChartIso U0 f f0 hF q j hfac T p).hom.val.app (op (f0 ⁻¹ᵁ U))
        (((Scheme.Modules.restrictAdjunction f0).unit.app
          (schemeModuleTensor (closedImmersionModule q) T)).val.app (op U)
            (actualModuleLocalTensorSection (closedImmersionModule q) T U m
              (T.val.map (homOfLE (show U ≤ ⊤ from le_top)).op
                (v.val.app (op ⊤) (1 : Γ(X, ⊤)))))) =
      (actualClosedIdealSourceRestrictionIso f0 q j
        (actualNamedIdealChartFactorization U0 f f0 hF q j hfac)).hom.val.app (op (f0 ⁻¹ᵁ U))
        (((Scheme.Modules.restrictAdjunction f0).unit.app
          (closedImmersionModule q)).val.app (op U) m) := by
  intro v hb U m
  letI : Mono (closedImmersionModuleToUnit j) := by
    dsimp only [closedImmersionModuleToUnit]
    infer_instance
  have hlocal := actualRestrictedIdealTwistLocalBasisAction f0
    (closedImmersionModule q) T (closedImmersionModule j)
    (closedImmersionModuleToUnit q) (closedImmersionModuleToUnit j) v
    (actualNamedIdealTwistChartUnitIso U0 f f0 hF T p)
    (actualNamedIdealTwistChartIso U0 f f0 hF q j hfac T p)
    (actualClosedIdealSourceRestrictionIso f0 q j
      (actualNamedIdealChartFactorization U0 f f0 hF q j hfac))
    (actualNamedIdealChartData_basisSquare U0 f f0 hF T p v hb)
    (actualNamedIdealTwistChartIso_toInclusion U0 f f0 hF q j hfac T p)
    (actualClosedIdealSourceRestrictionIso_toUnit f0 q j
      (actualNamedIdealChartFactorization U0 f f0 hF q j hfac)) U m
  exact (congrArg (fun t =>
    (actualNamedIdealTwistChartIso U0 f f0 hF q j hfac T p).hom.val.app
      (op (f0 ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction f0).unit.app
        (schemeModuleTensor (closedImmersionModule q) T)).val.app (op U)
          (actualModuleLocalTensorSection (closedImmersionModule q) T U m t)))
      (actualUnitHom_restrictedTopSection T v U)).trans hlocal

/-- Coefficient transport is proved separately, so record checking does
not reconstruct the raw unit Iso while checking every other field. -/
private lemma actualNamedIdealChartData_unitCoefficient
    {X Y Z : Scheme.{u}} (U0 : X.Opens) (f : Y ⟶ (U0 : Scheme)) [IsIso f]
    (f0 : Y ⟶ X) [hf0 : IsOpenImmersion f0] (hF : f0 = f ≫ U0.ι)
    (q : Z ⟶ X) [IsClosedImmersion q]
    (j : Z ⟶ Y) [IsClosedImmersion j]
    (hfac : (j ≫ f) ≫ U0.ι = q) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U0.ι).obj T ≅
      SheafOfModules.unit (U0 : Scheme).ringCatSheaf) :
    ∀ (s : schemeModuleUnit X ⟶ T) (c : Γ(Y, ⊤)),
    (unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso (f ≫ U0.ι)).inv ≫
        (Scheme.Modules.restrictFunctor (f ≫ U0.ι)).map s ≫
        (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U0 f T p).hom) = c) →
    unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso f0).inv ≫
        (Scheme.Modules.restrictFunctor f0).map s ≫ (actualNamedIdealTwistChartUnitIso U0 f f0 hF T p).hom) = c := by
  subst f0
  exact fun _ _ h => h

/-- Each Iso value has its accepted NAMED factory head. Whole-source
fidelity and inclusion reuse independently proved factory laws; the two
remaining laws are fully proved opaque lemmas above. No raw-to-named
record-wide definitional comparison is required from a caller. -/
def actualNamedIdealTwistChartData
    {X Y Z : Scheme.{u}} (U0 : X.Opens) (f : Y ⟶ (U0 : Scheme)) [IsIso f]
    (f0 : Y ⟶ X) [hf0 : IsOpenImmersion f0] (hF : f0 = f ≫ U0.ι)
    (q : Z ⟶ X) [IsClosedImmersion q]
    (j : Z ⟶ Y) [IsClosedImmersion j]
    (hfac : (j ≫ f) ≫ U0.ι = q) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U0.ι).obj T ≅
      SheafOfModules.unit (U0 : Scheme).ringCatSheaf) :
    ActualNamedIdealTwistChartData U0 f f0 hF q j hfac T p := by
  exact {
    idealIso := actualNamedIdealTwistChartIso U0 f f0 hF q j hfac T p
    unitIso := actualNamedIdealTwistChartUnitIso U0 f f0 hF T p
    untwistedIso := actualClosedIdealSourceRestrictionIso f0 q j
      (actualNamedIdealChartFactorization U0 f f0 hF q j hfac)
    idealIso_eq_named := rfl
    unitIso_eq_named := rfl
    idealIso_eq_source := actualNamedIdealTwistChartIso_heq_source U0 f f0 hF q j hfac T p
    unitIso_eq_source := actualNamedIdealTwistChartUnitIso_heq_source U0 f f0 hF T p
    untwistedIso_eq_source := rfl
    inclusion := actualNamedIdealTwistChartIso_toInclusion U0 f f0 hF q j hfac T p
    localBasisAction := actualNamedIdealChartData_localBasisAction U0 f f0 hF q j hfac T p
    unitCoefficient := actualNamedIdealChartData_unitCoefficient U0 f f0 hF q j hfac T p }

end PfaffianDescent
