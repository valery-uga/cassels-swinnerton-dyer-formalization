import PfaffianDescent.ActualClosedImmersionFactorIdealTwistRestriction
import PfaffianDescent.ActualPullbackTensorLeftUnit

/- SOURCE ONLY / UNVERIFIED. The actual restricted ideal-twist section,
under its actual ideal inclusion and left unitor, is the literal pullback
of the original ambient section. The comparison is derived. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open BundleSectionZeroLocus IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

def actualIdealTwistInclusion
    {X Z : Scheme.{u}} (q : Z ⟶ X) [IsClosedImmersion q] (T : X.Modules) :
    schemeModuleTensor (closedImmersionModule q) T ⟶ T :=
  schemeModuleTensorMap (closedImmersionModuleToUnit q) (𝟙 T) ≫
    (schemeModuleTensorUnitLeftIso T).hom

lemma actualIdealTwistRestriction_inclusion
    {Y X Z : Scheme.{u}} (i : X ⟶ Y) (q : Z ⟶ X)
    [IsClosedImmersion q] [IsClosedImmersion (q ≫ i)] (T : Y.Modules) :
    actualClosedImmersionFactorIdealTwistRestriction i q T ≫
        actualIdealTwistInclusion q ((Scheme.Modules.pullback i).obj T) =
      (Scheme.Modules.pullback i).map (actualIdealTwistInclusion (q ≫ i) T) := by
  let P := Scheme.Modules.pullback i
  let a := schemeModuleTensorMap (closedImmersionModuleToUnit (q ≫ i)) (𝟙 T)
  let b := cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap i (schemeModuleUnit Y) T
  let c := schemeModuleTensorMap (pullbackUnitComparison i) (𝟙 (P.obj T))
  let t := (schemeModuleTensorUnitLeftIso (P.obj T)).hom
  let r := actualClosedImmersionFactorIdealTwistRestriction i q T
  let j := schemeModuleTensorMap (closedImmersionModuleToUnit q) (𝟙 (P.obj T))
  have hr : r ≫ j = P.map a ≫ b ≫ c :=
    actualClosedImmersionFactorIdealTwistRestriction_toUnit i q T
  have hu : b ≫ c ≫ t = P.map (schemeModuleTensorUnitLeftIso T).hom :=
    actualPullbackTensorMap_unit_left i T
  change r ≫ (j ≫ t) = P.map (a ≫ (schemeModuleTensorUnitLeftIso T).hom)
  calc
    _ = (r ≫ j) ≫ t := (Category.assoc r j t).symm
    _ = (P.map a ≫ b ≫ c) ≫ t := congrArg (fun m => m ≫ t) hr
    _ = P.map a ≫ (b ≫ c ≫ t) :=
      (Category.assoc (P.map a) (b ≫ c) t).trans
        (congrArg (fun m => P.map a ≫ m) (Category.assoc b c t))
    _ = P.map a ≫ P.map (schemeModuleTensorUnitLeftIso T).hom :=
      congrArg (fun m => P.map a ≫ m) hu
    _ = _ := (P.map_comp a (schemeModuleTensorUnitLeftIso T).hom).symm

lemma actualIdealTwistRestriction_nativeInclusion
    {Y X Z : Scheme.{u}} (i : X ⟶ Y) (q : Z ⟶ X)
    [IsClosedImmersion q] [IsClosedImmersion (q ≫ i)]
    (T : Y.Modules) (N : X.Modules) (e : (Scheme.Modules.pullback i).obj T ≅ N) :
    actualClosedImmersionFactorIdealTwistRestriction i q T ≫
        schemeModuleTensorMap (𝟙 (closedImmersionModule q)) e.hom ≫
        actualIdealTwistInclusion q N =
      (Scheme.Modules.pullback i).map (actualIdealTwistInclusion (q ≫ i) T) ≫ e.hom := by
  let P := Scheme.Modules.pullback i
  let I : X.Modules := closedImmersionModule q
  let O : X.Modules := schemeModuleUnit X
  let PT : X.Modules := P.obj T
  let a : I ⟶ O := closedImmersionModuleToUnit q
  let r := actualClosedImmersionFactorIdealTwistRestriction i q T
  let bPT := schemeModuleTensorMap a (𝟙 PT)
  let bN := schemeModuleTensorMap a (𝟙 N)
  let tI := schemeModuleTensorMap (𝟙 I) e.hom
  let tO := schemeModuleTensorMap (𝟙 O) e.hom
  let lPT := (schemeModuleTensorUnitLeftIso PT).hom
  let lN := (schemeModuleTensorUnitLeftIso N).hom
  have hLeft : tI ≫ bN = schemeModuleTensorMap a e.hom := by
    exact (schemeModuleTensorMap_comp (𝟙 I) e.hom a (𝟙 N)).trans
      (congrArg₂ (fun (f : I ⟶ O) (g : PT ⟶ N) => schemeModuleTensorMap f g)
        (Category.id_comp a) (Category.comp_id e.hom))
  have hRight : bPT ≫ tO = schemeModuleTensorMap a e.hom := by
    exact (schemeModuleTensorMap_comp a (𝟙 PT) (𝟙 O) e.hom).trans
      (congrArg₂ (fun (f : I ⟶ O) (g : PT ⟶ N) => schemeModuleTensorMap f g)
        (Category.comp_id a) (Category.id_comp e.hom))
  have hs : tI ≫ bN = bPT ≫ tO := hLeft.trans hRight.symm
  have hUnit : tO ≫ lN = lPT ≫ e.hom :=
    schemeModuleTensorUnitLeftIso_naturality e.hom
  have hNative : tI ≫ actualIdealTwistInclusion q N =
      actualIdealTwistInclusion q PT ≫ e.hom := by
    calc
      _ = tI ≫ (bN ≫ lN) := rfl
      _ = (tI ≫ bN) ≫ lN := (Category.assoc _ _ _).symm
      _ = (bPT ≫ tO) ≫ lN := congrArg (fun m => m ≫ lN) hs
      _ = bPT ≫ (tO ≫ lN) := Category.assoc _ _ _
      _ = bPT ≫ (lPT ≫ e.hom) := congrArg (fun m => bPT ≫ m) hUnit
      _ = (bPT ≫ lPT) ≫ e.hom := (Category.assoc _ _ _).symm
  calc
    _ = r ≫ (actualIdealTwistInclusion q PT ≫ e.hom) :=
      congrArg (fun m => r ≫ m) hNative
    _ = (r ≫ actualIdealTwistInclusion q PT) ≫ e.hom :=
      (Category.assoc _ _ _).symm
    _ = P.map (actualIdealTwistInclusion (q ≫ i) T) ≫ e.hom :=
      congrArg (fun m => m ≫ e.hom) (actualIdealTwistRestriction_inclusion i q T)

end PfaffianDescent
