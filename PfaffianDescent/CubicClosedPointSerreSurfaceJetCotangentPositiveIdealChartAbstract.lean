import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealOpenRestrictionInclusion
import PfaffianDescent.SerreExtensionFoundation
import PfaffianDescent.VoisinPositiveTwistTriviality

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open IdealSheafDataModule ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false

private def composeThreeChartIsos {C : Type u} [Category C]
    {W X Y Z : C} (a : W ≅ X) (b : X ≅ Y) (c : Y ≅ Z) : W ≅ Z :=
  a ≪≫ b ≪≫ c

private def chartCoordinateDiscrepancy {C : Type u} [Category C]
    {V O T P : C} (e : V ≅ O) (a : O ≅ P) (l : V ≅ T) (p : T ≅ P) : P ≅ P :=
  a.symm ≪≫ e.symm ≪≫ l ≪≫ p

private theorem correctedChartSquare {C : Type u} [Category C]
    {W M N V O T P : C} (eI : W ≅ M) (eJ : M ≅ N)
    (eO : V ≅ O) (a : O ≅ P) (l : V ≅ T) (p : T ≅ P) (k : N ≅ N)
    (f : W ⟶ V) (m : M ⟶ O) (n : N ⟶ P)
    (hk : k.hom ≫ n = n ≫ (chartCoordinateDiscrepancy eO a l p).hom)
    (hj : eJ.hom ≫ n = m ≫ a.hom)
    (hn : f ≫ eO.hom = eI.hom ≫ m) :
    (composeThreeChartIsos eI eJ k).hom ≫ n = f ≫ l.hom ≫ p.hom := by
  simp only [composeThreeChartIsos, Iso.trans_hom, Category.assoc]
  rw [hk, ← Category.assoc eJ.hom, hj]
  dsimp only [chartCoordinateDiscrepancy, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc eI.hom m, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Scheme-level tensor restriction coordinates, abstracting the ambient projective chart. -/
def cubicClosedPointSerreSurfaceJetCotangent_abstractTensorRestrictIso
    {X : Scheme.{u}} (U : X.Opens) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).obj (schemeModuleTensor M T) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj M :=
  schemeModuleTensorRestrictIsoOfLocalTrivialization U M T
    (overFunctorIsoUnit_of_restrictIsoUnit U p)

def cubicClosedPointSerreSurfaceJetCotangent_abstractChartUnitDiscrepancy
    {X : Scheme.{u}} (U : X.Opens) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    SheafOfModules.unit (U : Scheme).ringCatSheaf ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
  chartCoordinateDiscrepancy
    (cubicClosedPointSerreSurfaceJetCotangent_abstractTensorRestrictIso U T p
      (SheafOfModules.unit X.ringCatSheaf))
    (Scheme.Modules.restrictUnitIso U.ι)
    ((Scheme.Modules.restrictFunctor U.ι).mapIso (schemeModuleTensorUnitLeftIso T)) p

/-- The actual locally trivial ideal twist with inclusion-compatible coordinates. -/
def cubicClosedPointSerreSurfaceJetCotangent_abstractIdealChartIso
    {X : Scheme.{u}} (U : X.Opens) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf)
    {Z : Scheme.{u}} (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion j] [IsClosedImmersion (j ≫ U.ι)] :
    (Scheme.Modules.restrictFunctor U.ι).obj
      (closedImmersionIdealTwist (j ≫ U.ι) T) ≅ closedImmersionModule j :=
  composeThreeChartIsos
    (cubicClosedPointSerreSurfaceJetCotangent_abstractTensorRestrictIso U T p
      (closedImmersionModule (j ≫ U.ι)))
    (cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso U.ι j)
    (cubicClosedPointSerreSurfaceJetCotangent_idealUnitAutomorphismIso j
      (cubicClosedPointSerreSurfaceJetCotangent_abstractChartUnitDiscrepancy U T p))

theorem cubicClosedPointSerreSurfaceJetCotangent_abstractIdealChartIso_toUnit
    {X : Scheme.{u}} (U : X.Opens) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf)
    {Z : Scheme.{u}} (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion j] [IsClosedImmersion (j ≫ U.ι)] :
    (cubicClosedPointSerreSurfaceJetCotangent_abstractIdealChartIso U T p j).hom ≫
      closedImmersionModuleToUnit j =
    (Scheme.Modules.restrictFunctor U.ι).map
      ((closedImmersionIdealTwistSequence (j ≫ U.ι) T).f ≫
        (schemeModuleTensorUnitLeftIso T).hom) ≫ p.hom := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let i := j ≫ U.ι
  let m := closedImmersionModuleToUnit i
  let eI := cubicClosedPointSerreSurfaceJetCotangent_abstractTensorRestrictIso U T p
    (closedImmersionModule i)
  let eO := cubicClosedPointSerreSurfaceJetCotangent_abstractTensorRestrictIso U T p
    (SheafOfModules.unit X.ringCatSheaf)
  let d := cubicClosedPointSerreSurfaceJetCotangent_abstractChartUnitDiscrepancy U T p
  let a := cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso U.ι j
  have hn := schemeModuleTensorRestrictIsoOfLocalTrivialization_naturality
    U (overFunctorIsoUnit_of_restrictIsoUnit U p) m
  change R.map (schemeModuleTensorMap m (𝟙 T)) ≫ eO.hom = eI.hom ≫ R.map m at hn
  have h := correctedChartSquare eI a eO (Scheme.Modules.restrictUnitIso U.ι)
    (R.mapIso (schemeModuleTensorUnitLeftIso T)) p
    (cubicClosedPointSerreSurfaceJetCotangent_idealUnitAutomorphismIso j d)
    (R.map (schemeModuleTensorMap m (𝟙 T))) (R.map m) (closedImmersionModuleToUnit j)
    (cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism_toUnit j d.hom)
    (cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso_toUnit U.ι j) hn
  change (composeThreeChartIsos eI a
      (cubicClosedPointSerreSurfaceJetCotangent_idealUnitAutomorphismIso j d)).hom ≫
      closedImmersionModuleToUnit j =
    R.map (schemeModuleTensorMap m (𝟙 T) ≫ (schemeModuleTensorUnitLeftIso T).hom) ≫ p.hom
  rw [R.map_comp, Category.assoc]
  exact h

end PfaffianDescent
