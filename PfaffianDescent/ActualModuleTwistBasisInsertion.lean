import PfaffianDescent.ActualPositiveTwistPullbackTensorIso
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPullbackTensorUnit

/-! SOURCE ONLY, UNVERIFIED. A genuine basis insertion is cancelled only
after actual pullback and an actual twist trivialization. The global basis
section is not assumed invertible. Structural basis laws in these generic
helpers are supplied internally by the original/native callers. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

def actualModuleTwistBasisInsertion {X : Scheme.{u}} (M T : X.Modules)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ T) :
    M ⟶ schemeModuleTensor M T :=
  (schemeModuleTensorUnitRightIso M).inv ≫ schemeModuleTensorMap (𝟙 M) v

lemma actualModuleTwistBasisInsertion_pullback_contract
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M T : X.Modules)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ T)
    (e : (Scheme.Modules.pullback f).obj T ≅ SheafOfModules.unit Y.ringCatSheaf)
    (hv : (Scheme.Modules.pullback f).map v ≫ e.hom = pullbackUnitComparison f) :
    (Scheme.Modules.pullback f).map (actualModuleTwistBasisInsertion M T v) ≫
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M T ≫
      schemeModuleTensorMap (𝟙 ((Scheme.Modules.pullback f).obj M)) e.hom ≫
      (schemeModuleTensorUnitRightIso ((Scheme.Modules.pullback f).obj M)).hom =
        𝟙 ((Scheme.Modules.pullback f).obj M) := by
  let P := Scheme.Modules.pullback f
  let O := SheafOfModules.unit X.ringCatSheaf
  let r := schemeModuleTensorUnitRightIso M
  let s := schemeModuleTensorUnitRightIso (P.obj M)
  have hn : P.map (schemeModuleTensorMap (𝟙 M) v) ≫
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M T =
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M O ≫
        schemeModuleTensorMap (𝟙 (P.obj M)) (P.map v) := by
    exact (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_naturality
      f (𝟙 M) v).trans
        (congrArg (fun a =>
          cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M O ≫
            schemeModuleTensorMap a (P.map v)) (P.map_id M))
  change P.map (r.inv ≫ schemeModuleTensorMap (𝟙 M) v) ≫
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M T ≫
      schemeModuleTensorMap (𝟙 (P.obj M)) e.hom ≫ s.hom = _
  calc
    _ = P.map r.inv ≫
        (P.map (schemeModuleTensorMap (𝟙 M) v) ≫
          cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M T) ≫
          schemeModuleTensorMap (𝟙 (P.obj M)) e.hom ≫ s.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = P.map r.inv ≫
        cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M O ≫
          schemeModuleTensorMap (𝟙 (P.obj M)) (P.map v) ≫
          schemeModuleTensorMap (𝟙 (P.obj M)) e.hom ≫ s.hom := by
      rw [hn]
      simp only [Category.assoc]
    _ = P.map r.inv ≫
        cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M O ≫
          schemeModuleTensorMap (𝟙 (P.obj M)) (P.map v ≫ e.hom) ≫ s.hom := by
      rw [← Category.assoc (schemeModuleTensorMap (𝟙 (P.obj M)) (P.map v)),
        schemeModuleTensorMap_comp, Category.id_comp]
    _ = P.map r.inv ≫ P.map r.hom := by
      rw [hv, cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_unit_right]
    _ = _ := by
      rw [← P.map_comp, r.inv_hom_id, P.map_id]

lemma actualPositiveTwistBasisInsertion_pullback_eq_inverse
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    {Y : Scheme.{u}} (f : Y ⟶ scheme I) (M : (scheme I).Modules)
    (m : ℕ)
    (v : SheafOfModules.unit (scheme I).ringCatSheaf ⟶ positiveSheafOfModules (grading I) m)
    (e : (Scheme.Modules.pullback f).obj (positiveSheafOfModules (grading I) m) ≅
      SheafOfModules.unit Y.ringCatSheaf)
    (hv : (Scheme.Modules.pullback f).map v ≫ e.hom = pullbackUnitComparison f) :
    (Scheme.Modules.pullback f).map
        (actualModuleTwistBasisInsertion M (positiveSheafOfModules (grading I) m) v) =
      (actualPositiveTwistPullbackTensorIso I f M m ≪≫
        schemeModuleTensorMapIso (Iso.refl ((Scheme.Modules.pullback f).obj M)) e ≪≫
          schemeModuleTensorUnitRightIso ((Scheme.Modules.pullback f).obj M)).inv := by
  let C := actualPositiveTwistPullbackTensorIso I f M m ≪≫
    schemeModuleTensorMapIso (Iso.refl ((Scheme.Modules.pullback f).obj M)) e ≪≫
      schemeModuleTensorUnitRightIso ((Scheme.Modules.pullback f).obj M)
  apply (cancel_mono C.hom).1
  have h := actualModuleTwistBasisInsertion_pullback_contract f M
    (positiveSheafOfModules (grading I) m) v e hv
  change _ ≫ C.hom = C.inv ≫ C.hom
  rw [C.inv_hom_id]
  exact h

lemma actualPositiveTwistBasisInsertion_chart_map
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    {Y : Scheme.{u}} (f : Y ⟶ scheme I) (M : (scheme I).Modules)
    (N : Y.Modules) (m : ℕ)
    (v : SheafOfModules.unit (scheme I).ringCatSheaf ⟶ positiveSheafOfModules (grading I) m)
    (eT : (Scheme.Modules.pullback f).obj (positiveSheafOfModules (grading I) m) ≅
      SheafOfModules.unit Y.ringCatSheaf)
    (hv : (Scheme.Modules.pullback f).map v ≫ eT.hom = pullbackUnitComparison f)
    (eM : (Scheme.Modules.pullback f).obj M ≅ N) :
    (Scheme.Modules.pullback f).map
        (actualModuleTwistBasisInsertion M (positiveSheafOfModules (grading I) m) v) ≫
      (actualPositiveTwistPullbackTensorIso I f M m ≪≫
        schemeModuleTensorMapIso eM eT ≪≫ schemeModuleTensorUnitRightIso N).hom = eM.hom := by
  let P := Scheme.Modules.pullback f
  have hTensor : schemeModuleTensorMap eM.hom eT.hom ≫
      (schemeModuleTensorUnitRightIso N).hom =
      schemeModuleTensorMap (𝟙 (P.obj M)) eT.hom ≫
        (schemeModuleTensorUnitRightIso (P.obj M)).hom ≫ eM.hom := by
    calc
      _ = (schemeModuleTensorMap (𝟙 (P.obj M)) eT.hom ≫
          schemeModuleTensorMap eM.hom (𝟙 (SheafOfModules.unit Y.ringCatSheaf))) ≫
          (schemeModuleTensorUnitRightIso N).hom := by
        rw [schemeModuleTensorMap_comp, Category.id_comp, Category.comp_id]
      _ = _ := by
        rw [Category.assoc,
          cubicClosedPointSerreFiniteZeroResidual_tensorUnitRightIso_naturality]
  change P.map (actualModuleTwistBasisInsertion M (positiveSheafOfModules (grading I) m) v) ≫
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
      (positiveSheafOfModules (grading I) m) ≫
      schemeModuleTensorMap eM.hom eT.hom ≫ (schemeModuleTensorUnitRightIso N).hom = _
  rw [hTensor]
  calc
    _ = (P.map (actualModuleTwistBasisInsertion M (positiveSheafOfModules (grading I) m) v) ≫
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
        (positiveSheafOfModules (grading I) m) ≫
        schemeModuleTensorMap (𝟙 (P.obj M)) eT.hom ≫
        (schemeModuleTensorUnitRightIso (P.obj M)).hom) ≫ eM.hom := by
      simp only [Category.assoc]
    _ = _ := by
      rw [actualModuleTwistBasisInsertion_pullback_contract f M _ v eT hv,
        Category.id_comp]

end PfaffianDescent
