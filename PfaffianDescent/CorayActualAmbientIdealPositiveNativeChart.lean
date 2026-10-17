import PfaffianDescent.CorayActualAmbientPositivePullbackTensorIso
import PfaffianDescent.CorayActualHomogeneousAmbientChartIdealTilde
import PfaffianDescent.ActualIdealTwistRestrictionInclusion
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! Canonical native chart identification of the ACTUAL ideal tensored with
O(m), retaining its actual inclusion into O(m). SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
open BundleSectionZeroLocus IdealSheafDataModule MonoidalCategory
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem sheafTensor_unit_unitors {X : Scheme.{u}} :
    (schemeModuleTensorUnitRightIso (SheafOfModules.unit X.ringCatSheaf)).hom =
      (schemeModuleTensorUnitLeftIso (SheafOfModules.unit X.ringCatSheaf)).hom := by
  let O := SheafOfModules.unit X.ringCatSheaf
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let U : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := O.val
  letI : MonoidalCategory (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.monoidalCategory
  change F.map (ρ_ U).hom ≫ adj.counit.app O =
    F.map (λ_ U).hom ≫ adj.counit.app O
  exact congrArg (fun t => F.map t ≫ adj.counit.app O)
    (MonoidalCategory.unitors_equal (C := PresheafOfModules
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))).symm

private theorem actualTensorChartInclusion
    {X Y : Scheme.{u}} (f : X ⟶ Y) (J L : Y.Modules)
    (v : J ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (N : X.Modules) (a : (Scheme.Modules.pullback f).obj J ⟶ N)
    (b : (Scheme.Modules.pullback f).obj L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (w : N ⟶ SheafOfModules.unit X.ringCatSheaf)
    (ha : a ≫ w = (Scheme.Modules.pullback f).map v ≫ pullbackUnitComparison f) :
    (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f J L ≫
      schemeModuleTensorMap a b ≫ (schemeModuleTensorUnitRightIso N).hom) ≫ w =
    (Scheme.Modules.pullback f).map
      (schemeModuleTensorMap v (𝟙 L) ≫ (schemeModuleTensorUnitLeftIso L).hom) ≫ b := by
  let P : Y.Modules ⥤ X.Modules := Scheme.Modules.pullback f
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let PL : X.Modules := P.obj L
  let TJ : X.Modules := schemeModuleTensor (P.obj J) PL
  let TN : X.Modules := schemeModuleTensor N O
  let TO : X.Modules := schemeModuleTensor O O
  let TP : X.Modules := schemeModuleTensor (P.obj OY) PL
  let TL : X.Modules := schemeModuleTensor O PL
  let c : P.obj (schemeModuleTensor J L) ⟶ TJ :=
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f J L
  let cO : P.obj (schemeModuleTensor OY L) ⟶ TP :=
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f OY L
  let u : P.obj OY ⟶ O := pullbackUnitComparison f
  let t : TJ ⟶ TN := schemeModuleTensorMap a b
  let tw : TN ⟶ TO := schemeModuleTensorMap w (𝟙 O)
  let tv : TJ ⟶ TP := schemeModuleTensorMap (P.map v) (𝟙 PL)
  let tb : TP ⟶ TO := schemeModuleTensorMap u b
  let tu : TP ⟶ TL := schemeModuleTensorMap u (𝟙 PL)
  let tl : TL ⟶ TO := schemeModuleTensorMap (𝟙 O) b
  let rN : TN ⟶ N := (schemeModuleTensorUnitRightIso N).hom
  let rO : TO ⟶ O := (schemeModuleTensorUnitRightIso O).hom
  let lO : TO ⟶ O := (schemeModuleTensorUnitLeftIso O).hom
  let lPL : TL ⟶ PL := (schemeModuleTensorUnitLeftIso PL).hom
  let s : P.obj (schemeModuleTensor J L) ⟶ P.obj (schemeModuleTensor OY L) :=
    P.map (schemeModuleTensorMap v (𝟙 L))
  let p : P.obj (schemeModuleTensor OY L) ⟶ PL :=
    P.map (schemeModuleTensorUnitLeftIso L).hom
  have hr : tw ≫ rO = rN ≫ w :=
    cubicClosedPointSerreFiniteZeroResidual_tensorUnitRightIso_naturality w
  have hn : s ≫ cO = c ≫ tv :=
    (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_naturality f v (𝟙 L)).trans
      (congrArg (fun z : PL ⟶ PL => c ≫ schemeModuleTensorMap (P.map v) z)
        (P.map_id L))
  have hs₁ : t ≫ tw = schemeModuleTensorMap (a ≫ w) b :=
    (schemeModuleTensorMap_comp a b w (𝟙 O)).trans
      (congrArg (fun z : PL ⟶ O => schemeModuleTensorMap (a ≫ w) z)
        (Category.comp_id b))
  have hs₂ : tv ≫ tb = schemeModuleTensorMap (P.map v ≫ u) b :=
    (schemeModuleTensorMap_comp (P.map v) (𝟙 PL) u b).trans
      (congrArg (fun z : PL ⟶ O => schemeModuleTensorMap (P.map v ≫ u) z)
        (Category.id_comp b))
  have hs₃ : tu ≫ tl = tb :=
    (schemeModuleTensorMap_comp u (𝟙 PL) (𝟙 O) b).trans
      (congrArg₂ (fun (z : P.obj OY ⟶ O) (z' : PL ⟶ O) =>
        schemeModuleTensorMap z z') (Category.comp_id u) (Category.id_comp b))
  have ht : t ≫ tw = tv ≫ tb :=
    hs₁.trans ((congrArg (fun z : P.obj J ⟶ O => schemeModuleTensorMap z b) ha).trans
      hs₂.symm)
  have hl : tl ≫ lO = lPL ≫ b := schemeModuleTensorUnitLeftIso_naturality b
  have hu : cO ≫ tu ≫ lPL = p := actualPullbackTensorMap_unit_left f L
  have hrl : rO = lO := sheafTensor_unit_unitors (X := X)
  have huB : cO ≫ tb ≫ rO = p ≫ b := by
    calc
      cO ≫ tb ≫ rO = cO ≫ tb ≫ lO :=
        congrArg (fun z : TO ⟶ O => cO ≫ tb ≫ z) hrl
      _ = cO ≫ (tu ≫ tl) ≫ lO :=
        congrArg (fun z : TP ⟶ TO => cO ≫ z ≫ lO) hs₃.symm
      _ = cO ≫ tu ≫ (tl ≫ lO) :=
        congrArg (fun z : TP ⟶ O => cO ≫ z) (Category.assoc tu tl lO)
      _ = cO ≫ tu ≫ (lPL ≫ b) :=
        congrArg (fun z : TL ⟶ O => cO ≫ tu ≫ z) hl
      _ = (cO ≫ tu ≫ lPL) ≫ b :=
        ((Category.assoc cO (tu ≫ lPL) b).trans
          (congrArg (fun z : TP ⟶ O => cO ≫ z) (Category.assoc tu lPL b))).symm
      _ = p ≫ b := congrArg (fun z : P.obj (schemeModuleTensor OY L) ⟶ PL => z ≫ b) hu
  change (c ≫ t ≫ rN) ≫ w =
    P.map (schemeModuleTensorMap v (𝟙 L) ≫ (schemeModuleTensorUnitLeftIso L).hom) ≫ b
  calc
    (c ≫ t ≫ rN) ≫ w = c ≫ t ≫ (rN ≫ w) :=
      (Category.assoc c (t ≫ rN) w).trans
        (congrArg (fun z : TJ ⟶ O => c ≫ z) (Category.assoc t rN w))
    _ = c ≫ t ≫ (tw ≫ rO) :=
      congrArg (fun z : TN ⟶ O => c ≫ t ≫ z) hr.symm
    _ = c ≫ (t ≫ tw) ≫ rO :=
      congrArg (fun z : TJ ⟶ O => c ≫ z) (Category.assoc t tw rO).symm
    _ = c ≫ (tv ≫ tb) ≫ rO :=
      congrArg (fun z : TJ ⟶ TO => c ≫ z ≫ rO) ht
    _ = (c ≫ tv) ≫ tb ≫ rO :=
      (congrArg (fun z : TJ ⟶ O => c ≫ z) (Category.assoc tv tb rO)).trans
        (Category.assoc c tv (tb ≫ rO)).symm
    _ = (s ≫ cO) ≫ tb ≫ rO :=
      congrArg (fun z : P.obj (schemeModuleTensor J L) ⟶ TP => z ≫ tb ≫ rO) hn.symm
    _ = s ≫ (cO ≫ tb ≫ rO) := Category.assoc s cO (tb ≫ rO)
    _ = s ≫ (p ≫ b) :=
      congrArg (fun z : P.obj (schemeModuleTensor OY L) ⟶ O => s ≫ z) huB
    _ = (s ≫ p) ≫ b := (Category.assoc s p b).symm
    _ = P.map (schemeModuleTensorMap v (𝟙 L) ≫ (schemeModuleTensorUnitLeftIso L).hom) ≫ b :=
      congrArg (fun z : P.obj (schemeModuleTensor J L) ⟶ PL => z ≫ b)
        (P.map_comp (schemeModuleTensorMap v (𝟙 L)) (schemeModuleTensorUnitLeftIso L).hom).symm

/-- Native chart frame of the ACTUAL closed-immersion ideal tensor O(m).
The source remains the whole original ideal, including its nilpotents. -/
def actualAmbientHomogeneousIdealPositiveNativeChartIso
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :
    (Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).obj
        (schemeModuleTensor (closedImmersionModule (quotientProjMap I))
          (positiveSheafOfModules PS m)) ≅
    (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).obj
      (ModuleCat.of (HomogeneousLocalization.Away PS (X j))
        (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j))) := by
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let J := closedImmersionModule (quotientProjMap I)
  let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
  let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  exact actualAmbientPositiveTwistPullbackTensorIso (K := K) q J m ≪≫
    schemeModuleTensorMapIso a.symm b ≪≫ schemeModuleTensorUnitRightIso _

/-- Bounded cut of the actual hom-to-unit law, with the original tildeSelf. -/
private theorem actualNativeChartHomToUnit001
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let P := Scheme.Modules.pullback q
    let B := HomogeneousLocalization.Away PS (X j)
    let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
    let w := (tilde.functor (CommRingCat.of B)).map
      (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
        (tildeSelf (R := CommRingCat.of B)).hom
    a.hom ≫ P.map (closedImmersionModuleToUnit (quotientProjMap I)) ≫
      pullbackUnitComparison q = w := by
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback q
  let B := HomogeneousLocalization.Away PS (X j)
  let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
  let w := (tilde.functor (CommRingCat.of B)).map
    (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
      (tildeSelf (R := CommRingCat.of B)).hom
  simpa only [PfaffianDescent.affineGlobalSectionsUnitTildeIso_eq_tildeSelf] using
    actualAmbientHomogeneousQuotientChartIdealTildeIso_hom_toUnit I j

/-- Bounded inverse cut; no actual inclusion hypothesis is supplied. -/
private theorem actualNativeChartInvToUnit001
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let P := Scheme.Modules.pullback q
    let B := HomogeneousLocalization.Away PS (X j)
    let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
    let w := (tilde.functor (CommRingCat.of B)).map
      (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
        (tildeSelf (R := CommRingCat.of B)).hom
    a.inv ≫ w = P.map (closedImmersionModuleToUnit (quotientProjMap I)) ≫
      pullbackUnitComparison q := by
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback q
  let B := HomogeneousLocalization.Away PS (X j)
  let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
  let w := (tilde.functor (CommRingCat.of B)).map
    (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
      (tildeSelf (R := CommRingCat.of B)).hom
  exact (a.inv_comp_eq).mpr (actualNativeChartHomToUnit001 I j).symm

/-- The checked generic tensor law applied to the original actual native data. -/
private theorem actualNativeChartTensorInclusion001
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :
    let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let P := Scheme.Modules.pullback q
    let J := closedImmersionModule (quotientProjMap I)
    let L := positiveSheafOfModules PS m
    let B := HomogeneousLocalization.Away PS (X j)
    let N := (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
    let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
    let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
    let w := (tilde.functor (CommRingCat.of B)).map
      (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
        (tildeSelf (R := CommRingCat.of B)).hom
    (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q J L ≫
      schemeModuleTensorMap a.inv b.hom ≫ (schemeModuleTensorUnitRightIso N).hom) ≫ w =
      P.map (actualIdealTwistInclusion (quotientProjMap I) L) ≫ b.hom := by
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback q
  let J := closedImmersionModule (quotientProjMap I)
  let L := positiveSheafOfModules PS m
  let B := HomogeneousLocalization.Away PS (X j)
  let N := (tilde.functor (CommRingCat.of B)).obj
    (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
  let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
  let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  let w := (tilde.functor (CommRingCat.of B)).map
    (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
      (tildeSelf (R := CommRingCat.of B)).hom
  exact actualTensorChartInclusion q J L (closedImmersionModuleToUnit (quotientProjMap I))
    N a.inv b.hom w (actualNativeChartInvToUnit001 I j)

/-- Abstract composition projection; actual Iso values stay opaque. -/
private theorem nativeIsoThreeHom002
    {Cat002 : Type*} [Category Cat002] {Obj0 Obj1 Obj2 Obj3 : Cat002}
    (a : Obj0 ≅ Obj1) (b : Obj1 ≅ Obj2) (c : Obj2 ≅ Obj3) :
    (a ≪≫ b ≪≫ c).hom = a.hom ≫ b.hom ≫ c.hom := rfl

/-- Projection before any native chart objects or maps are supplied. -/
private theorem nativeSchemeTensorIsoHom002
    {Y : Scheme.{u}} {M₁ M₂ N₁ N₂ : Y.Modules}
    (a : M₁ ≅ M₂) (b : N₁ ≅ N₂) :
    (schemeModuleTensorMapIso a b).hom = schemeModuleTensorMap a.hom b.hom := rfl

/-- Projection of the original asIso while f and M remain abstract. -/
private theorem nativePositiveTensorIsoHom002
    {Y : Scheme.{u}} (f : Y ⟶ Proj PS) (M : (Proj PS).Modules) (m : ℕ) :
    (actualAmbientPositiveTwistPullbackTensorIso (K := K) f M m).hom =
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
        (positiveSheafOfModules PS m) := rfl

/-- Actual first component, applied after generic projection was checked. -/
private theorem actualNativeChartFirstIsoHom002
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :
    let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let P := Scheme.Modules.pullback q
    let J := closedImmersionModule (quotientProjMap I)
    let L := positiveSheafOfModules PS m
    let B := HomogeneousLocalization.Away PS (X j)
    let N := (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
    let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
    let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
    let w := (tilde.functor (CommRingCat.of B)).map
      (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
        (tildeSelf (R := CommRingCat.of B)).hom
    (actualAmbientPositiveTwistPullbackTensorIso (K := K) q J m).hom =
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q J L := by
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback q
  let J := closedImmersionModule (quotientProjMap I)
  let L := positiveSheafOfModules PS m
  let B := HomogeneousLocalization.Away PS (X j)
  let N := (tilde.functor (CommRingCat.of B)).obj
    (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
  let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
  let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  let w := (tilde.functor (CommRingCat.of B)).map
    (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
      (tildeSelf (R := CommRingCat.of B)).hom
  exact nativePositiveTensorIsoHom002 q J m

/-- Actual tensor-factor component, applied after generic projection. -/
private theorem actualNativeChartSecondIsoHom002
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :
    let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let P := Scheme.Modules.pullback q
    let J := closedImmersionModule (quotientProjMap I)
    let L := positiveSheafOfModules PS m
    let B := HomogeneousLocalization.Away PS (X j)
    let N := (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
    let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
    let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
    let w := (tilde.functor (CommRingCat.of B)).map
      (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
        (tildeSelf (R := CommRingCat.of B)).hom
    (schemeModuleTensorMapIso a.symm b).hom = schemeModuleTensorMap a.inv b.hom := by
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback q
  let J := closedImmersionModule (quotientProjMap I)
  let L := positiveSheafOfModules PS m
  let B := HomogeneousLocalization.Away PS (X j)
  let N := (tilde.functor (CommRingCat.of B)).obj
    (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
  let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
  let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  let w := (tilde.functor (CommRingCat.of B)).map
    (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
      (tildeSelf (R := CommRingCat.of B)).hom
  exact nativeSchemeTensorIsoHom002 a.symm b

/-- WHOLE original Iso identity; no field or component is replaced. -/
private theorem actualNativeChartOriginalWholeIso002
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :
    let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let P := Scheme.Modules.pullback q
    let J := closedImmersionModule (quotientProjMap I)
    let L := positiveSheafOfModules PS m
    let B := HomogeneousLocalization.Away PS (X j)
    let N := (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
    let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
    let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
    let w := (tilde.functor (CommRingCat.of B)).map
      (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
        (tildeSelf (R := CommRingCat.of B)).hom
    actualAmbientHomogeneousIdealPositiveNativeChartIso I j m =
      actualAmbientPositiveTwistPullbackTensorIso (K := K) q J m ≪≫
        schemeModuleTensorMapIso a.symm b ≪≫ schemeModuleTensorUnitRightIso N := by
  rfl

/-- Fix the literal Scheme.Modules category and all four actual objects,
before supplying any of the original concrete Iso values. -/
private def actualNativeChartThreeHomObjects004
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback q
  let J := closedImmersionModule (quotientProjMap I)
  let L := positiveSheafOfModules PS m
  let B := HomogeneousLocalization.Away PS (X j)
  let Y := Spec (CommRingCat.of B)
  let N := (tilde.functor (CommRingCat.of B)).obj
    (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
  @nativeIsoThreeHom002 Y.Modules (inferInstance : Category Y.Modules)
    (P.obj (schemeModuleTensor J L))
    (schemeModuleTensor (P.obj J) (P.obj L))
    (schemeModuleTensor N (SheafOfModules.unit Y.ringCatSheaf)) N

/-- Supply only the original positive-tensor pullback Iso. Its output type
is inferred from the exact previously specialized theorem consumer. -/
private def actualNativeChartThreeHomFirst004
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let J := closedImmersionModule (quotientProjMap I)
  actualNativeChartThreeHomObjects004 (K := K) I j m
    (actualAmbientPositiveTwistPullbackTensorIso (K := K) q J m)

/-- Supply only the original tensor-factor Iso to the exact consumer. -/
private def actualNativeChartThreeHomSecond004
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
  let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  actualNativeChartThreeHomFirst004 (K := K) I j m (schemeModuleTensorMapIso a.symm b)

/-- Supply the original right unitor. This is the exact inferred proof
produced by the fully specialized original abstract projection theorem. -/
private def actualNativeChartThreeHomComplete004
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  let B := HomogeneousLocalization.Away PS (X j)
  let N := (tilde.functor (CommRingCat.of B)).obj
    (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
  actualNativeChartThreeHomSecond004 (K := K) I j m (schemeModuleTensorUnitRightIso N)

/-- Insert hom replacements and the WHOLE Iso identity while all category
objects, Iso values and morphisms are abstract. This avoids a concrete
three-Iso-hom result conversion before simplifying the two components. -/
private theorem nativeOriginalIsoNormalHom005
    {Cat005 : Type*} [Category Cat005] {Obj0 Obj1 Obj2 Obj3 : Cat005}
    (e : Obj0 ≅ Obj3) (s : Obj0 ≅ Obj1) (t : Obj1 ≅ Obj2) (r : Obj2 ≅ Obj3)
    (v : Obj0 ⟶ Obj1) (w : Obj1 ⟶ Obj2)
    (hs : s.hom = v) (ht : t.hom = w) (he : e = s ≪≫ t ≪≫ r) :
    e.hom = v ≫ w ≫ r.hom := by
  exact (congrArg (fun z : Obj0 ≅ Obj3 => z.hom) he).trans
    ((nativeIsoThreeHom002 s t r).trans
      (congrArg₂ (fun x y => x ≫ y ≫ r.hom) hs ht))

/-- Exact actual category and endpoints; all remaining inputs are inferred
from the previously checked abstract normal-hom consumer. -/
private def actualNativeChartNormalObjects005
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback q
  let J := closedImmersionModule (quotientProjMap I)
  let L := positiveSheafOfModules PS m
  let B := HomogeneousLocalization.Away PS (X j)
  let Y := Spec (CommRingCat.of B)
  let N := (tilde.functor (CommRingCat.of B)).obj
    (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
  @nativeOriginalIsoNormalHom005 Y.Modules (inferInstance : Category Y.Modules)
    (P.obj (schemeModuleTensor J L))
    (schemeModuleTensor (P.obj J) (P.obj L))
    (schemeModuleTensor N (SheafOfModules.unit Y.ringCatSheaf)) N

/-- Supply the unchanged original WHOLE Iso. -/
private def actualNativeChartNormalOriginalIso005
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  actualNativeChartNormalObjects005 (K := K) I j m
    (actualAmbientHomogeneousIdealPositiveNativeChartIso I j m)

/-- Supply the unchanged original first Iso. -/
private def actualNativeChartNormalFirstIso005
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let J := closedImmersionModule (quotientProjMap I)
  actualNativeChartNormalOriginalIso005 (K := K) I j m
    (actualAmbientPositiveTwistPullbackTensorIso (K := K) q J m)

/-- Supply the unchanged tensor-factor Iso. -/
private def actualNativeChartNormalSecondIso005
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
  let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  actualNativeChartNormalFirstIso005 (K := K) I j m
    (schemeModuleTensorMapIso a.symm b)

/-- Supply the unchanged actual right unitor. -/
private def actualNativeChartNormalUnitor005
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  let B := HomogeneousLocalization.Away PS (X j)
  let N := (tilde.functor (CommRingCat.of B)).obj
    (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
  actualNativeChartNormalSecondIso005 (K := K) I j m
    (schemeModuleTensorUnitRightIso N)

/-- Supply the original tensor-pullback morphism. -/
private def actualNativeChartNormalFirstMap005
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let J := closedImmersionModule (quotientProjMap I)
  actualNativeChartNormalUnitor005 (K := K) I j m
    (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q J (positiveSheafOfModules PS m))

/-- Supply the original tensor-factor morphism. -/
private def actualNativeChartNormalSecondMap005
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
  let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  actualNativeChartNormalFirstMap005 (K := K) I j m
    (schemeModuleTensorMap a.inv b.hom)

/-- Insert the previously proved first hom law into its exact inferred consumer. -/
private def actualNativeChartNormalFirstLaw005
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  actualNativeChartNormalSecondMap005 (K := K) I j m
    (actualNativeChartFirstIsoHom002 I j m)

/-- Insert the previously proved second hom law into its exact inferred consumer. -/
private def actualNativeChartNormalSecondLaw005
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  actualNativeChartNormalFirstLaw005 (K := K) I j m
    (actualNativeChartSecondIsoHom002 I j m)

/-- Insert the unchanged original WHOLE Iso identity; the result law is inferred. -/
private def actualNativeChartNormalWholeLaw005
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :=
  actualNativeChartNormalSecondLaw005 (K := K) I j m
    (actualNativeChartOriginalWholeIso002 I j m)

/-- Only two separately checked hom equalities are substituted here. -/
private theorem actualNativeChartOriginalComponentsHom002
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :
    let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let P := Scheme.Modules.pullback q
    let J := closedImmersionModule (quotientProjMap I)
    let L := positiveSheafOfModules PS m
    let B := HomogeneousLocalization.Away PS (X j)
    let N := (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
    let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
    let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
    let w := (tilde.functor (CommRingCat.of B)).map
      (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
        (tildeSelf (R := CommRingCat.of B)).hom
    (actualAmbientPositiveTwistPullbackTensorIso (K := K) q J m).hom ≫
        (schemeModuleTensorMapIso a.symm b).hom ≫ (schemeModuleTensorUnitRightIso N).hom =
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q J L ≫
        schemeModuleTensorMap a.inv b.hom ≫ (schemeModuleTensorUnitRightIso N).hom := by
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback q
  let J := closedImmersionModule (quotientProjMap I)
  let L := positiveSheafOfModules PS m
  let B := HomogeneousLocalization.Away PS (X j)
  let N := (tilde.functor (CommRingCat.of B)).obj
    (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
  let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
  let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  let w := (tilde.functor (CommRingCat.of B)).map
    (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
      (tildeSelf (R := CommRingCat.of B)).hom
  exact congrArg₂ (fun x y => x ≫ y ≫ (schemeModuleTensorUnitRightIso N).hom)
    (actualNativeChartFirstIsoHom002 I j m) (actualNativeChartSecondIsoHom002 I j m)

/-- Only the hom field of the unchanged original WHOLE Iso is unfolded here. -/
private theorem actualNativeChartOriginalIsoHom001
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :
    let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let P := Scheme.Modules.pullback q
    let J := closedImmersionModule (quotientProjMap I)
    let L := positiveSheafOfModules PS m
    let B := HomogeneousLocalization.Away PS (X j)
    let N := (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
    let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
    let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
    let w := (tilde.functor (CommRingCat.of B)).map
      (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
        (tildeSelf (R := CommRingCat.of B)).hom
    (actualAmbientHomogeneousIdealPositiveNativeChartIso I j m).hom =
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q J L ≫
        schemeModuleTensorMap a.inv b.hom ≫ (schemeModuleTensorUnitRightIso N).hom := by
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback q
  let J := closedImmersionModule (quotientProjMap I)
  let L := positiveSheafOfModules PS m
  let B := HomogeneousLocalization.Away PS (X j)
  let N := (tilde.functor (CommRingCat.of B)).obj
    (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
  let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
  let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  let w := (tilde.functor (CommRingCat.of B)).map
    (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
      (tildeSelf (R := CommRingCat.of B)).hom
  exact actualNativeChartNormalWholeLaw005 (K := K) I j m

/-- The constructed native chart frame commutes with the literal ideal-twist
inclusion into O(m). It is not merely an abstract isomorphism of objects. -/
theorem actualAmbientHomogeneousIdealPositiveNativeChartIso_inclusion
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :
    (actualAmbientHomogeneousIdealPositiveNativeChartIso I j m).hom ≫
      (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).map
        (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
      (tildeSelf (R := CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).hom =
    (Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).map
        (actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m)) ≫
      (actualAmbientPositiveNativeChartUnitIso (K := K) j m).hom := by
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback q
  let J := closedImmersionModule (quotientProjMap I)
  let L := positiveSheafOfModules PS m
  let B := HomogeneousLocalization.Away PS (X j)
  let N := (tilde.functor (CommRingCat.of B)).obj
    (ModuleCat.of B (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))
  let a := actualAmbientHomogeneousQuotientChartIdealTildeIso (K := K) I j
  let b := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  let w := (tilde.functor (CommRingCat.of B)).map
    (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
      (tildeSelf (R := CommRingCat.of B)).hom
  exact (congrArg (fun z => z ≫ w) (actualNativeChartOriginalIsoHom001 I j m)).trans
    (actualNativeChartTensorInclusion001 I j m)

end PfaffianDescent.Coray
