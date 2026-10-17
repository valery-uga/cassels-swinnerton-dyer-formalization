import PfaffianDescent.ActualPointOpenRestrictAdjunctionUnit
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealOpenRestriction

/-! A genuine chosen frame of the ACTUAL pullback fiber, together with
its compatibility with the SAME pullback/pushforward adjunction unit.
The choice trivializes the intrinsic fiber; it never replaces that
fiber in the canonical map. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open BundleSectionZeroLocus IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual unit adjunction square, from the native definition of the
pullback-unit comparison. No desired fiber comparison is supplied. -/
theorem schemeModulePullbackUnitComparison_unit_square
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.pushforward f).map (pullbackUnitComparison f) =
        closedImmersionUnitToPushforwardUnit f := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  change (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (pullbackUnitComparison f) = _
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom

/-- Actual frame of the pulled-back fiber, internally obtained from a
chart on the original scheme and the genuine unit pullback Iso. -/
def schemeModuleFiberFrameIso
    {X U Y : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (j : Y ⟶ U) (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor f).obj T ≅
      SheafOfModules.unit U.ringCatSheaf) :
    (Scheme.Modules.pullback (j ≫ f)).obj T ≅
      SheafOfModules.unit Y.ringCatSheaf := by
  letI : IsIso (pullbackUnitComparison j) := isIso_pullbackUnitComparison j
  exact cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso f j T ≪≫
    (Scheme.Modules.pullback j).mapIso eT ≪≫ asIso (pullbackUnitComparison j)

/-- In the chosen frame the SAME canonical adjunction unit is the
literal local quotient, preceded by actual open restriction. -/
theorem schemeModuleFiberFrameIso_adjunctionUnit
    {X U Y : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (j : Y ⟶ U) (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor f).obj T ≅
      SheafOfModules.unit U.ringCatSheaf) :
    (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)).unit.app T ≫
      (Scheme.Modules.pushforward (j ≫ f)).map
        (schemeModuleFiberFrameIso f j T eT).hom =
    (Scheme.Modules.restrictAdjunction f).unit.app T ≫
      (Scheme.Modules.pushforward f).map
        (eT.hom ≫ closedImmersionUnitToPushforwardUnit j) ≫
      (Scheme.Modules.pushforwardComp j f).hom.app
        (SheafOfModules.unit Y.ringCatSheaf) := by
  let R : X.Modules ⥤ U.Modules := Scheme.Modules.restrictFunctor f
  let Q : U.Modules ⥤ X.Modules := Scheme.Modules.pushforward f
  let P : U.Modules ⥤ Y.Modules := Scheme.Modules.pullback j
  let G : Y.Modules ⥤ U.Modules := Scheme.Modules.pushforward j
  let H : Y.Modules ⥤ X.Modules := Scheme.Modules.pushforward (j ≫ f)
  let A : P ⊣ G := Scheme.Modules.pullbackPushforwardAdjunction j
  let O : U.Modules := SheafOfModules.unit U.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let L := cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso f j T
  let b : P.obj (R.obj T) ⟶ OY :=
    P.map eT.hom ≫ pullbackUnitComparison j
  have hUnit : eT.hom ≫ A.unit.app O =
      A.unit.app (R.obj T) ≫ G.map (P.map eT.hom) := by
    have h := A.unit.naturality eT.hom
    change eT.hom ≫ A.unit.app O =
      A.unit.app (R.obj T) ≫ G.map (P.map eT.hom) at h
    exact h
  have hb : A.unit.app (R.obj T) ≫ G.map b =
      eT.hom ≫ closedImmersionUnitToPushforwardUnit j := by
    dsimp only [b]
    rw [G.map_comp, ← Category.assoc, ← hUnit, Category.assoc]
    rw [schemeModulePullbackUnitComparison_unit_square]
  have hn := (Scheme.Modules.pushforwardComp j f).hom.naturality b
  change Q.map (G.map b) ≫ (Scheme.Modules.pushforwardComp j f).hom.app _ =
    (Scheme.Modules.pushforwardComp j f).hom.app _ ≫ H.map b at hn
  have hu := actualPointOpenRestrictAdjunctionUnit f j T
  change _ ≫ H.map (L.hom ≫ b) = _
  calc
    _ = ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)).unit.app T ≫
        H.map L.hom) ≫ H.map b := by
      simp only [H.map_comp, Category.assoc]
    _ = ((Scheme.Modules.restrictAdjunction f).unit.app T ≫
        Q.map (A.unit.app (R.obj T)) ≫
        (Scheme.Modules.pushforwardComp j f).hom.app (P.obj (R.obj T))) ≫ H.map b :=
      congrArg (· ≫ H.map b) hu
    _ = (Scheme.Modules.restrictAdjunction f).unit.app T ≫
        Q.map (A.unit.app (R.obj T)) ≫
        Q.map (G.map b) ≫ (Scheme.Modules.pushforwardComp j f).hom.app _ := by
      simp only [Category.assoc]
      rw [← hn]
    _ = (Scheme.Modules.restrictAdjunction f).unit.app T ≫
        Q.map (A.unit.app (R.obj T) ≫ G.map b) ≫
        (Scheme.Modules.pushforwardComp j f).hom.app _ := by
      simp only [Q.map_comp, Category.assoc]
    _ = _ := by rw [hb]

/-- After restricting to the actual open, the actual fiber-unit square
is literally the original closed-chart quotient composed with the
chosen chart. This is the precise map coherence needed for the
canonical GLOBAL cokernel, rather than an arbitrary fiber Iso. -/
theorem schemeModuleFiberFrameIso_restrict_unit_square
    {X U Y : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (j : Y ⟶ U) (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor f).obj T ≅
      SheafOfModules.unit U.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)).unit.app T) ≫
      (Scheme.Modules.restrictFunctor f).map
        ((Scheme.Modules.pushforward (j ≫ f)).map
          (schemeModuleFiberFrameIso f j T eT).hom) ≫
      (restrictPushforwardUnitFactorThroughOpenIso j f).hom =
    eT.hom ≫ closedImmersionUnitToPushforwardUnit j := by
  let R : X.Modules ⥤ U.Modules := Scheme.Modules.restrictFunctor f
  let Q : U.Modules ⥤ X.Modules := Scheme.Modules.pushforward f
  let G : Y.Modules ⥤ U.Modules := Scheme.Modules.pushforward j
  let H : Y.Modules ⥤ X.Modules := Scheme.Modules.pushforward (j ≫ f)
  let A : R ⊣ Q := Scheme.Modules.restrictAdjunction f
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let B : U.Modules := G.obj OY
  let V : X.Modules := H.obj OY
  let c : Q.obj B ≅ V := (Scheme.Modules.pushforwardComp j f).app OY
  let a : R.obj T ⟶ B := eT.hom ≫ closedImmersionUnitToPushforwardUnit j
  let t : T ⟶ V :=
    (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)).unit.app T ≫
      H.map (schemeModuleFiberFrameIso f j T eT).hom
  have hn : R.map (Q.map a) ≫ A.counit.app B = A.counit.app (R.obj T) ≫ a := by
    have h := A.counit.naturality a
    change R.map (Q.map a) ≫ A.counit.app B = A.counit.app (R.obj T) ≫ a at h
    exact h
  have ht : R.map (A.unit.app T) ≫ A.counit.app (R.obj T) = 𝟙 (R.obj T) :=
    A.left_triangle_components T
  have h : t = A.unit.app T ≫ Q.map a ≫ c.hom :=
    schemeModuleFiberFrameIso_adjunctionUnit f j T eT
  have hc : t ≫ c.inv = A.unit.app T ≫ Q.map a := by
    rw [h]
    simp only [Category.assoc, c.hom_inv_id, Category.comp_id]
  change R.map _ ≫ R.map _ ≫ R.map c.inv ≫ A.counit.app B = a
  calc
    _ = R.map (t ≫ c.inv) ≫ A.counit.app B := by
      simp only [t, H, R.map_comp, Category.assoc]
    _ = R.map (A.unit.app T ≫ Q.map a) ≫ A.counit.app B :=
      congrArg (fun b : T ⟶ Q.obj B => R.map b ≫ A.counit.app B) hc
    _ = R.map (A.unit.app T) ≫ A.counit.app (R.obj T) ≫ a := by
      rw [R.map_comp, Category.assoc, hn]
    _ = (R.map (A.unit.app T) ≫ A.counit.app (R.obj T)) ≫ a :=
      (Category.assoc _ _ _).symm
    _ = (𝟙 (R.obj T)) ≫ a :=
      congrArg (fun b : R.obj T ⟶ R.obj T => b ≫ a) ht
    _ = a := Category.id_comp a

end PfaffianDescent
