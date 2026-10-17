import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointRestrictSection
import Mathlib.CategoryTheory.Adjunction.Mates

/-! SOURCE ONLY, UNVERIFIED. Compatibility of the actual point/open pullback
comparison with the genuine adjunction units, including local sections. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem actualPointOpenRestrictAdjunctionUnit
    {X U Y : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (j : Y ⟶ U) (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)).unit.app M ≫
      (Scheme.Modules.pushforward (j ≫ f)).map
        (cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso f j M).hom =
    (Scheme.Modules.restrictAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          ((Scheme.Modules.restrictFunctor f).obj M)) ≫
      (Scheme.Modules.pushforwardComp j f).hom.app
        ((Scheme.Modules.pullback j).obj ((Scheme.Modules.restrictFunctor f).obj M)) := by
  let A := (Scheme.Modules.restrictFunctorIsoPullback f).app M
  let B := (Scheme.Modules.pullbackComp j f).app M
  let Af := Scheme.Modules.pullbackPushforwardAdjunction f
  let Aj := Scheme.Modules.pullbackPushforwardAdjunction j
  let Aq := Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)
  let Ar := Scheme.Modules.restrictAdjunction f
  have hRestrict : Af.unit.app M ≫ (Scheme.Modules.pushforward f).map A.inv =
      Ar.unit.app M := by
    have h := Adjunction.unit_leftAdjointUniq_hom_app Ar Af M
    change Ar.unit.app M ≫ (Scheme.Modules.pushforward f).map A.hom = Af.unit.app M at h
    rw [← h, Category.assoc, ← Functor.map_comp, A.hom_inv_id,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have hComp := unit_conjugateEquiv (Af.comp Aj) Aq
    (Scheme.Modules.pullbackComp j f).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hComp
  change (Af.comp Aj).unit.app M ≫
      (Scheme.Modules.pushforwardComp j f).hom.app _ =
    Aq.unit.app M ≫ (Scheme.Modules.pushforward (j ≫ f)).map B.inv at hComp
  have hNat := (Scheme.Modules.pushforwardComp j f).hom.naturality
    ((Scheme.Modules.pullback j).map A.inv)
  have hUnitNat := Aj.unit.naturality A.inv
  change A.inv ≫ Aj.unit.app _ =
    Aj.unit.app _ ≫ (Scheme.Modules.pushforward j).map
      ((Scheme.Modules.pullback j).map A.inv) at hUnitNat
  change Aq.unit.app M ≫ (Scheme.Modules.pushforward (j ≫ f)).map
      (B.inv ≫ (Scheme.Modules.pullback j).map A.inv) = _
  rw [Functor.map_comp, ← Category.assoc, ← hComp, Category.assoc]
  erw [← hNat]
  rw [Adjunction.comp_unit_app]
  change (Af.unit.app M ≫ (Scheme.Modules.pushforward f).map (Aj.unit.app _)) ≫
      ((Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pushforward j).map ((Scheme.Modules.pullback j).map A.inv)) ≫ _) = _
  have hInner :
      (Scheme.Modules.pushforward f).map
          (Aj.unit.app ((Scheme.Modules.pullback f).obj M)) ≫
        (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pushforward j).map
            ((Scheme.Modules.pullback j).map A.inv)) =
      (Scheme.Modules.pushforward f).map A.inv ≫
        (Scheme.Modules.pushforward f).map
          (Aj.unit.app ((Scheme.Modules.restrictFunctor f).obj M)) := by
    rw [← Functor.map_comp, ← hUnitNat, Functor.map_comp]
    rfl
  calc
    _ = Af.unit.app M ≫
        ((Scheme.Modules.pushforward f).map
          (Aj.unit.app ((Scheme.Modules.pullback f).obj M)) ≫
        (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pushforward j).map
            ((Scheme.Modules.pullback j).map A.inv))) ≫
        (Scheme.Modules.pushforwardComp j f).hom.app
          ((Scheme.Modules.pullback j).obj ((Scheme.Modules.restrictFunctor f).obj M)) := by
      simp only [Category.assoc]
    _ = Af.unit.app M ≫
        ((Scheme.Modules.pushforward f).map A.inv ≫
        (Scheme.Modules.pushforward f).map
          (Aj.unit.app ((Scheme.Modules.restrictFunctor f).obj M))) ≫
        (Scheme.Modules.pushforwardComp j f).hom.app
          ((Scheme.Modules.pullback j).obj ((Scheme.Modules.restrictFunctor f).obj M)) := by
      rw [hInner]
    _ = (Af.unit.app M ≫ (Scheme.Modules.pushforward f).map A.inv) ≫
        (Scheme.Modules.pushforward f).map
          (Aj.unit.app ((Scheme.Modules.restrictFunctor f).obj M)) ≫
        (Scheme.Modules.pushforwardComp j f).hom.app
          ((Scheme.Modules.pullback j).obj ((Scheme.Modules.restrictFunctor f).obj M)) := by
      simp only [Category.assoc]
    _ = _ := by rw [hRestrict]

theorem actualPointOpenRestrictAdjunctionHomEquiv
    {X U Y : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (j : Y ⟶ U) (M : X.Modules) (N : Y.Modules)
    (d : (Scheme.Modules.pullback j).obj ((Scheme.Modules.restrictFunctor f).obj M) ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)).homEquiv M N
      ((cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso f j M).hom ≫ d) =
    (Scheme.Modules.restrictAdjunction f).homEquiv M
      ((Scheme.Modules.pushforward j).obj N)
      ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
        ((Scheme.Modules.restrictFunctor f).obj M) N d) ≫
      (Scheme.Modules.pushforwardComp j f).hom.app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, actualPointOpenRestrictAdjunctionUnit]
  simp only [Category.assoc]
  rw [← (Scheme.Modules.pushforwardComp j f).hom.naturality d]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

end PfaffianDescent
