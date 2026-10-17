import PfaffianDescent.RelativeClosedImmersionIdealBaseChange
import PfaffianDescent.OpenPullbackMono

/-!
# Testing ideal-inclusion exactness on target opens

If the pulled-back ideal inclusion is monic after first restricting a
closed immersion to an open target chart, it is monic for the composite
map to the original target. This uses flatness of the open immersion
only; the map into that chart may be nonflat.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- If the canonical ideal base-change map is an isomorphism, the
pullback of the original ideal inclusion remains monic. -/
theorem closedImmersionIdealPullback_mono_of_baseChangeIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [IsIso (closedImmersionIdealBaseChangeHom f i)] :
    Mono ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) := by
  let P := Scheme.Modules.pullback f
  let m := IdealSheafDataModule.closedImmersionModuleToUnit i
  let e := closedImmersionIdealBaseChangeHom f i
  let n := IdealSheafDataModule.closedImmersionModuleToUnit (pullback.fst f i)
  let w := BundleSectionZeroLocus.pullbackUnitComparison f
  haveI : IsIso e := inferInstance
  have hn : Mono n := by
    change Mono (IdealSheafDataModule.idealModuleToUnit
      (pullback.fst f i).ker)
    infer_instance
  have h₁ : Mono (e ≫ n) := mono_comp' (IsIso.mono_of_iso e) hn
  have h₂ : Mono (P.map m ≫ w) := by
    rw [← closedImmersionIdealBaseChangeHom_toUnit f i]
    exact h₁
  letI : Mono (P.map m ≫ w) := h₂
  exact mono_of_mono_fac (f := w) (g := P.map m) rfl

theorem closedImmersionIdealPullback_mono_of_targetOpen
    {X U Y Z : Scheme.{u}}
    (g : X ⟶ U) (v : U ⟶ Y) [IsOpenImmersion v]
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (h : Mono ((Scheme.Modules.pullback g).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst v i)))) :
    Mono ((Scheme.Modules.pullback (g ≫ v)).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) := by
  let P := Scheme.Modules.pullback g
  let Q := Scheme.Modules.pullback v
  let m := IdealSheafDataModule.closedImmersionModuleToUnit i
  let mU := IdealSheafDataModule.closedImmersionModuleToUnit (pullback.fst v i)
  let e := closedImmersionIdealBaseChangeHom v i
  let w := BundleSectionZeroLocus.pullbackUnitComparison v
  haveI : Flat v := inferInstance
  haveI : IsIso e := isIso_flatClosedImmersionIdealBaseChangeHom_general v i
  haveI : IsIso (P.map e) := Functor.map_isIso P e
  have h₁ : Mono (P.map (e ≫ mU)) := by
    have hc : P.map (e ≫ mU) = P.map e ≫ P.map mU := P.map_comp e mU
    rw [hc]
    exact mono_comp' (by infer_instance) h
  have h₂ : Mono (P.map (Q.map m ≫ w)) := by
    rw [← closedImmersionIdealBaseChangeHom_toUnit v i]
    exact h₁
  have h₃ : Mono (P.map (Q.map m)) := by
    have hc : P.map (Q.map m ≫ w) = P.map (Q.map m) ≫ P.map w :=
      P.map_comp (Q.map m) w
    have h₃' : Mono (P.map (Q.map m) ≫ P.map w) := hc ▸ h₂
    letI : Mono (P.map (Q.map m) ≫ P.map w) := h₃'
    exact mono_of_mono_fac (f := P.map w) (g := P.map (Q.map m)) rfl
  exact mono_map_of_natIso (Scheme.Modules.pullbackComp g v) m h₃

end PfaffianDescent
