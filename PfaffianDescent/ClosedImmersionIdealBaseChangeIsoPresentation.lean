import PfaffianDescent.ClosedImmersionIdealPullbackMonoOnOpen

/-!
# Transporting ideal base change across an isomorphic presentation

If a closed immersion is presented by another closed immersion through
isomorphisms of source and target, the canonical ideal-module
base-change theorem transfers to the original immersion. The
coefficient-change map into the original target is the composite of
the model map with the target isomorphism.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem isIso_closedImmersionIdealBaseChangeHom_of_isoPresentation
    {X U Y W Z : Scheme.{u}}
    (g : X ⟶ U) (v : U ≅ Y)
    (j : W ⟶ U) (i : Z ⟶ Y)
    [IsClosedImmersion j] [IsClosedImmersion i]
    (e : W ≅ Z) (h : j ≫ v.hom = e.hom ≫ i)
    [IsIso (closedImmersionIdealBaseChangeHom g j)] :
    IsIso (closedImmersionIdealBaseChangeHom (g ≫ v.hom) i) := by
  have H : IsPullback j e.hom v.hom i :=
    IsPullback.of_vert_isIso ⟨h⟩
  have hker : j.ker = (pullback.fst v.hom i).ker := by
    have he : H.isoPullback.hom ≫ pullback.fst v.hom i = j :=
      H.isoPullback_hom_fst
    rw [← he, Scheme.Hom.ker_comp_of_isIso]
  have hmodel : Mono ((Scheme.Modules.pullback g).map
      (IdealSheafDataModule.closedImmersionModuleToUnit j)) :=
    closedImmersionIdealPullback_mono_of_baseChangeIso g j
  have hlocal : Mono ((Scheme.Modules.pullback g).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst v.hom i))) := by
    change Mono ((Scheme.Modules.pullback g).map
      (IdealSheafDataModule.idealModuleToUnit (pullback.fst v.hom i).ker))
    rw [← hker]
    exact hmodel
  haveI : IsOpenImmersion v.hom := inferInstance
  have hglobal :=
    closedImmersionIdealPullback_mono_of_targetOpen g v.hom i hlocal
  letI : Mono ((Scheme.Modules.pullback (g ≫ v.hom)).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) := hglobal
  exact isIso_closedImmersionIdealBaseChangeHom_of_pullback_mono (g ≫ v.hom) i

/-- Transfer a local canonical ideal comparison through a Cartesian
presentation of an open restriction of a closed immersion. -/
theorem isIso_closedImmersionIdealBaseChangeHom_of_openPullbackPresentation
    {X U Y W Z : Scheme.{u}}
    (g : X ⟶ U) (v : U ⟶ Y) [IsOpenImmersion v]
    (j : W ⟶ U) (i : Z ⟶ Y)
    [IsClosedImmersion j] [IsClosedImmersion i]
    (z : W ⟶ Z) (H : IsPullback j z v i)
    [IsIso (closedImmersionIdealBaseChangeHom g j)] :
    IsIso (closedImmersionIdealBaseChangeHom (g ≫ v) i) := by
  have hker : j.ker = (pullback.fst v i).ker := by
    have he : H.isoPullback.hom ≫ pullback.fst v i = j :=
      H.isoPullback_hom_fst
    rw [← he, Scheme.Hom.ker_comp_of_isIso]
  have hmodel : Mono ((Scheme.Modules.pullback g).map
      (IdealSheafDataModule.closedImmersionModuleToUnit j)) :=
    closedImmersionIdealPullback_mono_of_baseChangeIso g j
  have hlocal : Mono ((Scheme.Modules.pullback g).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst v i))) := by
    change Mono ((Scheme.Modules.pullback g).map
      (IdealSheafDataModule.idealModuleToUnit (pullback.fst v i).ker))
    rw [← hker]
    exact hmodel
  have hglobal :=
    closedImmersionIdealPullback_mono_of_targetOpen g v i hlocal
  letI : Mono ((Scheme.Modules.pullback (g ≫ v)).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) := hglobal
  exact isIso_closedImmersionIdealBaseChangeHom_of_pullback_mono (g ≫ v) i

end PfaffianDescent
