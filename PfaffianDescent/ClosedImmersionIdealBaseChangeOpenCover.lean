import PfaffianDescent.RelativeClosedImmersionIdealBaseChange
import PfaffianDescent.ClosedImmersionIdealPullbackMonoOnOpen

/-!
# Locality of canonical ideal base change on the source

The canonical ideal base-change map is an isomorphism if it is so after
precomposing the change map with every member of an open cover of its source.
The proof tests monicity of the pulled-back original ideal inclusion and
uses the already-checked quotient-kernel comparison.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem isIso_closedImmersionIdealBaseChangeHom_of_openCover_comp_isIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] (𝒰 : X.OpenCover)
    (h : ∀ a : 𝒰.I₀,
      IsIso (closedImmersionIdealBaseChangeHom ((𝒰.f a) ≫ f) i)) :
    IsIso (closedImmersionIdealBaseChangeHom f i) := by
  apply isIso_closedImmersionIdealBaseChangeHom_of_openCover_comp_mono
    f i 𝒰
  intro a
  letI : IsIso (closedImmersionIdealBaseChangeHom ((𝒰.f a) ≫ f) i) := h a
  exact closedImmersionIdealPullback_mono_of_baseChangeIso
    ((𝒰.f a) ≫ f) i

/-- A canonical ideal comparison on a target open supplies the comparison
for a map factoring through that open. -/
theorem isIso_closedImmersionIdealBaseChangeHom_of_targetOpen_iso
    {X U Y Z : Scheme.{u}}
    (g : X ⟶ U) (v : U ⟶ Y) [IsOpenImmersion v]
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (h : IsIso (closedImmersionIdealBaseChangeHom
      g (pullback.fst v i))) :
    IsIso (closedImmersionIdealBaseChangeHom (g ≫ v) i) := by
  letI : IsIso (closedImmersionIdealBaseChangeHom
      g (pullback.fst v i)) := h
  have hlocal : Mono ((Scheme.Modules.pullback g).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst v i))) :=
    closedImmersionIdealPullback_mono_of_baseChangeIso g (pullback.fst v i)
  letI : Mono ((Scheme.Modules.pullback (g ≫ v)).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) :=
    closedImmersionIdealPullback_mono_of_targetOpen g v i hlocal
  exact isIso_closedImmersionIdealBaseChangeHom_of_pullback_mono (g ≫ v) i

/-- The canonical ideal base-change map is local on an open cover of its
target. Local comparisons use the pulled-back closed immersion and the
corresponding map into each target open. -/
theorem isIso_closedImmersionIdealBaseChangeHom_of_targetOpenCover
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] (𝒰 : Y.OpenCover)
    (h : ∀ a : 𝒰.I₀,
      IsIso (closedImmersionIdealBaseChangeHom
        (𝒰.pullbackHom f a) (pullback.fst (𝒰.f a) i))) :
    IsIso (closedImmersionIdealBaseChangeHom f i) := by
  apply isIso_closedImmersionIdealBaseChangeHom_of_openCover_comp_isIso
    f i (𝒰.pullback₁ f)
  intro a
  haveI : IsOpenImmersion (𝒰.f a) := 𝒰.map_prop a
  have hlocal := isIso_closedImmersionIdealBaseChangeHom_of_targetOpen_iso
    (𝒰.pullbackHom f a) (𝒰.f a) i (h a)
  rw [Scheme.Cover.pullbackHom_map 𝒰 f a] at hlocal
  exact hlocal

end PfaffianDescent
