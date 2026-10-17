import PfaffianDescent.CorayAffineNativeQuasicoherentKernel
import PfaffianDescent.SheafModulePushforwardExact
import Mathlib.Topology.Sheaves.Module
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! Native global QC kernel closure, constructed from actual affine restriction
and over-site descent. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private theorem overEquivInverse_isQuasicoherent
    {X : Scheme.{u}} (U : X.Opens) (M : (U : Scheme).Modules)
    [M.IsQuasicoherent] :
    ((Scheme.Modules.overEquiv U).inverse.obj M).IsQuasicoherent := by
  have hM : M.IsQuasicoherent := inferInstance
  let G := (TopologicalSpace.Opens.overEquivalence
    (U : TopologicalSpace.Opens X)).functor
  let J := (Opens.grothendieckTopology X).over U
  let H := Opens.grothendieckTopology ↥(U : TopologicalSpace.Opens X)
  letI : G.IsContinuous J H :=
    inferInstanceAs ((TopologicalSpace.Opens.overEquivalence
      (U : TopologicalSpace.Opens X)).functor.IsContinuous
      ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology ↥(U : TopologicalSpace.Opens X)))
  letI : Functor.PreservesOneHypercovers G J H :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (CoverPreserving.of_isContinuous G J H)
  let R₀ : Sheaf H RingCat.{u} := U.sheafRestrict.obj X.ringCatSheaf
  let S₀ : Sheaf J RingCat.{u} := X.ringCatSheaf.over U
  let ψ : S₀ ⟶ (G.sheafPushforwardContinuous RingCat.{u} J H).obj R₀ :=
    (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
  letI : IsIso ψ :=
    (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).isIso_inv
  letI : (show SheafOfModules.{u} R₀ from M).IsQuasicoherent := hM
  change ((SheafOfModules.pushforward ψ).obj M).IsQuasicoherent
  exact SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    (J := H) (K := J) (R := R₀) (S := S₀)
    (M := show SheafOfModules.{u} R₀ from M) G ψ
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)

private theorem isQuasicoherent_of_isoRestriction
    {X Y : Scheme.{u}} (e : X ≅ Y) (M : X.Modules)
    [((Scheme.Modules.restrictFunctor e.inv).obj M).IsQuasicoherent] :
    M.IsQuasicoherent := by
  let P := Scheme.Modules.restrictFunctor e.inv
  let H := Scheme.Modules.restrictFunctor e.hom
  letI : (H.obj (P.obj M)).IsQuasicoherent := inferInstance
  let c : H.obj (P.obj M) ≅ M :=
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm.app M) ≪≫
      ((Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app M) ≪≫
      (Scheme.Modules.restrictFunctorId.app M)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso c inferInstance

private theorem over_isQuasicoherent_of_restrict
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    [((Scheme.Modules.restrictFunctor U.ι).obj M).IsQuasicoherent] :
    (M.over U).IsQuasicoherent := by
  let E := Scheme.Modules.overEquiv U
  let T := (SheafOfModules.overFunctor X.ringCatSheaf U).obj M
  let N := (Scheme.Modules.restrictFunctor U.ι).obj M
  letI : (E.inverse.obj N).IsQuasicoherent := overEquivInverse_isQuasicoherent U N
  let c : T ≅ E.inverse.obj N :=
    E.unitIso.app T ≪≫ E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
    c.symm inferInstance

/-- Native QC on actual Spec charts descends to the original scheme module.
The input here is the natural local QC condition; actual free/ideal callers
below construct it from their canonical chart frames. -/
theorem schemeNative_isQuasicoherent_of_nativeAffineCover
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (R : ι → CommRingCat.{u}) (e : ∀ i, (U i : Scheme) ≅ Spec (R i))
    (M : X.Modules)
    [∀ i, ((Scheme.Modules.pullback ((e i).inv ≫ (U i).ι)).obj M).IsQuasicoherent] :
    M.IsQuasicoherent := by
  letI : ∀ i, (M.over (U i)).IsQuasicoherent := fun i => by
    let q := (e i).inv ≫ (U i).ι
    let P := Scheme.Modules.restrictFunctor (e i).inv
    let N := (Scheme.Modules.restrictFunctor (U i).ι).obj M
    letI : ((Scheme.Modules.restrictFunctor q).obj M).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Spec (R i)).ringCatSheaf).prop_of_iso
        ((Scheme.Modules.restrictFunctorIsoPullback q).app M).symm inferInstance
    letI : (P.obj N).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Spec (R i)).ringCatSheaf).prop_of_iso
        ((Scheme.Modules.restrictFunctorComp (e i).inv (U i).ι).app M) inferInstance
    letI : N.IsQuasicoherent := isQuasicoherent_of_isoRestriction (e i) N
    exact over_isQuasicoherent_of_restrict (U i) M
  exact SheafOfModules.IsQuasicoherent.of_coversTop M U hU

/-- Kernels between actual QC scheme modules are QC. No kernel QC, comparison
iso, global section-surjectivity or cohomology-vanishing premise is supplied. -/
theorem schemeNative_kernel_isQuasicoherent
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  obtain ⟨ι, U, pres, hU, hAffine⟩ := M.exists_isOpenCover_presentation
  let R : ι → CommRingCat.{u} := fun i => Γ(X, U i)
  let e : ∀ i, (U i : Scheme) ≅ Spec (R i) := fun i => (hAffine i).isoSpec
  letI : ∀ i, ((Scheme.Modules.pullback ((e i).inv ≫ (U i).ι)).obj
      (kernel f)).IsQuasicoherent := fun i => by
    let q := (e i).inv ≫ (U i).ι
    let F := Scheme.Modules.restrictFunctor q
    letI : PreservesFiniteLimits F := restrictFunctor_preservesFiniteLimits q
    letI : (kernel (F.map f)).IsQuasicoherent :=
      affineNative_kernel_isQuasicoherent (R i) (F.map f)
    letI : (F.obj (kernel f)).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Spec (R i)).ringCatSheaf).prop_of_iso
        (PreservesKernel.iso F f).symm inferInstance
    exact (SheafOfModules.isQuasicoherent (Spec (R i)).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback q).app (kernel f)) inferInstance
  exact schemeNative_isQuasicoherent_of_nativeAffineCover
    U ((_root_.Opens.coversTop_iff (T := X) U).mpr hU) R e (kernel f)

end PfaffianDescent.Coray
