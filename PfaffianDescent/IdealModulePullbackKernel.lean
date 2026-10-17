import PfaffianDescent.IdealSheafModule
import PfaffianDescent.AffineGammaPushforward
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! The canonical kernel comparison for pulling back a closed-immersion ideal module. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- The canonical global map from pullback of the geometric kernel
ideal to the kernel of the pulled-back quotient map. -/
noncomputable def closedImmersionKernelPullbackComparison
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    (Scheme.Modules.pullback f).obj
      (IdealSheafDataModule.closedImmersionKernelModule i) ⟶
    kernel ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)) := by
  let P := Scheme.Modules.pullback f
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  haveI : P.Additive := inferInstance
  refine kernel.lift (P.map q) (P.map (kernel.ι q)) ?_
  calc
    P.map (kernel.ι q) ≫ P.map q = P.map (kernel.ι q ≫ q) :=
      (P.map_comp _ _).symm
    _ = P.map 0 := congrArg P.map (kernel.condition q)
    _ = 0 := P.mapAddHom.map_zero

/-- Pullback of the ideal inclusion factors through the kernel of the
pulled-back quotient map via the canonical comparison. -/
theorem closedImmersionKernelPullbackComparison_comp_ι
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    closedImmersionKernelPullbackComparison f i ≫
      kernel.ι ((Scheme.Modules.pullback f).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)) =
      (Scheme.Modules.pullback f).map
        (IdealSheafDataModule.closedImmersionKernelModuleToUnit i) := by
  unfold closedImmersionKernelPullbackComparison
  exact kernel.lift_ι _ _ _

/-- The canonical global comparison from pullback of the actual
closed-immersion ideal module to the pulled-back quotient kernel. -/
noncomputable def closedImmersionIdealPullbackKernelComparison
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    (Scheme.Modules.pullback f).obj
      (IdealSheafDataModule.closedImmersionModule i) ⟶
    kernel ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)) :=
  (Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToKernelIso i).hom ≫
    closedImmersionKernelPullbackComparison f i

/-- The actual ideal module's canonical kernel comparison has the
expected inclusion into the pulled-back structure sheaf. -/
theorem closedImmersionIdealPullbackKernelComparison_comp_ι
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    closedImmersionIdealPullbackKernelComparison f i ≫
      kernel.ι ((Scheme.Modules.pullback f).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)) =
      (Scheme.Modules.pullback f).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
  let P := Scheme.Modules.pullback f
  unfold closedImmersionIdealPullbackKernelComparison
  rw [Category.assoc, closedImmersionKernelPullbackComparison_comp_ι]
  exact (P.map_comp _ _).symm.trans
    (congrArg P.map (IdealSheafDataModule.closedImmersionModuleToKernel_comp i))

/-- It suffices to prove the geometric-kernel comparison invertible:
the actual ideal-module comparison then is invertible as well. -/
theorem isIso_closedImmersionIdealPullbackKernelComparison_of_kernel
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [IsIso (closedImmersionKernelPullbackComparison f i)] :
    IsIso (closedImmersionIdealPullbackKernelComparison f i) := by
  have h : IsIso ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToKernelIso i).hom) :=
    ((Scheme.Modules.pullback f).mapIso
      (IdealSheafDataModule.closedImmersionModuleToKernelIso i)).isIso_hom
  unfold closedImmersionIdealPullbackKernelComparison
  exact IsIso.comp_isIso' h inferInstance

/-- For a closed immersion, the ideal-kernel comparison is invertible
whenever pullback preserves monicity of its ideal inclusion. Pullback
preserves the cokernel because it is a left adjoint. -/
theorem isIso_closedImmersionIdealPullbackKernelComparison_of_mono
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [Mono ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i))] :
    IsIso (closedImmersionIdealPullbackKernelComparison f i) := by
  let P := Scheme.Modules.pullback f
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  haveI : P.Additive := inferInstance
  have hS : S.ShortExact :=
    IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i
  haveI : Epi S.g := hS.epi_g
  have hMap : (S.map P).Exact := by
    apply ShortComplex.exact_of_g_is_cokernel
    exact CokernelCofork.mapIsColimit _ hS.exact.gIsCokernel P
  haveI : Mono (S.map P).f := by
    change Mono (P.map (IdealSheafDataModule.closedImmersionModuleToUnit i))
    infer_instance
  let e := IsLimit.conePointUniqueUpToIso hMap.fIsKernel
    (kernelIsKernel (P.map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)))
  have he : e.hom ≫ kernel.ι (P.map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)) =
      P.map (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
    change e.hom ≫ kernel.ι (P.map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)) = P.map S.f
    exact
      (IsLimit.conePointUniqueUpToIso_hom_comp hMap.fIsKernel
        (kernelIsKernel (P.map
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)))
        (.zero))
  have heq : e.hom = closedImmersionIdealPullbackKernelComparison f i := by
    apply (cancel_mono (kernel.ι
      (P.map (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)))).mp
    exact he.trans (closedImmersionIdealPullbackKernelComparison_comp_ι f i).symm
  rw [← heq]
  exact e.isIso_hom

/-- The actual ideal-module kernel comparison is invertible for flat
pullback between affine schemes and an affine quotient immersion. -/
theorem isIso_flatAffineClosedImmersionIdealPullbackKernelComparison
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A)
    [IsClosedImmersion (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk I)))] :
    IsIso (closedImmersionIdealPullbackKernelComparison
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  haveI : Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :=
    flatAffineClosedImmersionIdealModulePullback_mono g hg I
  exact isIso_closedImmersionIdealPullbackKernelComparison_of_mono _ _

/-- The actual ideal-module kernel comparison is invertible under flat
affine pullback for every closed immersion into the affine target. -/
theorem isIso_flatAffineClosedImmersionIdealPullbackKernelComparison_of_closed
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat)
    {Z : Scheme.{u}} (i : Z ⟶ Spec (CommRingCat.of A))
    [IsClosedImmersion i] :
    IsIso (closedImmersionIdealPullbackKernelComparison
      (Spec.map (CommRingCat.ofHom g)) i) := by
  haveI : Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) :=
    flatAffineClosedImmersionIdealModulePullback_mono_of_closed g hg i
  exact isIso_closedImmersionIdealPullbackKernelComparison_of_mono _ _

end PfaffianDescent
