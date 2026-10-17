import PfaffianDescent.ClosedImmersionPushforwardBaseChange

/-! The actual ideal-module map attached to a closed-immersion base change. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- The canonical map from the pulled-back actual ideal module to the actual
ideal module of the fibre-product closed immersion. -/
noncomputable def closedImmersionIdealBaseChangeHom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    (Scheme.Modules.pullback f).obj
      (IdealSheafDataModule.closedImmersionModule i) ⟶
    IdealSheafDataModule.closedImmersionModule (pullback.fst f i) :=
  closedImmersionIdealPullbackKernelComparison f i ≫
    closedImmersionPushforwardBaseChangeKernelMap f i ≫
    (IdealSheafDataModule.closedImmersionModuleToKernelIso
      (pullback.fst f i)).inv

/-- The ideal-module base-change map carries the pulled-back original ideal
inclusion to the actual ideal inclusion, through the canonical comparison
of structure sheaves. -/
theorem closedImmersionIdealBaseChangeHom_toUnit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    closedImmersionIdealBaseChangeHom f i ≫
      IdealSheafDataModule.closedImmersionModuleToUnit (pullback.fst f i) =
    (Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫
      BundleSectionZeroLocus.pullbackUnitComparison f := by
  let j := pullback.fst f i
  let m := IdealSheafDataModule.closedImmersionModuleToKernelIso j
  let k := closedImmersionPushforwardBaseChangeKernelMap f i
  have hm : m.inv ≫ IdealSheafDataModule.closedImmersionModuleToUnit j =
      kernel.ι (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j) := by
    rw [← IdealSheafDataModule.closedImmersionModuleToKernel_comp j]
    exact m.inv_hom_id_assoc _
  let a := closedImmersionIdealPullbackKernelComparison f i
  let u := BundleSectionZeroLocus.pullbackUnitComparison f
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  change (a ≫ k ≫ m.inv) ≫
      IdealSheafDataModule.closedImmersionModuleToUnit j =
    (Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫ u
  calc
    (a ≫ k ≫ m.inv) ≫ IdealSheafDataModule.closedImmersionModuleToUnit j =
        a ≫ k ≫ (m.inv ≫ IdealSheafDataModule.closedImmersionModuleToUnit j) := by
      cat_disch
    _ = a ≫ k ≫ kernel.ι (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j) :=
      congrArg (a ≫ k ≫ ·) hm
    _ = a ≫ (k ≫ kernel.ι (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j)) :=
      (Category.assoc _ _ _).symm
    _ = a ≫ (kernel.ι ((Scheme.Modules.pullback f).map q) ≫ u) :=
      congrArg (a ≫ ·) (closedImmersionPushforwardBaseChangeKernelMap_comp_ι f i)
    _ = (a ≫ kernel.ι ((Scheme.Modules.pullback f).map q)) ≫ u :=
      (Category.assoc _ _ _).symm
    _ = (Scheme.Modules.pullback f).map
          (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫ u :=
      congrArg (· ≫ u) (closedImmersionIdealPullbackKernelComparison_comp_ι f i)

/-- The canonical actual ideal-module base-change map is characterized by
its composite with the inclusion into the structure sheaf. -/
theorem closedImmersionIdealBaseChangeHom_eq_of_toUnit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    (e : (Scheme.Modules.pullback f).obj
      (IdealSheafDataModule.closedImmersionModule i) ⟶
      IdealSheafDataModule.closedImmersionModule (pullback.fst f i))
    (he : e ≫ IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst f i) =
      (Scheme.Modules.pullback f).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫
        BundleSectionZeroLocus.pullbackUnitComparison f) :
    e = closedImmersionIdealBaseChangeHom f i := by
  haveI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit
      (pullback.fst f i)) := by
    change Mono (IdealSheafDataModule.idealModuleToUnit _)
    infer_instance
  apply (cancel_mono
    (IdealSheafDataModule.closedImmersionModuleToUnit (pullback.fst f i))).1
  exact he.trans (closedImmersionIdealBaseChangeHom_toUnit f i).symm

/-- An inclusion-compatible ideal-module isomorphism is necessarily the
canonical base-change map. -/
theorem isIso_closedImmersionIdealBaseChangeHom_of_compatibleIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    (e : (Scheme.Modules.pullback f).obj
      (IdealSheafDataModule.closedImmersionModule i) ≅
      IdealSheafDataModule.closedImmersionModule (pullback.fst f i))
    (he : e.hom ≫ IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst f i) =
      (Scheme.Modules.pullback f).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫
        BundleSectionZeroLocus.pullbackUnitComparison f) :
    IsIso (closedImmersionIdealBaseChangeHom f i) := by
  rw [← closedImmersionIdealBaseChangeHom_eq_of_toUnit f i e.hom he]
  exact e.isIso_hom

/-- The canonical ideal base-change map is monic whenever the pullback of
the original ideal inclusion is monic. Relative flatness of the quotient
can supply this condition even for a nonflat parameter change. -/
theorem closedImmersionIdealBaseChangeHom_mono_of_pullback_mono
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [Mono ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i))] :
    Mono (closedImmersionIdealBaseChangeHom f i) := by
  let u := BundleSectionZeroLocus.pullbackUnitComparison f
  have hu : IsIso u := BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  have hmonoU : Mono u := by
    letI := hu
    exact IsIso.mono_of_iso u
  have hmonoComp : Mono ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫ u) :=
    mono_comp' inferInstance hmonoU
  let j := pullback.fst f i
  exact @mono_of_mono_fac _ _ _ _ _
    (IdealSheafDataModule.closedImmersionModuleToUnit j)
    (closedImmersionIdealBaseChangeHom f i)
    ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫ u)
    hmonoComp (closedImmersionIdealBaseChangeHom_toUnit f i)

/-- Under the same relative-injectivity condition, epimorphy of the
canonical ideal map suffices for the desired isomorphism. -/
theorem isIso_closedImmersionIdealBaseChangeHom_of_pullback_mono_of_epi
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [Mono ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i))]
    [Epi (closedImmersionIdealBaseChangeHom f i)] :
    IsIso (closedImmersionIdealBaseChangeHom f i) := by
  letI : Mono (closedImmersionIdealBaseChangeHom f i) :=
    closedImmersionIdealBaseChangeHom_mono_of_pullback_mono f i
  exact isIso_of_mono_of_epi _

/-- Flat pullback of the actual closed-immersion ideal embeds in the ideal
of the fibre-product closed immersion. Only surjectivity of this map remains
for the full ideal-module base-change isomorphism. -/
theorem closedImmersionIdealBaseChangeHom_mono
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f] (i : Z ⟶ Y)
    [IsClosedImmersion i] : Mono (closedImmersionIdealBaseChangeHom f i) := by
  let P := Scheme.Modules.pullback f
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let a := closedImmersionIdealPullbackKernelComparison f i
  let u := BundleSectionZeroLocus.pullbackUnitComparison f
  have ha : IsIso a := isIso_flatClosedImmersionIdealPullbackKernelComparison f i
  have hmonoA : Mono a := by
    letI := ha
    exact IsIso.mono_of_iso a
  have hmonoK : Mono (kernel.ι (P.map q)) := inferInstance
  have hmonoP : Mono (P.map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) := by
    have h := mono_comp' hmonoA hmonoK
    exact (closedImmersionIdealPullbackKernelComparison_comp_ι f i) ▸ h
  have hu : IsIso u := BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  have hmonoU : Mono u := by
    letI := hu
    exact IsIso.mono_of_iso u
  have hmonoComp : Mono (P.map
      (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫ u) :=
    mono_comp' hmonoP hmonoU
  let j := pullback.fst f i
  have hfac := closedImmersionIdealBaseChangeHom_toUnit f i
  exact @mono_of_mono_fac _ _ _ _ _
    (IdealSheafDataModule.closedImmersionModuleToUnit j)
    (closedImmersionIdealBaseChangeHom f i)
    (P.map (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫ u)
    hmonoComp hfac

/-- Under flat base change, surjectivity is the only remaining obligation
for the canonical map between the actual ideal modules to be an isomorphism. -/
theorem isIso_closedImmersionIdealBaseChangeHom_of_epi
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f] (i : Z ⟶ Y)
    [IsClosedImmersion i] [Epi (closedImmersionIdealBaseChangeHom f i)] :
    IsIso (closedImmersionIdealBaseChangeHom f i) := by
  letI : Mono (closedImmersionIdealBaseChangeHom f i) :=
    closedImmersionIdealBaseChangeHom_mono f i
  exact isIso_of_mono_of_epi _

/-- For flat base change, invertibility of the actual ideal-module map
implies invertibility of the induced map between quotient kernels. -/
theorem isIso_closedImmersionPushforwardBaseChangeKernelMap_of_ideal
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f] (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIso (closedImmersionIdealBaseChangeHom f i)] :
    IsIso (closedImmersionPushforwardBaseChangeKernelMap f i) := by
  let a := closedImmersionIdealPullbackKernelComparison f i
  let k := closedImmersionPushforwardBaseChangeKernelMap f i
  let m := IdealSheafDataModule.closedImmersionModuleToKernelIso
    (pullback.fst f i)
  haveI : IsIso a := isIso_flatClosedImmersionIdealPullbackKernelComparison f i
  haveI : IsIso (a ≫ k ≫ m.inv) := by
    change IsIso (closedImmersionIdealBaseChangeHom f i)
    infer_instance
  have hkm : IsIso (k ≫ m.inv) := IsIso.of_isIso_comp_left a _
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ k m.inv m.isIso_inv hkm

/-- The quotient-pushforward base-change isomorphism follows from the
corresponding actual ideal-module base-change isomorphism. -/
theorem isIso_closedImmersionPushforwardBaseChangeHom_of_ideal
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f] (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIso (closedImmersionIdealBaseChangeHom f i)] :
    IsIso (closedImmersionPushforwardBaseChangeHom f i) := by
  haveI : IsIso (closedImmersionPushforwardBaseChangeKernelMap f i) :=
    isIso_closedImmersionPushforwardBaseChangeKernelMap_of_ideal f i
  exact closedImmersionPushforwardBaseChangeHom_isIso_of_kernelMap_isIso f i

/-- The flat base-change map on the actual quotient pushforward is an
isomorphism as soon as the actual ideal-module map is surjective. -/
theorem isIso_closedImmersionPushforwardBaseChangeHom_of_ideal_epi
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f] (i : Z ⟶ Y)
    [IsClosedImmersion i] [Epi (closedImmersionIdealBaseChangeHom f i)] :
    IsIso (closedImmersionPushforwardBaseChangeHom f i) := by
  letI : IsIso (closedImmersionIdealBaseChangeHom f i) :=
    isIso_closedImmersionIdealBaseChangeHom_of_epi f i
  exact isIso_closedImmersionPushforwardBaseChangeHom_of_ideal f i

end PfaffianDescent
