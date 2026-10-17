import PfaffianDescent.TargetAffineIdealSheaf

/-! Flat pullback of the actual closed-immersion ideal sequence. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- For a flat morphism, pullback of the actual closed-immersion
ideal-to-structure-to-pushforward sequence remains short exact. -/
theorem flatClosedImmersionModulePushforwardSequence_shortExact
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (i : Z ⟶ Y) [IsClosedImmersion i] :
    ((IdealSheafDataModule.closedImmersionModulePushforwardSequence i).map
      (Scheme.Modules.pullback f)).ShortExact := by
  let P := Scheme.Modules.pullback f
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  have hS : S.ShortExact :=
    IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i
  haveI : P.Additive := inferInstance
  haveI : Epi S.g := hS.epi_g
  haveI : Epi (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) := by
    change Epi S.g
    exact hS.epi_g
  have hExact : (S.map P).Exact := by
    apply ShortComplex.exact_of_g_is_cokernel
    exact CokernelCofork.mapIsColimit _ hS.exact.gIsCokernel P
  have hcomp : IsIso (closedImmersionIdealPullbackKernelComparison f i) :=
    isIso_flatClosedImmersionIdealPullbackKernelComparison f i
  have hmono : Mono ((S.map P).f) := by
    change Mono (P.map (IdealSheafDataModule.closedImmersionModuleToUnit i))
    rw [← closedImmersionIdealPullbackKernelComparison_comp_ι f i]
    let e := closedImmersionIdealPullbackKernelComparison f i
    haveI : IsIso e := hcomp
    have he : Mono e :=
      mono_of_mono_fac (f := inv e) (IsIso.hom_inv_id e)
    exact mono_comp' he (inferInstanceAs (Mono (kernel.ι (P.map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)))))
  have hepi : Epi (S.map P).g := by
    change Epi (P.map (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i))
    have hSourceEpi : Epi (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) :=
      inferInstance
    exact @Functor.map_epi _ _ _ _ P _ _ _ _ hSourceEpi
  exact ShortComplex.ShortExact.mk' hExact hmono hepi

/-- The quotient of the flat-pulled ideal inclusion is the pullback of the
original closed-immersion pushforward.  This is the canonical cokernel
isomorphism supplied by the pulled-back exact sequence. -/
noncomputable def flatClosedImmersionPullbackQuotientIsoCokernel
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (i : Z ⟶ Y) [IsClosedImmersion i] :
    cokernel ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≅
      (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) := by
  let P := Scheme.Modules.pullback f
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  change cokernel (S.map P).f ≅ (S.map P).X₃
  have hS := flatClosedImmersionModulePushforwardSequence_shortExact f i
  haveI : Epi (S.map P).g := hS.epi_g
  exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    hS.exact.gIsCokernel

/-- The quotient isomorphism takes the canonical cokernel projection to the
pulled-back structure-to-pushforward quotient map. -/
theorem flatClosedImmersionPullbackQuotientIsoCokernel_π
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (i : Z ⟶ Y) [IsClosedImmersion i] :
    cokernel.π ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≫
        (flatClosedImmersionPullbackQuotientIsoCokernel f i).hom =
      (Scheme.Modules.pullback f).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) := by
  let P := Scheme.Modules.pullback f
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  have hS := flatClosedImmersionModulePushforwardSequence_shortExact f i
  haveI : Epi (S.map P).g := hS.epi_g
  change cokernel.π (S.map P).f ≫
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      hS.exact.gIsCokernel).hom = (S.map P).g
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) hS.exact.gIsCokernel WalkingParallelPair.one

end PfaffianDescent
