import PfaffianDescent.AffineTildeHopfian
import PfaffianDescent.SchemeModuleOpenCoverIso
import PfaffianDescent.OpenImmersionQuotientPushforward

/-! Object comparisons for closed-immersion base change on affine source charts. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- The two closed immersions over a source chart obtained by first base
changing globally or first restricting to the chart have identical ideal
sheaves. -/
theorem affineSourceChartBaseChange_kernelEq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : X.affineCover.I₀) :
    (pullback.fst (X.affineCover.f a) (pullback.fst f i)).ker =
      (pullback.fst (X.affineCover.f a ≫ f) i).ker := by
  rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.IdealSheafData.comap_comp]

/-- Restricting the global base-changed quotient pushforward to a source
chart yields the same object as the quotient pushforward computed directly
on that chart. -/
noncomputable def affineSourceChartBaseChange_targetIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : X.affineCover.I₀) :
    let u := X.affineCover.f a
    let j := pullback.fst f i
    (Scheme.Modules.restrictFunctor u).obj
      ((Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit (pullback f i).ringCatSheaf)) ≅
    (Scheme.Modules.pushforward (pullback.fst (u ≫ f) i)).obj
      (SheafOfModules.unit (pullback (u ≫ f) i).ringCatSheaf) := by
  let u := X.affineCover.f a
  let j := pullback.fst f i
  let jU := pullback.fst u j
  let k := pullback.fst (u ≫ f) i
  have hker : jU.ker = k.ker := affineSourceChartBaseChange_kernelEq f i a
  exact targetAffineChartClosedImmersionPushforwardIso j a ≪≫
    closedImmersionPushforwardIsoOfKernelEq jU k hker

/-- Restriction of the pulled-back original quotient pushforward to a
source chart is pullback along the composite chart morphism. -/
noncomputable def affineSourceChartBaseChange_sourceIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : X.affineCover.I₀) :
    let u := X.affineCover.f a
    (Scheme.Modules.restrictFunctor u).obj
      ((Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf))) ≅
    (Scheme.Modules.pullback (u ≫ f)).obj
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) := by
  let u := X.affineCover.f a
  let M := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit Z.ringCatSheaf)
  exact (Scheme.Modules.restrictFunctorIsoPullback u).app
    ((Scheme.Modules.pullback f).obj M) ≪≫
    (Scheme.Modules.pullbackComp u f).app M

/-- For a closed immersion into an affine target, the canonical quotient
base-change map becomes an isomorphism after restriction to every affine
source chart. This uses the epimorphism property and the finite cyclic
quotient model, without identifying the restricted map with the local map. -/
theorem isIso_toAffineClosedImmersionPushforwardBaseChangeHom_restrict
    {A : Type u} [CommRing A] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i]
    (a : X.affineCover.I₀) :
    IsIso ((Scheme.Modules.restrictFunctor (X.affineCover.f a)).map
      (closedImmersionPushforwardBaseChangeHom f i)) := by
  let u := X.affineCover.f a
  let R := Scheme.Modules.restrictFunctor u
  let m := closedImmersionPushforwardBaseChangeHom f i
  let mChart := closedImmersionPushforwardBaseChangeHom (u ≫ f) i
  let eSource := affineSourceChartBaseChange_sourceIso f i a
  let eTarget := affineSourceChartBaseChange_targetIso f i a
  letI : IsIso mChart :=
    isIso_affineSourceChartClosedImmersionPushforwardBaseChangeHom f i a
  let eST := eSource ≪≫ asIso mChart ≪≫ eTarget.symm
  let p := affineSpectraClosedImmersionPushforwardPullback_exists_quotientTildeIso
    (u ≫ f) i
  let eS := eSource ≪≫ p.2
  haveI : Epi (R.map m) :=
    closedImmersionPushforwardBaseChangeHom_restrict_epi f i u
  exact @epiIsIsoOfAffineQuotientTildeSourceAndTargetIso
    _ _ p.1 _ _ eS eST (R.map m)
      (closedImmersionPushforwardBaseChangeHom_restrict_epi f i u)

/-- Closed-immersion quotient pushforward commutes with arbitrary base
change to an affine target, even when the source is not affine. -/
theorem isIso_toAffineClosedImmersionPushforwardBaseChangeHom
    {A : Type u} [CommRing A] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    IsIso (closedImmersionPushforwardBaseChangeHom f i) := by
  apply schemeModule_isIso_of_openCover_restrict_isIso X.affineCover
  intro a
  exact isIso_toAffineClosedImmersionPushforwardBaseChangeHom_restrict f i a

/-- Over an affine target, the canonical quotient-kernel base-change map
is an isomorphism for an arbitrary source scheme. -/
theorem isIso_toAffineClosedImmersionPushforwardBaseChangeKernelMap
    {A : Type u} [CommRing A] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    IsIso (closedImmersionPushforwardBaseChangeKernelMap f i) := by
  letI : IsIso (closedImmersionPushforwardBaseChangeHom f i) :=
    isIso_toAffineClosedImmersionPushforwardBaseChangeHom f i
  exact isIso_closedImmersionPushforwardBaseChangeKernelMap_of_pushforward f i

/-- Flat pullback of the actual closed-immersion ideal module agrees with
the actual ideal module of the fibre product over any affine target. -/
theorem isIso_flatToAffineClosedImmersionIdealBaseChangeHom
    {A : Type u} [CommRing A] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    IsIso (closedImmersionIdealBaseChangeHom f i) := by
  letI : IsIso (closedImmersionPushforwardBaseChangeHom f i) :=
    isIso_toAffineClosedImmersionPushforwardBaseChangeHom f i
  exact isIso_closedImmersionIdealBaseChangeHom_of_pushforward f i

/-- On a pulled-back affine target chart, the restriction of the global
fibre-product closed immersion and the chartwise fibre-product closed
immersion have the same ideal sheaf. -/
theorem affineTargetPullbackChartBaseChange_kernelEq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let u := Y.affineCover.f a
    let v := pullback.fst f u
    let g := pullback.snd f u
    (pullback.fst v (pullback.fst f i)).ker =
      (pullback.fst g (pullback.fst u i)).ker := by
  dsimp only
  let u := Y.affineCover.f a
  let v := pullback.fst f u
  let g := pullback.snd f u
  rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rw [← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp]
  exact congrArg (fun h => i.ker.comap h) pullback.condition

/-- On the pullback of a target affine chart, the source object of global
base change agrees with the source object of base change performed on that
target chart. -/
noncomputable def affineTargetPullbackChartBaseChange_sourceIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let u := Y.affineCover.f a
    let v := pullback.fst f u
    let g := pullback.snd f u
    let iU := pullback.fst u i
    (Scheme.Modules.restrictFunctor v).obj
      ((Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf))) ≅
    (Scheme.Modules.pullback g).obj
      ((Scheme.Modules.pushforward iU).obj
        (SheafOfModules.unit (pullback u i).ringCatSheaf)) := by
  let u := Y.affineCover.f a
  let v := pullback.fst f u
  let g := pullback.snd f u
  let M := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit Z.ringCatSheaf)
  exact (Scheme.Modules.restrictFunctorIsoPullback v).app
      ((Scheme.Modules.pullback f).obj M) ≪≫
    (pullbackSquareModuleComparison f u).app M ≪≫
    (Scheme.Modules.pullback g).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback u).app M).symm ≪≫
    (Scheme.Modules.pullback g).mapIso
      (targetAffineChartClosedImmersionPushforwardIso i a)

/-- On a pulled-back target affine chart, the restricted global quotient
pushforward agrees with the quotient pushforward of the chartwise fibre
product. -/
noncomputable def affineTargetPullbackChartBaseChange_targetIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let u := Y.affineCover.f a
    let v := pullback.fst f u
    let g := pullback.snd f u
    let j := pullback.fst f i
    let iU := pullback.fst u i
    (Scheme.Modules.restrictFunctor v).obj
      ((Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit (pullback f i).ringCatSheaf)) ≅
    (Scheme.Modules.pushforward (pullback.fst g iU)).obj
      (SheafOfModules.unit (pullback g iU).ringCatSheaf) := by
  let u := Y.affineCover.f a
  let v := pullback.fst f u
  let g := pullback.snd f u
  let j := pullback.fst f i
  let iU := pullback.fst u i
  let jV := pullback.fst v j
  let k := pullback.fst g iU
  have hker : jV.ker = k.ker :=
    affineTargetPullbackChartBaseChange_kernelEq f i a
  exact openImmersionClosedImmersionPushforwardIso j v ≪≫
    closedImmersionPushforwardIsoOfKernelEq jV k hker

/-- The global canonical quotient-pushforward base-change map is an
isomorphism after restriction to the preimage of each affine target chart. -/
theorem isIso_closedImmersionPushforwardBaseChangeHom_restrict_targetAffineChart
    {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    IsIso ((Scheme.Modules.restrictFunctor
      (pullback.fst f (Y.affineCover.f a))).map
        (closedImmersionPushforwardBaseChangeHom f i)) := by
  let u := Y.affineCover.f a
  let v := pullback.fst f u
  let g := pullback.snd f u
  let iU := pullback.fst u i
  letI : IsClosedImmersion iU := inferInstance
  let R := Scheme.Modules.restrictFunctor v
  let m := closedImmersionPushforwardBaseChangeHom f i
  let mLocal := closedImmersionPushforwardBaseChangeHom g iU
  let eSource := affineTargetPullbackChartBaseChange_sourceIso f i a
  let eTarget := affineTargetPullbackChartBaseChange_targetIso f i a
  letI : IsIso mLocal :=
    @isIso_toAffineClosedImmersionPushforwardBaseChangeHom _ _ _ _ g iU
      (by change IsClosedImmersion (pullback.fst u i); infer_instance)
  let eST := eSource ≪≫ asIso mLocal ≪≫ eTarget.symm
  haveI : Epi (R.map m) :=
    closedImmersionPushforwardBaseChangeHom_restrict_epi f i v
  apply schemeModule_isIso_of_openCover_restrict_isIso
    (pullback f u).affineCover
  intro b
  let w := (pullback f u).affineCover.f b
  let Rw := Scheme.Modules.restrictFunctor w
  haveI : IsOpenImmersion w := inferInstance
  let eSourceB := Rw.mapIso eSource ≪≫
    affineSourceChartBaseChange_sourceIso g iU b
  let p := @affineSpectraClosedImmersionPushforwardPullback_exists_quotientTildeIso
    _ _ _ _ (w ≫ g) _ iU
      (by change IsClosedImmersion (pullback.fst u i); infer_instance)
  let eS := eSourceB ≪≫ p.2
  let eT := Rw.mapIso eST
  have hEpiRm : Epi (R.map m) :=
    closedImmersionPushforwardBaseChangeHom_restrict_epi f i v
  haveI : Rw.PreservesEpimorphisms := inferInstance
  have hEpiDouble : Epi (Rw.map (R.map m)) :=
    @Functor.map_epi _ _ _ _ Rw inferInstance _ _ (R.map m) hEpiRm
  exact @epiIsIsoOfAffineQuotientTildeSourceAndTargetIso
    _ _ p.1 _ _ eS eT (Rw.map (R.map m)) hEpiDouble

/-- The canonical quotient-pushforward base-change map for a closed
immersion is an isomorphism over arbitrary schemes. -/
theorem isIso_closedImmersionPushforwardBaseChangeHom_general
    {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Z ⟶ Y) [IsClosedImmersion i] :
    IsIso (closedImmersionPushforwardBaseChangeHom f i) := by
  apply schemeModule_isIso_of_openCover_restrict_isIso
    (Y.affineCover.pullback₁ f : X.OpenCover)
  intro a
  exact isIso_closedImmersionPushforwardBaseChangeHom_restrict_targetAffineChart f i a

/-- The canonical map between quotient kernels is an isomorphism under
arbitrary base change of a closed immersion. -/
theorem isIso_closedImmersionPushforwardBaseChangeKernelMap_general
    {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Z ⟶ Y) [IsClosedImmersion i] :
    IsIso (closedImmersionPushforwardBaseChangeKernelMap f i) := by
  letI : IsIso (closedImmersionPushforwardBaseChangeHom f i) :=
    isIso_closedImmersionPushforwardBaseChangeHom_general f i
  exact isIso_closedImmersionPushforwardBaseChangeKernelMap_of_pushforward f i

/-- Under flat base change, the actual ideal module of a closed immersion
pulls back to the actual ideal module of the fibre-product immersion. -/
theorem isIso_flatClosedImmersionIdealBaseChangeHom_general
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (i : Z ⟶ Y) [IsClosedImmersion i] :
    IsIso (closedImmersionIdealBaseChangeHom f i) := by
  letI : IsIso (closedImmersionPushforwardBaseChangeHom f i) :=
    isIso_closedImmersionPushforwardBaseChangeHom_general f i
  exact isIso_closedImmersionIdealBaseChangeHom_of_pushforward f i

end PfaffianDescent
