import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodUnitCoefficient
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodPresentation
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodUnitExtension

/-! # Spreading an actual finite presentation and its lifted generators -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- In a map of short exact sequences, invertibility of the actual middle
and right maps identifies the actual kernel map as an isomorphism. -/
theorem cubicClosedPointSerreFreeNeighborhood_kernel_map_isIso
    {C : Type*} [Category C] [Preadditive C] [Balanced C]
    (S T : ShortComplex C) (hS : S.ShortExact) (hT : T.ShortExact)
    (a : S ⟶ T) [IsIso a.τ₂] [IsIso a.τ₃] : IsIso a.τ₁ := by
  let b : Arrow.mk S.g ≅ Arrow.mk T.g :=
    Arrow.isoMk (asIso a.τ₂) (asIso a.τ₃) a.comm₂₃
  letI : Mono T.f := hT.mono_f
  let k : S.X₁ ≅ T.X₁ := KernelFork.mapIsoOfIsLimit
    (kf := KernelFork.ofι S.f S.zero) (kf' := KernelFork.ofι T.f T.zero)
    (ShortComplex.ShortExact.fIsKernel (S := S) hS)
    (ShortComplex.ShortExact.fIsKernel (S := T) hT) b
  have hk : k.hom = a.τ₁ := by
    apply (cancel_mono T.f).mp
    simpa [k, b] using (KernelFork.mapOfIsLimit_ι
      (KernelFork.ofι S.f S.zero) hT.fIsKernel b.hom).trans a.comm₁₂.symm
  rw [← hk]
  infer_instance

/-- An actual lifted map from a rank-two finite quotient presentation,
known invertible at one stalk, becomes an actual rank-two free
identification on an affine neighborhood. No finite-presentation property
of the unknown middle sheaf is assumed. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_of_presentation_lift
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionSequenceData X M)
    (d : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)))
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ⟶ M)
    (hdq : d ≫ q = 0) (hS : (ShortComplex.mk d q hdq).ShortExact)
    (v : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ⟶ e.E)
    (hv : v ≫ e.projection = q) (x : X)
    [IsIso ((schemeModuleStalkModuleFunctor X x).map v)] :
    ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 2)) ≅
        e.E.over U) := by
  let S := ShortComplex.mk d q hdq
  have hz : (d ≫ v) ≫ e.projection = 0 := by rw [Category.assoc, hv, hdq]
  let c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
    e.shortExact.fIsKernel.lift (KernelFork.ofι (d ≫ v) hz)
  have hc : c ≫ e.inclusion = d ≫ v :=
    e.shortExact.fIsKernel.fac (KernelFork.ofι (d ≫ v) hz) WalkingParallelPair.zero
  let a : S ⟶ e.complex := ShortComplex.homMk c v (𝟙 M) hc (by simpa [S] using hv)
  let F := schemeModuleStalkModuleFunctor X x
  letI : PreservesFiniteLimits F := by dsimp [F]; infer_instance
  letI : PreservesFiniteColimits F := by dsimp [F]; infer_instance
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  have hFx : IsIso (F.map c) := by
    haveI : IsIso (F.mapShortComplex.map a).τ₂ := by change IsIso (F.map v); infer_instance
    haveI : IsIso (F.mapShortComplex.map a).τ₃ := by
      change IsIso (F.map (𝟙 M))
      rw [F.map_id]
      infer_instance
    exact cubicClosedPointSerreFreeNeighborhood_kernel_map_isIso
      (S.map F) (e.complex.map F) (hS.map_of_exact F) (e.shortExact.map_of_exact F) (F.mapShortComplex.map a)
  letI := hFx
  obtain ⟨U, hxU, hU, hUc⟩ :=
    cubicClosedPointSerreFreeNeighborhood_unit_exists_affine_isIso c x
  let R := Scheme.Modules.restrictFunctor U.ι
  letI : R.IsLeftAdjoint := by dsimp [R]; infer_instance
  letI : IsIso (R.map c) := hUc
  have hRv : IsIso (R.map v) := by
    haveI : IsIso (R.mapShortComplex.map a).τ₁ := by change IsIso (R.map c); infer_instance
    haveI : IsIso (R.mapShortComplex.map a).τ₃ := by
      change IsIso (R.map (𝟙 M))
      rw [R.map_id]
      infer_instance
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ (R.mapShortComplex.map a)
      (ShortComplex.shortExact_map_restrictFunctor U.ι S hS)
      (ShortComplex.shortExact_map_restrictFunctor U.ι e.complex e.shortExact)
  letI := hRv
  let η := (Scheme.Modules.restrictUnitIso U.ι).symm
  let t := SheafOfModules.mapFreeIso R (ULift.{u} (Fin 2)) η ≪≫ asIso (R.map v)
  let G := (Scheme.Modules.overEquiv U).functor
  let b := BundleSectionZeroLocus.overEquivFreeIso (X := X) U (ULift.{u} (Fin 2))
  let z := (Scheme.Modules.overFunctorEquiv U).app (show X.Modules from e.E)
  exact ⟨U, hxU, hU, ⟨G.preimageIso (b.symm ≪≫ t ≪≫ z.symm)⟩⟩

end PfaffianDescent
