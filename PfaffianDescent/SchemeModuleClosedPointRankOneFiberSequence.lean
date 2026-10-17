import PfaffianDescent.SchemeModuleRankOneCanonicalFiberIso
import PfaffianDescent.SchemeModuleSupportedFiberGroundDimension

/-! The actual closed-point ideal-tensor restriction sequence with SAME
adjunction unit as projection, and actual original-K weighted fiber dimension.
These are genuine tensor geometry; this file does not silently identify its
first object I_P tensor T with an independently prescribed line bundle.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

/-- Genuine frame of the actual point pullback, internally from its
ordinary rank-one neighborhood. The bare residue-field frame is chosen. -/
theorem schemeModuleLocallyRankOne_closedPoint_fiberFrame
    (P : closedPoints X) (T : X.Modules) (hT : schemeModuleLocallyRankOne T) :
    Nonempty ((Scheme.Modules.pullback (X.fromSpecResidueField P.1)).obj T ≅
      SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf) := by
  classical
  let i := X.fromSpecResidueField P.1
  obtain ⟨U, hPU, ⟨eU⟩⟩ := hT P.1
  let eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    ((Scheme.Modules.overFunctorEquiv U).app T).symm ≪≫
      (Scheme.Modules.overEquiv U).functor.mapIso eU ≪≫
      (Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
      Scheme.Modules.restrictUnitIso U.ι
  have hrange : Set.range i ⊆ Set.range U.ι := by
    rintro x ⟨z, rfl⟩
    rw [Scheme.fromSpecResidueField_apply]
    exact ⟨⟨P.1, hPU⟩, rfl⟩
  let j := IsOpenImmersion.lift U.ι i hrange
  have hji : j ≫ U.ι = i := IsOpenImmersion.lift_fac _ _ _
  exact ⟨by simpa only [hji] using schemeModuleFiberFrameIso U.ι j T eT⟩

/-- The SAME canonical projection for an arbitrary locally rank-one
coefficient at a closed point is an Iso, with all charts chosen internally. -/
theorem schemeModuleLocallyRankOne_closedPoint_canonicalFiberProjection_isIso
    (P : closedPoints X) (T : X.Modules) (hT : schemeModuleLocallyRankOne T) :
    IsIso (schemeModuleCanonicalFiberProjection (X.fromSpecResidueField P.1) T) := by
  classical
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts T hT
  let U := B P.1
  have hrange : Set.range i ⊆ Set.range U.ι := by
    rintro x ⟨z, rfl⟩
    rw [Scheme.fromSpecResidueField_apply]
    exact ⟨⟨P.1, hB P.1⟩, rfl⟩
  let j := IsOpenImmersion.lift U.ι i hrange
  have hji : j ≫ U.ι = i := IsOpenImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (j ≫ U.ι) := hji.symm ▸ inferInstance
  have hlocal : IsIso (schemeModuleCanonicalFiberProjection (j ≫ U.ι) T) :=
    schemeModuleCanonicalFiberProjection_isIso_of_factor_unitCharts U j T B hB eB (eB P.1)
  change IsIso (schemeModuleCanonicalFiberProjection i T)
  exact hji ▸ hlocal

/-- Actual I_P tensor T -> T -> i_*i^*T is short exact, and its actual
cokernel has the unique Iso carrying its original projection to eta_T.
Neither desired exactness nor a comparison square is supplied as input. -/
theorem schemeModuleLocallyRankOne_closedPoint_idealTensor_fiberSequence
    (P : closedPoints X) (T : X.Modules) (hT : schemeModuleLocallyRankOne T) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let S := closedImmersionIdealTwistSequence i T
    let beta := S.f ≫ (schemeModuleTensorUnitLeftIso T).hom
    let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T
    ∃ hzero : beta ≫ eta = 0,
      (ShortComplex.mk beta eta hzero).ShortExact ∧
      ∃ E : cokernel beta ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T),
        cokernel.π beta ≫ E.hom = eta ∧
        ∀ F : cokernel beta ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T),
          cokernel.π beta ≫ F = eta → F = E.hom := by
  classical
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let S := closedImmersionIdealTwistSequence i T
  have hS : S.ShortExact := schemeModuleLocallyRankOne_tensor_shortExact T hT
    (closedImmersionModulePushforwardSequence i) (closedImmersionModulePushforwardSequence_shortExact i)
  let mu := schemeModuleTensorUnitLeftIso T
  let beta := S.f ≫ mu.hom
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T
  letI := schemeModuleLocallyRankOne_closedPoint_canonicalFiberProjection_isIso P T hT
  let v := asIso (schemeModuleCanonicalFiberProjection i T)
  have hq : S.g ≫ v.hom = mu.hom ≫ eta :=
    schemeModuleCanonicalFiberProjection_unit_square i T
  have hzero : beta ≫ eta = 0 := by
    change (S.f ≫ mu.hom) ≫ eta = 0
    rw [Category.assoc, ← hq, ← Category.assoc, S.zero, zero_comp]
  let A := ShortComplex.mk beta eta hzero
  let e : S ≅ A := ShortComplex.isoMk (Iso.refl _) mu v
    (by simp only [A, beta, Iso.refl_hom, Category.id_comp])
    hq.symm
  have hA : A.ShortExact := ShortComplex.shortExact_of_iso e hS
  let E : cokernel beta ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T) :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel A.f) hA.gIsCokernel
  have hE : cokernel.π beta ≫ E.hom = eta :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel A.f) hA.gIsCokernel WalkingParallelPair.one
  refine ⟨hzero, hA, E, hE, ?_⟩
  intro F hF
  exact (cancel_epi (cokernel.π beta)).mp (hF.trans hE.symm)

/-- The actual supported fiber has finite ORIGINAL-K sections of full
residue degree. Its frame and scalar identification are derived internally. -/
theorem schemeModuleLocallyRankOne_closedPoint_fiberTop_finite_and_finrank
    {K : Type u} [Field K] [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (P : closedPoints X) (T : X.Modules) (hT : schemeModuleLocallyRankOne T) :
    Module.Finite K (SchemeModuleOpenSectionsOver pi
      ((Scheme.Modules.pushforward (X.fromSpecResidueField P.1)).obj
        ((Scheme.Modules.pullback (X.fromSpecResidueField P.1)).obj T)) ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi
        ((Scheme.Modules.pushforward (X.fromSpecResidueField P.1)).obj
          ((Scheme.Modules.pullback (X.fromSpecResidueField P.1)).obj T)) ⊤) = pi.residueDegree P.1 := by
  obtain ⟨e⟩ := schemeModuleLocallyRankOne_closedPoint_fiberFrame P T hT
  exact Coray.schemeModuleResiduePointFiberTop_finite_and_finrank pi P T e

end PfaffianDescent

