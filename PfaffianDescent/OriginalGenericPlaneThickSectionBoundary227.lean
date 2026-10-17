import PfaffianDescent.OriginalGenericPlanePointBoundaryValue227
import PfaffianDescent.ActualPointToThickBoundaryNonzero225
import PfaffianDescent.PlaneCubicSectionCokernelZeroCycle172
import PfaffianDescent.CorayStalkSupportSectionVanishing
import PfaffianDescent.OriginalCurvePointSurfaceFactory210

/-! SOURCE ONLY227. Original arbitrary rank-one M/nonzero section and its
SAME thick cokernel.172 supplies actual own-support closed points;224/225
supply nonzero of the literal original thick-section connecting AddHom.
The empty-support branch is retained separately. No H1-rank argument here. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open IdealSheafDataModule SchemeModuleInternalHom
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Only the native support and cohomology capabilities needed by thick227
and positiveEuler227, derived from the entire original zero-cycle theorem172.
No reduction of the section cokernel, base field change, or degree premise. -/
theorem planeCubic_nonzeroRankOneSection_nativeSupportCohomologyData227
    {k : Type u} [hField : Field k]
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    [hIntegral : IsIntegral (scheme (equationIdeal p hp))]
    (M : (scheme (equationIdeal p hp)).Modules) (hM : schemeModuleLocallyRankOne M)
    (s : M.val.obj (op ⊤)) (hs : s ≠ 0) :
    let I := equationIdeal p hp
    let X := scheme I
    let pi := toBase I
    let Q := cokernel (schemeModuleTopSectionHom M s)
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    (∀ x ∈ schemeModuleStalkSupport Q, IsClosed ({x} : Set X)) ∧
      Module.Finite k (SchemeModuleOpenSectionsOver pi Q ⊤) ∧
      Subsingleton (schemeModuleCohomology X Q 1) := by
  dsimp only
  obtain ⟨_hFinite, hClosed, hQ0, hQ1, _hDegree⟩ :=
    @planeCubic_nonzeroRankOneSection_cokernel_zeroCycle_data172.{u}
      k hField p hp hp0 hSmooth hIntegral M hM s hs
  exact ⟨hClosed, hQ0, hQ1⟩

/-- Extract only actual support closedness while the plane equation is abstract.
The numerical cycle/degree and cohomology tails never enter the concrete
original wrapper's type conversion. -/
private theorem originalPlaneSection_supportClosedNativeCut227
    {k : Type u} [hField : Field k]
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    [hIntegral : IsIntegral (scheme (equationIdeal p hp))]
    (M : (scheme (equationIdeal p hp)).Modules) (hM : schemeModuleLocallyRankOne M)
    (s : M.val.obj (op ⊤)) (hs : s ≠ 0) :
    ∀ x ∈ schemeModuleStalkSupport (cokernel (schemeModuleTopSectionHom M s)),
      IsClosed ({x} : Set (scheme (equationIdeal p hp))) := by
  have hData := @planeCubic_nonzeroRankOneSection_nativeSupportCohomologyData227.{u}
    k hField p hp hp0 hSmooth hIntegral M hM s hs
  exact hData.1

/-- Choose a genuine frame at the generic point while the scheme is abstract.
The frame and monomorphism are derived from ordinary rank-one local geometry. -/
private theorem originalThickSection_shortExactNativeCut227
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M)
    (s : M.val.obj (op ⊤)) (hs : s ≠ 0) :
    (ShortComplex.cokernelSequence (schemeModuleTopSectionHom M s)).ShortExact := by
  obtain ⟨U, hgU, ⟨eU⟩⟩ := hM (genericPoint X)
  exact (schemeModuleTopSectionHom_mono_and_cokernelSequence_shortExact
    (X := X) (K := k) pi M hM U hgU eU s hs).2

/-- Native point-to-thick specialization with every actual scheme dictionary
explicit. The original wrapper constructs its point, point sequence and value;
this cut retains the entire section cokernel and the caller's HasExt instance. -/
private theorem originalThickSection_pointBoundaryNativeCut227
    {X : Scheme.{u}} [hIntegral : IsIntegral X]
    [hNoetherian : IsLocallyNoetherian X] [hExt : HasExt.{u} X.Modules]
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M)
    (hphi : (ShortComplex.cokernelSequence phi).ShortExact)
    (P : closedPoints X) [hDVR : IsDiscreteValuationRing (X.presheaf.stalk P.1)]
    (hP : P.1 ∈ schemeModuleStalkSupport (cokernel phi)) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ (hS : (incrementCokernelSequence (closedImmersionModuleToUnit i)).ShortExact)
      (c : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
        (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃),
      (Ext.mk₀.{u} (C := X.Modules) c).comp
        (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hS) (zero_add 1) ≠ 0 →
      (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi).postcomp
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (zero_add 1) ≠ 0 := by
  dsimp only
  intro hS c hc
  exact @schemeModuleUnitHom_closedPoint_globalBoundaryNonzero225.{u}
    X hIntegral hNoetherian hExt M hM phi hphi P hDVR hP hS c hc

/-- Eliminate the literal hS/E/scalar tuple on an abstract original scheme.
The original caller constructs this tuple using its point factory; no target
boundary conclusion is an input, and the entire thick cokernel is preserved. -/
private theorem originalThickSection_pointTupleConsumerNativeCut227
    {X : Scheme.{u}} [hIntegral : IsIntegral X]
    [hNoetherian : IsLocallyNoetherian X] [hExt : HasExt.{u} X.Modules]
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M)
    (hphi : (ShortComplex.cokernelSequence phi).ShortExact)
    (P : closedPoints X) [hDVR : IsDiscreteValuationRing (X.presheaf.stalk P.1)]
    (hP : P.1 ∈ schemeModuleStalkSupport (cokernel phi)) :
    let L := X.residueField P.1
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
    (∃ (hS : S.ShortExact)
      (E : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
        (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
      (a : L),
      (Ext.mk₀.{u} (C := X.Modules)
        (closedImmersionUnitToPushforwardUnit i ≫
          fieldPointPushforwardScalarEndomorphismAddHom i a ≫ E.inv)).comp
        (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hS) (zero_add 1) ≠ 0) →
      (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi).postcomp
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (zero_add 1) ≠ 0 := by
  dsimp only
  intro hPointData
  obtain ⟨hS, E, a, ha⟩ := hPointData
  exact @originalThickSection_pointBoundaryNativeCut227.{u}
    X hIntegral hNoetherian hExt M hM phi hphi P hDVR hP hS
    (closedImmersionUnitToPushforwardUnit (X.fromSpecResidueField P.1) ≫
      fieldPointPushforwardScalarEndomorphismAddHom (X.fromSpecResidueField P.1) a ≫ E.inv) ha

/-- The genuine original point factory specialized with its exact original
arguments, with the complete result type inferred and no thick-section context.
Its actual hS/E/scalar and literal three-arrow value are retained intact. -/
private def originalThickSection_pointValueRawFactoryCut227
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface (genericPlaneCubic p)
      (genericPlaneCubic_isHomogeneous p hp))) :=
  @originalGenericPlanePoint_exists_boundaryValue227.{u}
    K inferInstance inferInstance p hp hp0 hSmooth P

/-- Own-support of the ORIGINAL thick nonzero-section cokernel supplies
an actual closed point. Its actual nonzero point value is constructed by224,
and185/225 contract it into the SAME original M/section. The support premise
is geometric; no connecting-map or nonzero-class conclusion is assumed. -/
theorem originalGenericPlane_nonemptySectionSupport_boundaryNonzero227
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let F := GenericHyperplaneField K
    let pE := genericPlaneCubic p
    let hpE := genericPlaneCubic_isHomogeneous p hp
    let X := hypersurface pE hpE
    let pi := hypersurfaceToBase pE hpE
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    ∀ (M : X.Modules), schemeModuleLocallyRankOne M →
      ∀ (s : M.val.obj (op ⊤)), s ≠ 0 →
        (schemeModuleStalkSupport (cokernel (schemeModuleTopSectionHom M s))).Nonempty →
        ∃ hphi : (ShortComplex.cokernelSequence (schemeModuleTopSectionHom M s)).ShortExact,
          (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi).postcomp
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (zero_add 1) ≠ 0 := by
  classical
  dsimp only
  let F := GenericHyperplaneField K
  let pE := genericPlaneCubic p
  let hpE := genericPlaneCubic_isHomogeneous p hp
  let X := hypersurface pE hpE
  let pi := hypersurfaceToBase pE hpE
  letI hNativeExt : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI hNativeSmooth : Smooth pi := smoothCubic_actualGenericPlaneCubic_smooth p hp hp0
  letI hNativeIntegral : IsIntegral X := smoothCubic_actualGenericPlaneCubic_isIntegral p hp hp0
  letI hNativeNoetherian : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pi
  intro M hM s hs hSupport
  let phi := schemeModuleTopSectionHom M s
  have hphi : (ShortComplex.cokernelSequence phi).ShortExact :=
    originalThickSection_shortExactNativeCut227 (k := F) (X := X) pi M hM s hs
  letI hNativePlaneIntegral : IsIntegral (scheme (equationIdeal pE hpE)) :=
    (show IsIntegral X from inferInstance)
  have hClosed := @originalPlaneSection_supportClosedNativeCut227.{u}
    F inferInstance pE hpE (genericPlaneCubic_ne_zero p hp hp0)
    hNativeSmooth hNativePlaneIntegral M hM s hs
  obtain ⟨x, hx⟩ := hSupport
  let P : closedPoints X := ⟨x, hClosed x hx⟩
  letI hNativeDVR : IsDiscreteValuationRing (X.presheaf.stalk P.1) :=
    smoothCubic_actualGenericPlaneCubic_closedPoint_stalk_isDVR200 p hp hp0 P
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  have hPointData := @originalThickSection_pointValueRawFactoryCut227.{u}
    K inferInstance inferInstance p hp hp0 inferInstance P
  refine ⟨hphi, ?_⟩
  exact @originalThickSection_pointTupleConsumerNativeCut227.{u}
    X hNativeIntegral hNativeNoetherian hNativeExt M hM phi hphi P hNativeDVR hx hPointData

universe v

/-- Abstract existential elimination and disjunction introduction retain the
SAME witness. No actual scheme, Ext dictionary or boundary is reconstructed. -/
private theorem originalThickSection_existsBoundary_orRightCut227
    {witness : Sort v} (leftBranch : Prop) (boundary : witness → Prop)
    (hBoundary : ∃ w, boundary w) : ∃ w, leftBranch ∨ boundary w := by
  obtain ⟨w, hw⟩ := hBoundary
  exact ⟨w, Or.inr hw⟩

/-- The literal original section cokernel has two distinct branches. If its
actual support is empty, its sections on every original open are zero. If
support is nonempty, the SAME original thick connecting AddHom is nonzero. -/
theorem originalGenericPlane_nonzeroSection_boundary_cases227
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let pE := genericPlaneCubic p
    let hpE := genericPlaneCubic_isHomogeneous p hp
    let X := hypersurface pE hpE
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    ∀ (M : X.Modules), schemeModuleLocallyRankOne M →
      ∀ (s : M.val.obj (op ⊤)), s ≠ 0 →
        let phi := schemeModuleTopSectionHom M s
        let Q := cokernel phi
        ∃ hphi : (ShortComplex.cokernelSequence phi).ShortExact,
          (schemeModuleStalkSupport Q = ∅ ∧ ∀ U : X.Opens, Subsingleton Γ(Q, U)) ∨
          (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi).postcomp
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (zero_add 1) ≠ 0 := by
  classical
  dsimp only
  let pE := genericPlaneCubic p
  let hpE := genericPlaneCubic_isHomogeneous p hp
  let X := hypersurface pE hpE
  let pi := hypersurfaceToBase pE hpE
  letI hNativeExt : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI hNativeIntegral : IsIntegral X := smoothCubic_actualGenericPlaneCubic_isIntegral p hp hp0
  intro M hM s hs
  let phi := schemeModuleTopSectionHom M s
  let Q := (show X.Modules from cokernel phi)
  by_cases hEmpty : schemeModuleStalkSupport Q = ∅
  · have hphi : (ShortComplex.cokernelSequence phi).ShortExact :=
      originalThickSection_shortExactNativeCut227
        (k := GenericHyperplaneField K) (X := X) pi M hM s hs
    exact ⟨hphi, Or.inl ⟨hEmpty, fun U =>
      schemeModule_sections_subsingleton_of_support_empty Q hEmpty U⟩⟩
  · have hNonemptyBoundary := @originalGenericPlane_nonemptySectionSupport_boundaryNonzero227.{u}
      K inferInstance inferInstance p hp hp0 inferInstance M hM s hs
      (Set.nonempty_iff_ne_empty.mpr hEmpty)
    exact originalThickSection_existsBoundary_orRightCut227
      (schemeModuleStalkSupport Q = ∅ ∧ ∀ U : X.Opens, Subsingleton Γ(Q, U))
      _ hNonemptyBoundary

end PfaffianDescent.Coray
