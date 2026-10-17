import PfaffianDescent.SchemeModuleInternalHomRestrictedFiberIso
import PfaffianDescent.SchemeModuleInternalHomTensorCokernel
import PfaffianDescent.FiniteProjectiveProjectionFormula

/-! The ACTUAL canonical global cokernel-to-intrinsic-fiber map is an
Iso when the closed immersion factors through one actual ideal-unit
chart. Local map coherence proves invertibility on that chart; actual
support vanishing proves it elsewhere. No projection-formula or fiber
certificate is assumed. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

/-- Genuine GLOBAL invertibility of the SAME canonical fiber map.
The only generic assumptions are actual charts of the original ideal
and a geometric factor through one of those charts. -/
theorem closedImmersionDualIncrement_fiberMap_isIso_of_factor_unitChart
    {Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (e : (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U) :
    IsIso (closedImmersionDualIncrement_fiberMap (j ≫ U.ι) B hB eB) := by
  let i := j ≫ U.ι
  let M := IdealSheafDataModule.closedImmersionModule i
  let D := dual M
  let a := closedImmersionDualIncrement_fiberMap i B hB eB
  have hcover : (Opens.grothendieckTopology X).CoversTop B := by
    rw [Opens.coversTop_iff]
    change ⨆ x, B x = ⊤
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hB x⟩
  let eD (x : X) : (SheafOfModules.overFunctor X.ringCatSheaf (B x)).obj D ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (B x))) :=
    dualOverUnitIso (B x) (eB x) ≪≫ unitOverIso (B x)
  let E := closedImmersionDualIncrement_tensorCokernelIso i B hB eB
  apply schemeModuleMap_isIso_of_stalk a
  intro x
  by_cases hx : x ∈ U
  · haveI : IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) :=
      closedImmersionDualIncrement_restrictFiberMap_isIso U j B hB eB e
    exact schemeModuleStalkMap_isIso_of_restrict U ⟨x, hx⟩ a
  · have hoff : x ∉ Set.range i := by
      rintro ⟨z, hz⟩
      apply hx
      rw [← hz]
      exact (j z).property
    have hTensor : Subsingleton
        ((schemeModuleTensor ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) D).presheaf.stalk x) :=
      closedImmersionPushforwardTwist_stalk_subsingleton_off_range_of_coversTop_iso_unit
        i D B hcover eD x hoff
    have hsrc : Subsingleton
        ((show X.Modules from cokernel (unitToHom
          (IdealSheafDataModule.closedImmersionModuleToUnit i))).presheaf.stalk x) :=
      schemeModule_stalk_subsingleton_of_iso x E hTensor
    have htgt : Subsingleton
        (((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj D)).presheaf.stalk x) :=
      schemeModulePushforward_stalk_subsingleton_off_range i
        ((Scheme.Modules.pullback i).obj D) x hoff
    let A := (schemeModuleStalkModuleFunctor X x).obj
      (cokernel (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i)))
    let C := (schemeModuleStalkModuleFunctor X x).obj
      ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj D))
    letI : Subsingleton A := by
      change Subsingleton
        ((show X.Modules from cokernel (unitToHom
          (IdealSheafDataModule.closedImmersionModuleToUnit i))).presheaf.stalk x)
      exact hsrc
    letI : Subsingleton C := by
      change Subsingleton
        (((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj D)).presheaf.stalk x)
      exact htgt
    have hA : IsZero A := ModuleCat.isZero_of_subsingleton A
    have hC : IsZero C := ModuleCat.isZero_of_subsingleton C
    let v : A ≅ C := hA.iso hC
    have hv : (schemeModuleStalkModuleFunctor X x).map a = v.hom := hA.eq_of_src _ _
    rw [hv]
    infer_instance

/-- The canonical Iso retains the literal intrinsic pullback fiber.
Its underlying map is the previously constructed original cokernel
factor, whose value is independent of all chosen charts. -/
def closedImmersionDualIncrement_canonicalFiberIso
    {Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (e : (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U) :
    cokernel (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit (j ≫ U.ι))) ≅
      (Scheme.Modules.pushforward (j ≫ U.ι)).obj
        ((Scheme.Modules.pullback (j ≫ U.ι)).obj
          (dual (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)))) := by
  letI := closedImmersionDualIncrement_fiberMap_isIso_of_factor_unitChart U j B hB eB e
  exact asIso (closedImmersionDualIncrement_fiberMap (j ≫ U.ι) B hB eB)

/-- The GLOBAL Iso carries the SAME categorical projection to the SAME
canonical adjunction unit. Its target is i_*i^*D, not a chosen bare
residue-field sheaf. -/
theorem closedImmersionDualIncrement_canonicalFiberIso_projection
    {Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (e : (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U) :
    cokernel.π (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit (j ≫ U.ι))) ≫
      (closedImmersionDualIncrement_canonicalFiberIso U j B hB eB e).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ U.ι)).unit.app
      (dual (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι))) := by
  change cokernel.π (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit (j ≫ U.ι))) ≫
    closedImmersionDualIncrement_fiberMap (j ≫ U.ι) B hB eB = _
  exact closedImmersionDualIncrement_fiberMap_projection (j ≫ U.ι) B hB eB

/-- Consequently the SAME original tensor projection-formula morphism
is itself invertible. This follows from the actual cokernel factor
identity, not an input projection-formula certificate. -/
theorem closedImmersionDualIncrement_tensorProjection_isIso_of_factor_unitChart
    {Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (e : (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U) :
    IsIso (schemeModuleCanonicalFiberProjection (j ≫ U.ι)
      (dual (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)))) :=
  (closedImmersionDualIncrement_fiberMap_isIso_iff_tensorProjection (j ≫ U.ι) B hB eB).mp
    (closedImmersionDualIncrement_fiberMap_isIso_of_factor_unitChart U j B hB eB e)

/-- The SAME canonical Iso preserves independently pi-induced constants
on actual sections. Its source/target actions are their original
O_X-module actions; no scalar structure is transported through an Iso. -/
theorem closedImmersionDualIncrement_canonicalFiberIso_originalBaseConstant
    {K : Type u} [Field K] (pi : X ⟶ Spec (CommRingCat.of K))
    {Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (e : (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U)
    (V : X.Opens) (c : K)
    (z : (cokernel (unitToHom
      (IdealSheafDataModule.closedImmersionModuleToUnit (j ≫ U.ι)))).val.obj (Opposite.op V)) :
    (closedImmersionDualIncrement_canonicalFiberIso U j B hB eB e).hom.val.app (Opposite.op V)
        (schemeOpenBaseRingHom pi V c • z) =
      schemeOpenBaseRingHom pi V c •
        (closedImmersionDualIncrement_canonicalFiberIso U j B hB eB e).hom.val.app (Opposite.op V) z :=
  ((closedImmersionDualIncrement_canonicalFiberIso U j B hB eB e).hom.val.app
    (Opposite.op V)).hom.map_smul _ _

end PfaffianDescent.SchemeModuleInternalHom
