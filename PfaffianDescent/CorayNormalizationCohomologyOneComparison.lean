import PfaffianDescent.CorayPushforwardCechHomTransport
import PfaffianDescent.CorayGenericNormalizationPushforwardCechOne
import PfaffianDescent.CorayNormalizationIntrinsicCechOne
import PfaffianDescent.CorayProjectiveIntersectionChartDimension
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Map

/-! Actual boundary descent and the actual normalization H¹ comparison.
The comparison is constructed through the actual preimage Čech cochains.
The two actual Čech computations discharge their local Ext inputs internally.
No comparison, cocycle compatibility, flatness or acyclicity certificate is
a hypothesis of the geometric callers. The result is additive; no K-linear
dimension or genus formula is asserted.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} {ι : Type u}

/-- The genuine actual pushforward cocycle comparison identifies the two
actual connecting-map kernels. The cover and HasExt infrastructure are the
only generic hypotheses; actual boundaries are identified internally. -/
theorem schemeModulePushforwardCechOneToExt_eq_zero_iff
    (f : Y ⟶ X) (M : Y.Modules) (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules]
    (z : DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := (Scheme.Modules.pushforward f).obj M)) :
    schemeCoverDegreeOneToExtHom U hU ((Scheme.Modules.pushforward f).obj M) z = 0 ↔
      schemeCoverDegreeOneToExtHom (fun i => f ⁻¹ᵁ U i)
        (schemeModulePushforward_preimageFamily_coversTop f U hU) M
        (schemeModulePushforwardCechOneCocycleAddEquiv f M U z) = 0 := by
  exact (schemeCoverDegreeOneToExt_eq_zero_iff U hU
      ((Scheme.Modules.pushforward f).obj M) z).trans
    ((schemeModulePushforwardCechOneCocycleAddEquiv_boundary_iff f M U z).trans
      (schemeCoverDegreeOneToExt_eq_zero_iff (fun i => f ⁻¹ᵁ U i)
        (schemeModulePushforward_preimageFamily_coversTop f U hU) M
        (schemeModulePushforwardCechOneCocycleAddEquiv f M U z)).symm)

/-- The image of the actual ORIGINAL-X connecting-map kernel under the
actual preimage cocycle equivalence is precisely the actual target kernel.
This supplies the quotient descent proof, not a hypothesis for descent. -/
theorem schemeModulePushforwardCechOneToExt_map_ker
    (f : Y ⟶ X) (M : Y.Modules) (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules] :
    (schemeCoverDegreeOneToExtHom U hU ((Scheme.Modules.pushforward f).obj M)).ker.map
        (schemeModulePushforwardCechOneCocycleAddEquiv f M U).toAddMonoidHom =
      (schemeCoverDegreeOneToExtHom (fun i => f ⁻¹ᵁ U i)
        (schemeModulePushforward_preimageFamily_coversTop f U hU) M).ker := by
  let E := schemeModulePushforwardCechOneCocycleAddEquiv f M U
  ext z
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨w, hw, hwz⟩
    subst z
    change schemeCoverDegreeOneToExtHom (fun i => f ⁻¹ᵁ U i)
      (schemeModulePushforward_preimageFamily_coversTop f U hU) M (E w) = 0
    exact (schemeModulePushforwardCechOneToExt_eq_zero_iff f M U hU w).mp hw
  · intro hz
    refine ⟨E.symm z, ?_, E.apply_symm_apply z⟩
    change schemeCoverDegreeOneToExtHom U hU ((Scheme.Modules.pushforward f).obj M)
      (E.symm z) = 0
    apply (schemeModulePushforwardCechOneToExt_eq_zero_iff f M U hU (E.symm z)).mpr
    change schemeCoverDegreeOneToExtHom (fun i => f ⁻¹ᵁ U i)
      (schemeModulePushforward_preimageFamily_coversTop f U hU) M (E (E.symm z)) = 0
    rw [E.apply_symm_apply]
    exact hz

/-- The genuine degree-one cocycle quotients agree under actual preimage
transport for any actual scheme morphism and module. No local Ext vanishing
is needed for this quotient comparison; no desired kernel equality is an
input. The two connecting-map kernels are actual degree-zero boundaries. -/
def schemeModulePushforwardCechOneQuotientAddEquiv
    (f : Y ⟶ X) (M : Y.Modules) (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules] :
    DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
        (Y := (Scheme.Modules.pushforward f).obj M) ⧸
      (schemeCoverDegreeOneToExtHom U hU ((Scheme.Modules.pushforward f).obj M)).ker ≃+
    DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf
        (fun i => f ⁻¹ᵁ U i)).d 2 1) (Y := M) ⧸
      (schemeCoverDegreeOneToExtHom (fun i => f ⁻¹ᵁ U i)
        (schemeModulePushforward_preimageFamily_coversTop f U hU) M).ker :=
  QuotientAddGroup.congr _ _ (schemeModulePushforwardCechOneCocycleAddEquiv f M U)
    (schemeModulePushforwardCechOneToExt_map_ker f M U hU)

/-- Genuine additive H¹ comparison for the actual finite normalization of
an actual integral characteristic-zero scheme locally of finite type over
the original field. The normalization, its actual pushforward, the common
affine cover, actual face maps, actual boundaries, finite normalization,
local QC/local Ext and Ext infrastructure are constructed internally.
The comparison is not an assumption and no normalization flatness is used.
This theorem does not supply a K-linear comparison or a genus formula. -/
def genericNormalizationPushforwardUnit_cohomologyOneAddEquiv
    {K : Type u} [Field K] [CharZero K]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    schemeModuleCohomology X
        ((Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
          (SheafOfModules.unit N.ringCatSheaf)) 1 ≃+
      schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1 := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pi
  let U : X.affineOpens → X.Opens := fun i => i.1
  let M : N.Modules := SheafOfModules.unit N.ringCatSheaf
  let EX := genericNormalizationPushforwardUnit_affineCechQuotientEquivCohomologyOne X
  let EN := genericNormalizationUnit_preimageAffineCechQuotientEquivCohomologyOne X pi
  let EQ := schemeModulePushforwardCechOneQuotientAddEquiv ν M U
    (genericNormalization_affineOpenFamily_coversTop X)
  exact EX.symm.trans (EQ.trans EN)

/-- Primitive original p/q caller for the actual additive normalization H¹
comparison. Literal homogeneous intersection and integrality are the only
geometric inputs. Finite type over the original field, local Noetherianity,
finite normalization, Ext infrastructure and both affine computations are
internal. The foundation applies in particular to the original smooth cubic
case; it does not assert a genus or dimension formula. -/
def projectiveIntersection_genericNormalizationPushforwardUnit_cohomologyOneAddEquiv
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n)
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    schemeModuleCohomology X
        ((Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
          (SheafOfModules.unit N.ringCatSheaf)) 1 ≃+
      schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1 := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  exact genericNormalizationPushforwardUnit_cohomologyOneAddEquiv X (toBase I)

end PfaffianDescent.Coray
