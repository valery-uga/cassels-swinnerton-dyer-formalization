import PfaffianDescent.P3NegativeFourRawTrace

/-! # The intrinsic canonical cohomology trace on projective three-space -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
namespace PfaffianDescent
universe u v
private theorem canonicalTrace_quotientEq_mk {G : Type u} [AddCommGroup G]
    (N N' : AddSubgroup G) (h : N = N') (g : G) :
    QuotientAddGroup.quotientAddEquivOfEq h (QuotientAddGroup.mk g) =
      (QuotientAddGroup.mk g : G ⧸ N') := by
  subst N'
  rfl

namespace ProjectiveNegativeTwist
universe t
variable (K : Type t) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The actual Ext comparison and canonical scalar trace have the same
kernel, since both kernels are exactly actual Cech boundaries. -/
theorem p3NegativeFour_augmentedExt_ker_eq_trace_ker
    [HasExt.{t} (Proj PS).Modules] :
    (p3RawTopCocycleToAugmentedExtHom K 4).ker = (p3NegativeFourTopTrace K).ker := by
  ext w
  change p3RawTopCocycleToAugmentedExt K 4 w = 0 ↔
    p3NegativeFourRawTrace K w.1 = 0
  rw [p3RawTopCocycleToAugmentedExt_eq_zero_iff,
    p3NegativeFourRawTrace_zero_iff_boundary]

/-- The canonical trace identifies actual augmented Ext-three of O(-4)
with the ground field. -/
def p3NegativeFourAugmentedExtTraceEquiv
    [HasExt.{t} (Proj PS).Modules] :
    Ext.{t} (p3SectionRepresenterCechTarget K) (sheafOfModules PS 4) 3 ≃+ K :=
  (QuotientAddGroup.quotientKerEquivOfSurjective
    (p3RawTopCocycleToAugmentedExtHom K 4)
    (p3RawTopCocycleToAugmentedExt_surjective K 4)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq
      (p3NegativeFour_augmentedExt_ker_eq_trace_ker K)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (p3NegativeFourTopTrace K) (p3NegativeFourTopTrace_surjective K)))

/-- The canonical trace on actual augmented classes evaluates to the
literal canonical Laurent coefficient. -/
theorem p3NegativeFourAugmentedExtTraceEquiv_raw
    [HasExt.{t} (Proj PS).Modules] (w : P3RawTopCocycle K 4) :
    p3NegativeFourAugmentedExtTraceEquiv K (p3RawTopCocycleToAugmentedExt K 4 w) =
      p3NegativeFourRawTrace K w.1 := by
  let E := QuotientAddGroup.quotientKerEquivOfSurjective
    (p3RawTopCocycleToAugmentedExtHom K 4)
    (p3RawTopCocycleToAugmentedExt_surjective K 4)
  let x : P3RawTopCocycle K 4 ⧸ (p3RawTopCocycleToAugmentedExtHom K 4).ker :=
    QuotientAddGroup.mk w
  have hm : E x = p3RawTopCocycleToAugmentedExt K 4 w := by rfl
  have hx : E.symm (p3RawTopCocycleToAugmentedExt K 4 w) = x := by
    rw [← hm]
    exact E.symm_apply_apply x
  change QuotientAddGroup.quotientKerEquivOfSurjective
    (p3NegativeFourTopTrace K) (p3NegativeFourTopTrace_surjective K)
      (QuotientAddGroup.quotientAddEquivOfEq
        (p3NegativeFour_augmentedExt_ker_eq_trace_ker K) (E.symm _)) = _
  rw [hx, canonicalTrace_quotientEq_mk]
  rfl

/-- Fully internal canonical scalar trace on H-three(P-three,O(-4)). -/
def p3NegativeFourCohomologyThreeTraceEquiv
    [HasExt.{t} (Proj PS).Modules] :
    schemeModuleCohomology (Proj PS) (sheafOfModules PS 4) 3 ≃+ K :=
  (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)).symm.trans
    (p3NegativeFourAugmentedExtTraceEquiv K)

/-- Its evaluation on an actual raw representative includes the canonical
unit-source transport; no normalization equality is assumed. -/
theorem p3NegativeFourCohomologyThreeTraceEquiv_raw
    [HasExt.{t} (Proj PS).Modules] (w : P3RawTopCocycle K 4) :
    p3NegativeFourCohomologyThreeTraceEquiv K
      ((Ext.mk₀ (C := (Proj PS).Modules) (p3SectionRepresenterCechTargetIsoUnit K).inv).comp
        (p3RawTopCocycleToAugmentedExt K 4 w) (zero_add 3)) =
      p3NegativeFourRawTrace K w.1 := by
  let E : Ext.{t} (p3SectionRepresenterCechTarget K) (sheafOfModules PS 4) 3 ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS 4) 3 :=
    extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)
  change p3NegativeFourAugmentedExtTraceEquiv K
    (E.symm (E (p3RawTopCocycleToAugmentedExt K 4 w))) = _
  rw [E.symm_apply_apply]
  exact p3NegativeFourAugmentedExtTraceEquiv_raw K w

end ProjectiveNegativeTwist
end PfaffianDescent
