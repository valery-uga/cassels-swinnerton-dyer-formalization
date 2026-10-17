import PfaffianDescent.SchemeModuleActualDualIncrementStalkPrincipal194
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! SOURCE ONLY194. Literal residue-field coefficients of the WHOLE original
dual quotient. Canonical quotient module structures are used directly. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open SchemeModuleInternalHom IsLocalRing
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Equal actual ideals give the canonical original-R-linear residue quotient. -/
def actualPointParameterResidueLinearEquiv194
    {R : Type u} [CommRing R] [IsLocalRing R] (t : R)
    (hspan : maximalIdeal R = Ideal.span ({t} : Set R)) :
    (R ⧸ Ideal.span ({t} : Set R)) ≃ₗ[R] ResidueField R :=
  Submodule.quotEquivOfEq (Ideal.span ({t} : Set R)) (maximalIdeal R) hspan.symm

/-- The quotient comparison retains the ORIGINAL residue map on every lift. -/
theorem actualPointParameterResidueLinearEquiv_mk194
    {R : Type u} [CommRing R] [IsLocalRing R] (t : R)
    (hspan : maximalIdeal R = Ideal.span ({t} : Set R)) (r : R) :
    actualPointParameterResidueLinearEquiv194 t hspan
      (Ideal.Quotient.mk (Ideal.span ({t} : Set R)) r) = residue R r := by
  exact Submodule.quotEquivOfEq_mk _ _ hspan.symm r

/-- Every actual native projection value has the SAME original residue
coefficient. Neither a residue scalar nor quotient-comparison square is assumed. -/
theorem actualDualIncrementWholeStalkCokernelResidueCoefficient194
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (j : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (hS : (incrementCokernelSequence j).ShortExact)
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M))
    (t : X.presheaf.stalk (U.ι x))
    (he₀ : ∀ r, schemeModuleStalkToRingLinearMap j (U.ι x) (e₀ r) = r * t)
    (hspan : maximalIdeal (X.presheaf.stalk (U.ι x)) =
      Ideal.span ({t} : Set (X.presheaf.stalk (U.ι x))))
    (a : (schemeModuleStalkModuleFunctor X (U.ι x)).obj (dual M)) :
    actualPointParameterResidueLinearEquiv194 t hspan
      ((actualDualIncrementWholeStalkCokernelIso194 U x M e j hS e₀ t he₀).hom
        (((incrementCokernelSequence j).map
          (schemeModuleStalkModuleFunctor X (U.ι x))).g a)) =
      residue (X.presheaf.stalk (U.ι x))
        ((actualDualIncrementStalkCoefficientIso194 U x M e e₀).hom a) := by
  have h := actualDualIncrementWholeStalkCokernelIso_projection194 U x M e j hS e₀ t he₀
  have hv := ConcreteCategory.congr_hom h a
  change (actualDualIncrementWholeStalkCokernelIso194 U x M e j hS e₀ t he₀).hom
      (((incrementCokernelSequence j).map
        (schemeModuleStalkModuleFunctor X (U.ι x))).g a) =
    Ideal.Quotient.mk (Ideal.span ({t} : Set (X.presheaf.stalk (U.ι x))))
      ((actualDualIncrementStalkCoefficientIso194 U x M e e₀).hom a) at hv
  rw [hv]
  exact actualPointParameterResidueLinearEquiv_mk194 t hspan _

end PfaffianDescent
