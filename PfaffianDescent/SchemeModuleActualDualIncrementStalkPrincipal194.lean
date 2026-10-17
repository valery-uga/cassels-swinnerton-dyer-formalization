import PfaffianDescent.ActualOriginalPointIdealDualStalkComparison191
import PfaffianDescent.ActualIdealStalkDualPrincipalSequence190
import PfaffianDescent.SchemeModuleInternalHomIncrementExact

/-! SOURCE ONLY194. The actual global canonical dual increment, its whole
categorical cokernel and native projection are compared with the principal
parameter complex. The original sheaf and original stalk functor are retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open SchemeModuleInternalHom
open scoped nonZeroDivisors
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The functional in191 is literally the original inclusion-to-ring map. -/
theorem actualNativeInclusionFunctional194 (x : X) (M : X.Modules)
    (j : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    (((schemeModuleStalkModuleFunctor X x).map j ≫
      (schemeModuleUnitStalkIso X x).hom).hom) =
      schemeModuleStalkToRingLinearMap j x := by
  apply LinearMap.ext
  intro m
  rfl

/-- The actual dual-stalk comparison followed by the normalized ideal frame. -/
def actualDualIncrementStalkCoefficientIso194
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M)) :
    ((schemeModuleStalkModuleFunctor X (U.ι x)).obj (dual M)) ≅
      ModuleCat.of (X.presheaf.stalk (U.ι x)) (X.presheaf.stalk (U.ι x)) :=
  ((actualDualNativeStalkLinearEquiv191 U x M e).trans
    (actualIdealFrameDualCoordinate190 e₀)).toModuleIso

/-- The scalar is the SAME normalized parameter, derived from the original
unitToHom map and original inclusion, rather than a replacement scalar. -/
theorem actualDualIncrementStalk_scalar194
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (j : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M))
    (t : X.presheaf.stalk (U.ι x))
    (he₀ : ∀ r, schemeModuleStalkToRingLinearMap j (U.ι x) (e₀ r) = r * t) :
    pointCartierNativeStalkScalar
      ((incrementCokernelSequence j).map (schemeModuleStalkModuleFunctor X (U.ι x)))
      (schemeModuleUnitStalkIso X (U.ι x))
      (actualDualIncrementStalkCoefficientIso194 U x M e e₀) = t := by
  let F := schemeModuleStalkModuleFunctor X (U.ι x)
  let J : F.obj M →ₗ[X.presheaf.stalk (U.ι x)] X.presheaf.stalk (U.ι x) :=
    (F.map j ≫ (schemeModuleUnitStalkIso X (U.ι x)).hom).hom
  have hJ : J = schemeModuleStalkToRingLinearMap j (U.ι x) :=
    actualNativeInclusionFunctional194 (U.ι x) M j
  have heJ : ∀ r, J (e₀ r) = r * t := by
    intro r
    rw [hJ]
    exact he₀ r
  change actualIdealFrameDualCoordinate190 e₀
      (actualDualNativeStalkLinearEquiv191 U x M e
        (F.map (unitToHom j) ((schemeModuleUnitStalkIso X (U.ι x)).inv 1))) = t
  rw [actualDualNativeStalkLinearEquiv_unitToHom191, one_smul]
  exact actualIdealFrameDualCoordinate_inclusion190 e₀ J t heJ

/-- The original first map has precisely the principal-parameter square. -/
theorem actualDualIncrementStalk_first_square194
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (j : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M))
    (t : X.presheaf.stalk (U.ι x))
    (he₀ : ∀ r, schemeModuleStalkToRingLinearMap j (U.ι x) (e₀ r) = r * t) :
    ((incrementCokernelSequence j).map (schemeModuleStalkModuleFunctor X (U.ι x))).f ≫
        (actualDualIncrementStalkCoefficientIso194 U x M e e₀).hom =
      (schemeModuleUnitStalkIso X (U.ι x)).hom ≫
        (pointCartierYonedaCoefficientComplex t).f := by
  have h := pointCartierNativeStalkPrincipal_square
    ((incrementCokernelSequence j).map (schemeModuleStalkModuleFunctor X (U.ι x)))
    (schemeModuleUnitStalkIso X (U.ι x))
    (actualDualIncrementStalkCoefficientIso194 U x M e e₀)
  rw [actualDualIncrementStalk_scalar194 U x M e j e₀ t he₀] at h
  exact h

/-- Regularity is obtained from genuine exactness and actual coordinates. -/
theorem actualDualIncrementStalk_parameter_regular194
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (j : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (hS : (incrementCokernelSequence j).ShortExact)
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M))
    (t : X.presheaf.stalk (U.ι x))
    (he₀ : ∀ r, schemeModuleStalkToRingLinearMap j (U.ι x) (e₀ r) = r * t) :
    t ∈ (X.presheaf.stalk (U.ι x))⁰ := by
  have h := pointCartierNativeStalkScalar_regular
    ((incrementCokernelSequence j).map (schemeModuleStalkModuleFunctor X (U.ι x)))
    (hS.map_of_exact (schemeModuleStalkModuleFunctor X (U.ι x)))
    (schemeModuleUnitStalkIso X (U.ι x))
    (actualDualIncrementStalkCoefficientIso194 U x M e e₀)
  rw [actualDualIncrementStalk_scalar194 U x M e j e₀ t he₀] at h
  exact h

/-- The WHOLE original sheaf cokernel stalk, constructed through its native
universal property; no quotient or cokernel-comparison premise is supplied. -/
def actualDualIncrementWholeStalkCokernelIso194
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (j : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (hS : (incrementCokernelSequence j).ShortExact)
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M))
    (t : X.presheaf.stalk (U.ι x))
    (he₀ : ∀ r, schemeModuleStalkToRingLinearMap j (U.ι x) (e₀ r) = r * t) :
    ((incrementCokernelSequence j).map (schemeModuleStalkModuleFunctor X (U.ι x))).X₃ ≅
      (pointCartierYonedaCoefficientComplex t).X₃ :=
  pointCartierNativeStalkCokernelIso _ _
    (hS.map_of_exact (schemeModuleStalkModuleFunctor X (U.ι x)))
    (pointCartierYonedaCoefficientComplex_shortExact t
      (actualDualIncrementStalk_parameter_regular194 U x M e j hS e₀ t he₀))
    (schemeModuleUnitStalkIso X (U.ι x))
    (actualDualIncrementStalkCoefficientIso194 U x M e e₀)
    (actualDualIncrementStalk_first_square194 U x M e j e₀ t he₀)

/-- The quotient comparison preserves the actual native global projection. -/
theorem actualDualIncrementWholeStalkCokernelIso_projection194
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (j : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (hS : (incrementCokernelSequence j).ShortExact)
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M))
    (t : X.presheaf.stalk (U.ι x))
    (he₀ : ∀ r, schemeModuleStalkToRingLinearMap j (U.ι x) (e₀ r) = r * t) :
    ((incrementCokernelSequence j).map (schemeModuleStalkModuleFunctor X (U.ι x))).g ≫
        (actualDualIncrementWholeStalkCokernelIso194 U x M e j hS e₀ t he₀).hom =
      (actualDualIncrementStalkCoefficientIso194 U x M e e₀).hom ≫
        (pointCartierYonedaCoefficientComplex t).g :=
  pointCartierNativeStalkCokernelIso_square _ _
    (hS.map_of_exact (schemeModuleStalkModuleFunctor X (U.ι x)))
    (pointCartierYonedaCoefficientComplex_shortExact t
      (actualDualIncrementStalk_parameter_regular194 U x M e j hS e₀ t he₀))
    (schemeModuleUnitStalkIso X (U.ι x))
    (actualDualIncrementStalkCoefficientIso194 U x M e e₀)
    (actualDualIncrementStalk_first_square194 U x M e j e₀ t he₀)

/-- The entire actual sequence, with both original arrows, is constructed. -/
def actualDualIncrementWholeStalkPrincipalIso194
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (j : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (hS : (incrementCokernelSequence j).ShortExact)
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M))
    (t : X.presheaf.stalk (U.ι x))
    (he₀ : ∀ r, schemeModuleStalkToRingLinearMap j (U.ι x) (e₀ r) = r * t) :
    ((incrementCokernelSequence j).map (schemeModuleStalkModuleFunctor X (U.ι x))) ≅
      pointCartierYonedaCoefficientComplex t := by
  refine ShortComplex.isoMk (schemeModuleUnitStalkIso X (U.ι x))
    (actualDualIncrementStalkCoefficientIso194 U x M e e₀)
    (actualDualIncrementWholeStalkCokernelIso194 U x M e j hS e₀ t he₀) ?_ ?_
  · exact (actualDualIncrementStalk_first_square194 U x M e j e₀ t he₀).symm
  · exact (actualDualIncrementWholeStalkCokernelIso_projection194
      U x M e j hS e₀ t he₀).symm

end PfaffianDescent
