import PfaffianDescent.CorayOwnComponentProperConstants
import PfaffianDescent.CorayActualGenericPlaneSectionIntegral

/-! SOURCE ONLY / UNVERIFIED158. Actual properness and actual geometric
integrality derive rank-one unit H0 for the SAME scheme/base map. No
normalization, supplied H0 finiteness or constants-field conclusion enters.
This supplies the constant-term input needed later on the SAME actual E. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME scheme's global ring maps to its original function field
through the actual generic germ. Both algebra actions are independently
induced by the original base map; native Spec-preimage compatibility is
proved using the already constructed generic coefficient identity. -/
def integralScheme_originalGlobalRingToFunctionFieldAlgHom
    {X : Scheme.{u}} [IsIntegral X] (pi : X ⟶ Spec (.of K)) :
    let a : CommRingCat.of K ⟶ X.functionField :=
      Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ pi)
    letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
    letI : Algebra K X.functionField := a.hom.toAlgebra
    Γ(X, ⊤) →ₐ[K] X.functionField := by
  let a : CommRingCat.of K ⟶ X.functionField :=
    Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ pi)
  letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  letI : Algebra K X.functionField := a.hom.toAlgebra
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  refine { toRingHom := (X.germToFunctionField ⊤).hom, commutes' := ?_ }
  intro c
  have ha : Spec.map a = X.fromSpecStalk (genericPoint X) ≫ pi := Spec.map_preimage _
  exact (DFunLike.congr_fun
    (PfaffianDescent.serreIncidenceGenericCoefficientMap_eq pi a ha) c).symm

/-- Properness constructs finite H0. Geometric integrality then forces its
OWN finite constants field to have degree one through the actual generic
tensor-field theorem. No normalization constants hypothesis is used. -/
theorem integralProperGeometricallyIntegral_unitTopSections_finite_and_finrank_one
    {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [IsProper pi] [GeometricallyIntegral pi] :
    Module.Finite K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) ∧
    Module.finrank K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) = 1 := by
  obtain ⟨hfield, hfinite⟩ :=
    integralProper_originalGlobalFunctions_field_and_unitSectionsFinite pi
  let L := Γ(X, ⊤)
  let a : CommRingCat.of K ⟶ X.functionField :=
    Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ pi)
  letI : Algebra K L := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  letI : Algebra K X.functionField := a.hom.toAlgebra
  let E := schemeModuleUnitTopOriginalRingLinearEquiv pi
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi
    (SheafOfModules.unit X.ringCatSheaf) ⊤) := hfinite
  letI : Module.Finite K L := Module.Finite.equiv E
  letI : Field L := hfield.toField
  let i : L →ₐ[K] X.functionField := integralScheme_originalGlobalRingToFunctionFieldAlgHom pi
  have ha : Spec.map a = X.fromSpecStalk (genericPoint X) ≫ pi := Spec.map_preimage _
  have htensor : IsField (L ⊗[K] X.functionField) :=
    PfaffianDescent.serreIncidenceGeometric_generic_tensor_isField (L := L) pi a ha
  have hreverse : IsField (X.functionField ⊗[K] L) :=
    (Algebra.TensorProduct.comm K X.functionField L).toMulEquiv.isField htensor
  have hrank : Module.finrank K L = 1 :=
    finite_subfield_finrank_eq_one_of_tensor_isField K L X.functionField i hreverse
  exact ⟨hfinite, E.finrank_eq.trans hrank⟩

/-- ORIGINAL cubic smoothness yields actual finite unit H0 of rank one
on SAME rectangular generic plane cubic E over its original parameter field.
Native integrality and geometric integrality are produced internally. -/
theorem smoothCubic_actualLinearGenericPlaneSection_unitTopSections_finite_and_finrank_one
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let E := PfaffianDescent.linearHypersurfaceSection (genericPlaneInclusionMatrix (K := K))
      (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)
    let pi := hypersurfaceToBase
      (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
        (p.map (algebraMap K (GenericHyperplaneField K))))
      (PfaffianDescent.rectangularSubstitution_homogeneous
        (genericPlaneInclusionMatrix (K := K)) (hp.map _))
    Module.Finite (GenericHyperplaneField K)
      (SchemeModuleOpenSectionsOver pi (SheafOfModules.unit E.ringCatSheaf) ⊤) ∧
    Module.finrank (GenericHyperplaneField K)
      (SchemeModuleOpenSectionsOver pi (SheafOfModules.unit E.ringCatSheaf) ⊤) = 1 := by
  let E := PfaffianDescent.linearHypersurfaceSection (genericPlaneInclusionMatrix (K := K))
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)
  let pi := hypersurfaceToBase
    (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
      (p.map (algebraMap K (GenericHyperplaneField K))))
    (PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) (hp.map _))
  letI : IsIntegral E := smoothCubic_actualLinearGenericPlaneSection_isIntegral p hp hp0
  letI : GeometricallyIntegral pi :=
    smoothCubic_actualLinearGenericPlaneSection_geometricallyIntegral p hp hp0
  exact integralProperGeometricallyIntegral_unitTopSections_finite_and_finrank_one pi

end PfaffianDescent.Coray
