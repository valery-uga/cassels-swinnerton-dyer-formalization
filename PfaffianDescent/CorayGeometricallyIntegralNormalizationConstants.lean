import PfaffianDescent.CorayFiniteSubfieldTensorDegreeOne
import PfaffianDescent.CorayNormalizationGlobalUnitSectionsFinite
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGenericTensorField
import Mathlib.Algebra.Field.Equiv

/-!
# Actual generic-normalization constants over the original ground field

SOURCE ONLY / UNVERIFIED. No compiler was run by the author.
The original K action on the actual normalization unit section space is retained.
Its actual global ring is identified explicitly and made a field only by
integrality and finite dimension. The canonical Spec K(X) -> N map induces
its actual K-algebra embedding in the ORIGINAL function field. Genuine
geometric integrality of the ORIGINAL pi supplies the generic tensor-field
property; finite-subfield rank arithmetic then gives dimension one.

The generic tensor API is an existing Voisin/Serre project source, outside the
Coray inventory. Its source SHA matches an earlier accepted-impact snapshot,
and an olean exists; this packet makes no independent deep-audit claim for it.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
universe u
variable {K : Type u} [Field K]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual unit section space and actual ring of global functions are
linearly equivalent under the SAME independently pi-induced original K map.
The map is the identity on the actual underlying global sections. -/
def schemeModuleUnitTopOriginalRingLinearEquiv
    {X : Scheme.{u}} (pi : X ⟶ Spec (CommRingCat.of K)) :
    letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
    SchemeModuleOpenSectionsOver pi (SheafOfModules.unit X.ringCatSheaf) ⊤ ≃ₗ[K]
      Γ(X, ⊤) := by
  letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  refine
    { toFun := fun s => (show Γ(X, ⊤) from s)
      invFun := fun s => (show SchemeModuleOpenSectionsOver pi
        (SheafOfModules.unit X.ringCatSheaf) ⊤ from s)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := ?_ }
  intro c s
  change schemeOpenBaseRingHom pi ⊤ c * (show Γ(X, ⊤) from s) =
    schemeOpenBaseRingHom pi ⊤ c * (show Γ(X, ⊤) from s)
  rfl

/-- The canonical generic-point map into the SAME normalization induces an
actual K-algebra map from its actual global ring into the ORIGINAL function
field. Its K action is Spec.preimage of the actual original generic-base map;
exact coefficient compatibility is proved via toNormalization's composition.
No function-field identification of N, supplied coefficient square, or
normalization constant-field result is an input. -/
def integralGenericNormalization_globalFunctionsToOriginalFunctionFieldAlgHom
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let a : CommRingCat.of K ⟶ X.functionField :=
      Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ pi)
    letI : Algebra K Γ(N, ⊤) := (schemeOpenBaseRingHom (ν ≫ pi) ⊤).toAlgebra
    letI : Algebra K X.functionField := a.hom.toAlgebra
    Γ(N, ⊤) →ₐ[K] X.functionField := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let a : CommRingCat.of K ⟶ X.functionField :=
    Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ pi)
  letI : Algebra K Γ(N, ⊤) := (schemeOpenBaseRingHom (ν ≫ pi) ⊤).toAlgebra
  letI : Algebra K X.functionField := a.hom.toAlgebra
  let f := X.fromSpecStalk (genericPoint X)
  let t := f.toNormalization
  let F := X.functionField
  have hbase : t ≫ (ν ≫ pi) = Spec.map a := by
    calc
      t ≫ (ν ≫ pi) = (t ≫ ν) ≫ pi := (Category.assoc _ _ _).symm
      _ = f ≫ pi := by rw [Scheme.Hom.toNormalization_fromNormalization]
      _ = Spec.map a := (Spec.map_preimage (f ≫ pi)).symm
  refine
    { toRingHom := (t.appTop ≫ (Scheme.ΓSpecIso F).hom).hom
      commutes' := ?_ }
  intro c
  change (Scheme.ΓSpecIso F).hom
    (t.appTop (schemeOpenBaseRingHom (ν ≫ pi) ⊤ c)) = a.hom c
  rw [schemeOpenBaseRingHom_top_apply]
  have ht : t.appTop (affineFunctionHom (ν ≫ pi) c) =
      affineFunctionHom (Spec.map a) c := by
    change (t.appTop.hom.comp (affineFunctionHom (ν ≫ pi))) c = _
    rw [← affineFunctionHom_comp, hbase]
  rw [ht]
  have hnat := Scheme.ΓSpecIso_inv_naturality a
  have hv := ConcreteCategory.congr_hom hnat c
  change (Scheme.ΓSpecIso F).inv (a.hom c) = affineFunctionHom (Spec.map a) c at hv
  rw [← hv]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso F).inv_hom_id (a.hom c)

/-- Actual finite normalization unit sections have rank one when the
ORIGINAL structural morphism is geometrically integral. The finite ring is
made a field from its OWN domain structure, then its actual canonical map
into K(X) and genuine geometric generic tensor property force its K degree1.
No rank-one, H0(N)=K, sigma=0, or normalization-GI premise is supplied. -/
theorem integralGenericNormalization_unit_topSections_finrank_eq_one_of_geometricallyIntegral
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [GeometricallyIntegral pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    Module.Finite K (SchemeModuleOpenSectionsOver (ν ≫ pi)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) →
    Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) = 1 := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  change Module.Finite K (SchemeModuleOpenSectionsOver (ν ≫ pi)
    (SheafOfModules.unit N.ringCatSheaf) ⊤) →
    Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) = 1
  intro hfinite
  letI : IsIntegral N := inferInstance
  let L := Γ(N, ⊤)
  let a : CommRingCat.of K ⟶ X.functionField :=
    Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ pi)
  letI : Algebra K L := (schemeOpenBaseRingHom (ν ≫ pi) ⊤).toAlgebra
  letI : Algebra K X.functionField := a.hom.toAlgebra
  let E := schemeModuleUnitTopOriginalRingLinearEquiv (ν ≫ pi)
  letI : Module.Finite K (SchemeModuleOpenSectionsOver (ν ≫ pi)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) := hfinite
  letI : Module.Finite K L := Module.Finite.equiv E
  letI : IsDomain L := inferInstance
  letI : Field L := fieldOfFiniteDimensional K L
  let i : L →ₐ[K] X.functionField :=
    integralGenericNormalization_globalFunctionsToOriginalFunctionFieldAlgHom X pi
  have ha : Spec.map a = X.fromSpecStalk (genericPoint X) ≫ pi :=
    Spec.map_preimage _
  have htensor : IsField (L ⊗[K] X.functionField) :=
    PfaffianDescent.serreIncidenceGeometric_generic_tensor_isField
      (L := L) pi a ha
  have hreverse : IsField (X.functionField ⊗[K] L) :=
    (Algebra.TensorProduct.comm K X.functionField L).toMulEquiv.isField htensor
  have hdegree : Module.finrank K L = 1 :=
    finite_subfield_finrank_eq_one_of_tensor_isField K L X.functionField i hreverse
  exact E.finrank_eq.trans hdegree

end PfaffianDescent.Coray
