import PfaffianDescent.SchemeModuleBaseLinearCategory
import Mathlib.Algebra.Algebra.Tower

/-! Source-only genuine global-constants actions. Both category actions come
from original native structural maps. The K action is not replaced by a
transported module structure. No scalar compatibility/tower is an input to
the actual Scheme caller; it is derived from the actual global restrictions. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite
universe u w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original canonical affinization has the identity ring map on its
own global functions; no affine hypothesis on X. -/
theorem affineFunctionHom_toSpecGamma_eq_id (X : Scheme.{u}) :
    affineFunctionHom X.toSpecΓ = RingHom.id Γ(X, ⊤) := by
  unfold affineFunctionHom
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  rfl


/-- Native K coefficients, first mapped to global functions and then acted
on through X.toSpecGamma, restrict to EXACTLY the original pi coefficients. -/
theorem schemeOpenBaseRingHom_toSpecGamma_groundCoefficient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (.of K)) (hA : IsField Γ(X, ⊤))
    (U : X.Opens) (c : K) :
    letI : Field Γ(X, ⊤) := hA.toField
    schemeOpenBaseRingHom X.toSpecΓ U (schemeOpenBaseRingHom pi ⊤ c) =
      schemeOpenBaseRingHom pi U c := by
  letI : Field Γ(X, ⊤) := hA.toField
  change X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (affineFunctionHom X.toSpecΓ (schemeOpenBaseRingHom pi ⊤ c)) =
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (affineFunctionHom pi c)
  rw [affineFunctionHom_toSpecGamma_eq_id, RingHom.id_apply,
    schemeOpenBaseRingHom_top_apply]


/-- Equality of actual native morphisms under the two scalar actions, proved
on their original section components, before passing to Ext. -/
theorem schemeModuleHomBaseSmul_toSpecGamma_groundCoefficient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (.of K)) (hA : IsField Γ(X, ⊤))
    {M N : X.Modules} (c : K) (f : M ⟶ N) :
    letI : Field Γ(X, ⊤) := hA.toField
    schemeModuleHomBaseSmul X.toSpecΓ (schemeOpenBaseRingHom pi ⊤ c) f =
      schemeModuleHomBaseSmul pi c f := by
  letI : Field Γ(X, ⊤) := hA.toField
  apply schemeModuleHom_ext_sections
  intro U s
  change schemeOpenBaseRingHom X.toSpecΓ U (schemeOpenBaseRingHom pi ⊤ c) •
      f.val.app (op U) s = schemeOpenBaseRingHom pi U c • f.val.app (op U) s
  rw [schemeOpenBaseRingHom_toSpecGamma_groundCoefficient pi hA U c]


/-- Ordinary generic category cut: compatibility on the actual coefficient
identity morphism induces the tower on the INSTALLED Ext modules. The Scheme
caller below constructs the identity compatibility; it is not an endpoint
assumption. -/
def extScalarTowerOfIdentityScalars
    {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    [Linear K C] [Linear A C] (M N : C) (n : ℕ)
    (hscalar : ∀ c : K, c • (𝟙 N) = (algebraMap K A c) • (𝟙 N)) :
    IsScalarTower K A (Ext.{w} M N n) := by
  apply IsScalarTower.of_algebraMap_smul
  intro c z
  calc
    (algebraMap K A c) • z =
        z.comp (Ext.mk₀ ((algebraMap K A c) • (𝟙 N))) (add_zero n) :=
      Ext.smul_eq_comp_mk₀ z (algebraMap K A c)
    _ = z.comp (Ext.mk₀ (c • (𝟙 N))) (add_zero n) :=
      congrArg (fun f : N ⟶ N => z.comp (Ext.mk₀ f) (add_zero n)) (hscalar c).symm
    _ = c • z := (Ext.smul_eq_comp_mk₀ z c).symm


/-- The ACTUAL Ext modules over original pi and canonical global constants
form a scalar tower. Both original category actions are retained; structural
coefficient compatibility is derived internally for arbitrary M/N/degree. -/
def schemeModuleExtGlobalConstantsScalarTower
    {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (.of K)) (hA : IsField Γ(X, ⊤))
    (M N : X.Modules) (n : ℕ) :
    letI : Field Γ(X, ⊤) := hA.toField
    letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear Γ(X, ⊤) X.Modules := schemeModulesLinearOver X.toSpecΓ
    IsScalarTower K Γ(X, ⊤) (Ext.{u} M N n) := by
  letI : Field Γ(X, ⊤) := hA.toField
  letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear Γ(X, ⊤) X.Modules := schemeModulesLinearOver X.toSpecΓ
  apply extScalarTowerOfIdentityScalars M N n
  intro c
  change schemeModuleHomBaseSmul pi c (𝟙 N) =
    schemeModuleHomBaseSmul X.toSpecΓ (schemeOpenBaseRingHom pi ⊤ c) (𝟙 N)
  exact (schemeModuleHomBaseSmul_toSpecGamma_groundCoefficient pi hA c (𝟙 N)).symm

end PfaffianDescent.Coray
