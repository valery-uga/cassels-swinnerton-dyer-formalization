import PfaffianDescent.CorayProjectiveIntersectionIntrinsicH1Finite
import PfaffianDescent.SchemeIsoPushforwardUnit

/-! SOURCE ONLY / UNVERIFIED159. Intrinsic unit H¹ transports across a
scheme isomorphism over the original coefficient spectrum. Both field
actions are constructed independently from the actual structure maps. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native closed-immersion H¹ injection, followed by the genuine
pushforward-unit coefficient isomorphism. -/
def schemeIso_unit_cohomologyOneLinearInjection
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules]
    (pi : Y ⟶ Spec (CommRingCat.of K)) (e : X ≅ Y) :
    letI : Linear K Y.Modules := schemeModulesLinearOver pi
    letI : Linear K X.Modules := schemeModulesLinearOver (e.hom ≫ pi)
    schemeModuleCohomology X (SheafOfModules.unit X.ringCatSheaf) 1 →ₗ[K]
      schemeModuleCohomology Y (SheafOfModules.unit Y.ringCatSheaf) 1 := by
  letI : Linear K Y.Modules := schemeModulesLinearOver pi
  letI : Linear K X.Modules := schemeModulesLinearOver (e.hom ≫ pi)
  exact (schemeModuleCohomologyIsoLinearEquivOver pi
      (PfaffianDescent.schemeIsoPushforwardUnitIso e) 1).toLinearMap.comp
    (closedImmersion_cohomologyOneLinearMap pi e.hom
      (SheafOfModules.unit X.ringCatSheaf))

/-- Injectivity comes from native exact closed pushforward; it is not a
supplied comparison certificate. -/
theorem schemeIso_unit_cohomologyOneLinearInjection_injective
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules]
    (pi : Y ⟶ Spec (CommRingCat.of K)) (e : X ≅ Y) :
    Function.Injective (schemeIso_unit_cohomologyOneLinearInjection pi e) := by
  letI : Linear K Y.Modules := schemeModulesLinearOver pi
  letI : Linear K X.Modules := schemeModulesLinearOver (e.hom ≫ pi)
  exact (schemeModuleCohomologyIsoLinearEquivOver pi
      (PfaffianDescent.schemeIsoPushforwardUnitIso e) 1).injective.comp
    (closedImmersion_cohomologyOneLinearMap_injective pi e.hom
      (SheafOfModules.unit X.ringCatSheaf))

/-- Reusable finite-dimensional H¹ transport. Equality of structural maps
is eliminated before constructing the actions, retaining the original
action on X rather than defining it through the comparison. -/
theorem schemeIso_unit_cohomologyOne_finite_finrank_le
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules]
    (piX : X ⟶ Spec (CommRingCat.of K))
    (piY : Y ⟶ Spec (CommRingCat.of K)) (e : X ≅ Y)
    (hbase : e.hom ≫ piY = piX) :
    (letI : Linear K Y.Modules := schemeModulesLinearOver piY
     Module.Finite K (schemeModuleCohomology Y
       (SheafOfModules.unit Y.ringCatSheaf) 1)) →
    (letI : Linear K X.Modules := schemeModulesLinearOver piX
     letI : Linear K Y.Modules := schemeModulesLinearOver piY
     Module.Finite K (schemeModuleCohomology X
       (SheafOfModules.unit X.ringCatSheaf) 1) ∧
       Module.finrank K (schemeModuleCohomology X
         (SheafOfModules.unit X.ringCatSheaf) 1) ≤
       Module.finrank K (schemeModuleCohomology Y
         (SheafOfModules.unit Y.ringCatSheaf) 1)) := by
  subst piX
  letI : Linear K X.Modules := schemeModulesLinearOver (e.hom ≫ piY)
  letI : Linear K Y.Modules := schemeModulesLinearOver piY
  intro hfinite
  letI := hfinite
  let f := schemeIso_unit_cohomologyOneLinearInjection piY e
  have hf : Function.Injective f :=
    schemeIso_unit_cohomologyOneLinearInjection_injective piY e
  letI : Module.Finite K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) := Module.Finite.of_injective f hf
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_injective hf⟩

end PfaffianDescent.Coray
