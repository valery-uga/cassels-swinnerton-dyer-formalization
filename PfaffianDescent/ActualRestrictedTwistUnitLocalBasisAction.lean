import PfaffianDescent.ActualPositiveTwistRefinedChartBasisUnitAction
import PfaffianDescent.ActualPointLocalSectionClassRestrictTop

/- SOURCE ONLY / UNVERIFIED. Actual restricted unit action and SAME
basis coefficient on local sections, with all scalar changes computed by
actual f.appIso. Generic structural basis laws are discharged by callers. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false

lemma actualUnitHom_restrictedTopSection {X : Scheme.{u}} (M : X.Modules)
    (v : schemeModuleUnit X ⟶ M) (U : X.Opens) :
    M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (v.val.app (op ⊤) (1 : Γ(X, ⊤))) = v.val.app (op U) (1 : Γ(X, U)) := by
  let r := (homOfLE (show U ≤ ⊤ from le_top)).op
  have h := ConcreteCategory.congr_hom (v.mapPresheaf.naturality r)
    (1 : Γ(X, ⊤))
  change v.val.app (op U) ((schemeModuleUnit X).val.map r (1 : Γ(X, ⊤))) =
    M.val.map r (v.val.app (op ⊤) (1 : Γ(X, ⊤))) at h
  have h1 : (schemeModuleUnit X).val.map
      (homOfLE (show U ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤)) = (1 : Γ(X, U)) := by
    change X.presheaf.map _ (1 : Γ(X, ⊤)) = 1
    exact map_one _
  rw [h1] at h
  exact h.symm

lemma actualRestrictedTwistUnitLocalScalarAction
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor f).obj T ≅ schemeModuleUnit Y)
    (V : Y.Opens) (r : Γ(X, f ''ᵁ V)) (t : T.val.obj (op (f ''ᵁ V))) :
    p.hom.val.app (op V) (r • t) =
      (Scheme.Modules.restrictUnitIso f).hom.val.app (op V) r •
        p.hom.val.app (op V) t := by
  have h := (p.hom.val.app (op V)).hom.map_smul ((f.appIso V).hom r) t
  change p.hom.val.app (op V)
      ((f.appIso V).inv ((f.appIso V).hom r) • t) =
    (f.appIso V).hom r • p.hom.val.app (op V) t at h
  rw [Iso.hom_inv_id_apply] at h
  exact h

lemma actualRestrictedTwistUnitLocalBasisAction
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (T : X.Modules) (v : schemeModuleUnit X ⟶ T)
    (p : (Scheme.Modules.restrictFunctor f).obj T ≅ schemeModuleUnit Y)
    (hb : (Scheme.Modules.restrictFunctor f).map v ≫ p.hom =
      (Scheme.Modules.restrictUnitIso f).hom) (U : X.Opens) :
    p.hom.val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction f).unit.app T).val.app (op U)
        (v.val.app (op U) (1 : Γ(X, U)))) =
      (1 : Γ(Y, f ⁻¹ᵁ U)) := by
  let R := Scheme.Modules.restrictFunctor f
  let eta := (Scheme.Modules.restrictAdjunction f).unit
  let V := f ⁻¹ᵁ U
  have hn := congrArg (fun h => h.val.app (op U) (1 : Γ(X, U)))
    (eta.naturality v).symm
  change (R.map v).val.app (op V)
      ((eta.app (schemeModuleUnit X)).val.app (op U) (1 : Γ(X, U))) =
    (eta.app T).val.app (op U) (v.val.app (op U) (1 : Γ(X, U))) at hn
  have h := congrArg (fun h => h.val.app (op V)
      ((eta.app (schemeModuleUnit X)).val.app (op U) (1 : Γ(X, U)))) hb
  change p.hom.val.app (op V)
      ((R.map v).val.app (op V) ((eta.app (schemeModuleUnit X)).val.app (op U) (1 : Γ(X, U)))) =
    (Scheme.Modules.restrictUnitIso f).hom.val.app (op V)
      ((eta.app (schemeModuleUnit X)).val.app (op U) (1 : Γ(X, U))) at h
  rw [← hn]
  change p.hom.val.app (op V)
      ((R.map v).val.app (op V) _) = (1 : Γ(Y, V))
  rw [h]
  change (f.appIso V).hom (X.presheaf.map _ (1 : Γ(X, U))) = 1
  simp only [map_one]

end PfaffianDescent
