import PfaffianDescent.ActualPointLocalOpenRestrictionComparison
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-! SOURCE ONLY, UNVERIFIED. Genuine unit-defined local classes and the
existing morphism-valued point classes agree, including open transport. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

lemma actualPointLocalSectionClass_top_of_unitHom
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules) (v : schemeModuleUnit X ⟶ M) :
    actualPointLocalSectionClass q M ⊤ (by rfl)
      (v.val.app (op ⊤) (1 : Γ(X, ⊤))) = actualModulePointSectionClass q M v := by
  have h := actualGlobalPointAdjunctionSectionEvaluation q M
    ((Scheme.Modules.pullback q).obj M) v (𝟙 _)
  simp only [CategoryTheory.Functor.map_id, ModuleCat.id_apply, Adjunction.homEquiv_id] at h
  have hId (w : ((Scheme.Modules.pullback q).obj M).val.obj (op ⊤)) :
      ((Scheme.Modules.pullback q).obj M).val.map (𝟙 (op ⊤)) w = w :=
    ConcreteCategory.congr_hom (((Scheme.Modules.pullback q).obj M).val.map_id (op ⊤)) w
  exact (hId _).trans h.symm

lemma actualPointLocalSectionClass_eq_top
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules) (U : X.Opens)
    (hU : q ⁻¹ᵁ U = ⊤) (hTop : U = ⊤) (z : M.val.obj (op U)) :
    actualPointLocalSectionClass q M U hU z =
      actualPointLocalSectionClass q M ⊤ (by rfl)
        (M.val.map (eqToHom (congrArg op hTop)) z) := by
  subst U
  have hz : M.val.map (𝟙 (op ⊤)) z = z := ConcreteCategory.congr_hom (M.val.map_id (op ⊤)) z
  simpa only [eqToHom_refl, hz]

lemma actualPointLocalSectionClass_top_of_section
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (q : Spec (.of L) ⟶ X) (M : X.Modules)
    (z : Γ(M, ⊤)) :
    actualPointLocalSectionClass q M ⊤ (by rfl) z =
      actualModulePointSectionClass q M
        ((schemeModuleGlobalSectionsAddEquivOpenTop g M).symm z) := by
  let v := (schemeModuleGlobalSectionsAddEquivOpenTop g M).symm z
  have hz : v.val.app (op ⊤) (1 : Γ(X, ⊤)) = z :=
    (schemeModuleGlobalSectionsAddEquivOpenTop g M).apply_symm_apply z
  calc
    _ = actualPointLocalSectionClass q M ⊤ (by rfl)
        (v.val.app (op ⊤) (1 : Γ(X, ⊤))) :=
      congrArg (fun w => actualPointLocalSectionClass q M ⊤ (by rfl) w) hz.symm
    _ = actualModulePointSectionClass q M v :=
      actualPointLocalSectionClass_top_of_unitHom q M v

end PfaffianDescent
