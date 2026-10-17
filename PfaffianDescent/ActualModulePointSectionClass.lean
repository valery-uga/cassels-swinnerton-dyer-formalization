import PfaffianDescent.ActualFieldGammaSectionLinearEquiv
import PfaffianDescent.CubicPointTraceFieldBaseChangeConstantPullback

/- SOURCE ONLY / UNVERIFIED. Pull an actual morphism-valued section to
its actual field-point fiber, with the scalar computed by the original
structure-sheaf morphism. No section-comparison certificate is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
universe u
attribute [local instance] isIso_pullbackUnitComparison
set_option backward.isDefEq.respectTransparency false

def actualModulePointSectionClass
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules) :
    (schemeModuleUnit X ⟶ M) →+
      (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M) where
  toFun s := by
    letI : IsIso (pullbackUnitComparison q) := isIso_pullbackUnitComparison q
    exact actualFieldGammaSectionLinearEquiv ((Scheme.Modules.pullback q).obj M)
      (inv (pullbackUnitComparison q) ≫ (Scheme.Modules.pullback q).map s)
  map_zero' := by
    simp only [Functor.map_zero, Limits.comp_zero, map_zero]
  map_add' s t := by
    rw [Functor.map_add, Preadditive.comp_add, map_add]

lemma actualModulePointSectionClass_regularFunction
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules)
    (a : Γ(X, ⊤)) (s : schemeModuleUnit X ⟶ M) :
    actualModulePointSectionClass q M (unitEndomorphismOfRegularFunction a ≫ s) =
      (Scheme.ΓSpecIso (.of L)).hom (q.appTop a) •
        actualModulePointSectionClass q M s := by
  let P := Scheme.Modules.pullback q
  let u := pullbackUnitComparison q
  letI : IsIso u := isIso_pullbackUnitComparison q
  have hu : inv u ≫ P.map (unitEndomorphismOfRegularFunction a) =
      unitEndomorphismOfRegularFunction (q.appTop a) ≫ inv u := by
    apply (cancel_mono u).1
    have hnat := cubicPointTraceFieldBaseChange_pullbackUnit_regularFunction q a
    change P.map (unitEndomorphismOfRegularFunction a) ≫ u =
      u ≫ unitEndomorphismOfRegularFunction (q.appTop a) at hnat
    calc
      (inv u ≫ P.map (unitEndomorphismOfRegularFunction a)) ≫ u =
          inv u ≫ (u ≫ unitEndomorphismOfRegularFunction (q.appTop a)) := by
        rw [Category.assoc, hnat]
      _ = unitEndomorphismOfRegularFunction (q.appTop a) := by
        rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      _ = (unitEndomorphismOfRegularFunction (q.appTop a) ≫ inv u) ≫ u := by
        rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have ha : unitEndomorphismOfRegularFunction (q.appTop a) =
      schemeModuleConstantEndomorphism (𝟙 (Spec (.of L)))
        ((Scheme.ΓSpecIso (.of L)).hom (q.appTop a)) := by
    unfold schemeModuleConstantEndomorphism affineFunctionHom
    simp only [Scheme.Hom.id_appTop, Category.comp_id]
    rw [Iso.hom_inv_id_apply]
  change actualFieldGammaSectionLinearEquiv (P.obj M)
      (inv u ≫ P.map (unitEndomorphismOfRegularFunction a ≫ s)) = _
  rw [Functor.map_comp, ← Category.assoc, hu, Category.assoc, ha]
  exact (actualFieldGammaSectionLinearEquiv (P.obj M)).map_smul
    ((Scheme.ΓSpecIso (.of L)).hom (q.appTop a))
    (inv u ≫ P.map s)

end PfaffianDescent
