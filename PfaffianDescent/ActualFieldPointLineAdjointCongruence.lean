import PfaffianDescent.ActualFieldPointLineAdjoint

/- SOURCE ONLY / UNVERIFIED. Actual morphism equality transports BOTH sides
of the sheaf adjunction; no desired point/restriction square is input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

lemma actualFieldPointLineAdjoint_morphism_congr
    {L : Type u} [Field L] {X : Scheme.{u}}
    {q q' : Spec (.of L) ⟶ X} (h : q = q') (M : X.Modules)
    (ell : (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q').obj M) →ₗ[L] L) :
    actualFieldPointLineAdjoint q M
      (ell.comp ((moduleSpecΓFunctor (R := .of L)).map
        ((Scheme.Modules.pullbackCongr h).hom.app M)).hom) ≫
      (Scheme.Modules.pushforwardCongr h).hom.app
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) =
      actualFieldPointLineAdjoint q' M ell := by
  subst q'
  have hEll : ell.comp ((moduleSpecΓFunctor (R := .of L)).map
      ((Scheme.Modules.pullbackCongr rfl).hom.app M)).hom = ell := by
    ext w
    simp [Scheme.Modules.pullbackCongr]
  have hPush : (Scheme.Modules.pushforwardCongr (show q = q from rfl)).hom.app
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    simp
  rw [hEll, hPush, Category.comp_id]

end PfaffianDescent
