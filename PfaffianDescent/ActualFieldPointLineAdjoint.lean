import PfaffianDescent.ActualFieldPointModuleLineHom

/- SOURCE ONLY / UNVERIFIED. The GENUINE sheaf adjoint, with exact point
functional and point Epi. Global Epi is deliberately a distinct obligation. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

def actualFieldPointLineAdjoint
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules)
    (ell : (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M) →ₗ[L] L) :
    M ⟶ (Scheme.Modules.pushforward q).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) :=
  (Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _
    (actualFieldPointModuleLineHom ((Scheme.Modules.pullback q).obj M) ell)

/-- The inverse actual adjunction gives EXACTLY the derived point sheaf map. -/
theorem actualFieldPointLineAdjoint_inverseAdjunction
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules)
    (ell : (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M) →ₗ[L] L) :
    ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).symm
      (actualFieldPointLineAdjoint q M ell) =
        actualFieldPointModuleLineHom ((Scheme.Modules.pullback q).obj M) ell :=
  ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).symm_apply_apply _

theorem actualFieldPointLineAdjoint_exact_functional
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules)
    (ell : (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M) →ₗ[L] L)
    (w : (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M)) :
    affineGlobalSectionsUnitLinearEquiv
      ((moduleSpecΓFunctor (R := .of L)).map
        (((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).symm
          (actualFieldPointLineAdjoint q M ell)) w) = ell w := by
  rw [actualFieldPointLineAdjoint_inverseAdjunction]
  exact actualFieldPointModuleLineHom_gamma_apply _ ell w

/-- Actual pullback-side Epi is derived from surjectivity. This is NOT a
claim that taking the inverse adjoint automatically preserves Epi. -/
theorem actualFieldPointLineAdjoint_point_epi
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules)
    (ell : (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M) →ₗ[L] L)
    (hell : Function.Surjective ell) :
    Epi (((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).symm
      (actualFieldPointLineAdjoint q M ell)) := by
  rw [actualFieldPointLineAdjoint_inverseAdjunction]
  exact actualFieldPointModuleLineHom_epi _ ell hell

end PfaffianDescent
