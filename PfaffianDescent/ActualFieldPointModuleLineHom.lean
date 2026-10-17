import PfaffianDescent.ActualFieldPointModuleCounitIso
import PfaffianDescent.AffineQuotientPushforwardTilde
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Functor.EpiMono

/- SOURCE ONLY / UNVERIFIED. Actual sheaf line map derived from the point
Gamma functional; its map and Epi are proved, with no sheaf certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

def actualFieldPointModuleLineHom
    {L : Type u} [Field L] (M : (Spec (.of L)).Modules)
    (ell : (moduleSpecΓFunctor (R := .of L)).obj M →ₗ[L] L) :
    M ⟶ SheafOfModules.unit (Spec (.of L)).ringCatSheaf :=
  actualFieldPointModuleGamma_fullyFaithful.preimage (ModuleCat.ofHom
    ((affineGlobalSectionsUnitLinearEquiv (A := L)).symm.toLinearMap.comp ell))

theorem actualFieldPointModuleLineHom_gamma
    {L : Type u} [Field L] (M : (Spec (.of L)).Modules)
    (ell : (moduleSpecΓFunctor (R := .of L)).obj M →ₗ[L] L) :
    (moduleSpecΓFunctor (R := .of L)).map (actualFieldPointModuleLineHom M ell) =
      ModuleCat.ofHom ((affineGlobalSectionsUnitLinearEquiv (A := L)).symm.toLinearMap.comp ell) :=
  actualFieldPointModuleGamma_fullyFaithful.map_preimage _

theorem actualFieldPointModuleLineHom_gamma_apply
    {L : Type u} [Field L] (M : (Spec (.of L)).Modules)
    (ell : (moduleSpecΓFunctor (R := .of L)).obj M →ₗ[L] L)
    (w : (moduleSpecΓFunctor (R := .of L)).obj M) :
    affineGlobalSectionsUnitLinearEquiv
      ((moduleSpecΓFunctor (R := .of L)).map (actualFieldPointModuleLineHom M ell) w) = ell w := by
  rw [actualFieldPointModuleLineHom_gamma]
  exact (affineGlobalSectionsUnitLinearEquiv (A := L)).apply_symm_apply (ell w)

theorem actualFieldPointModuleLineHom_epi
    {L : Type u} [Field L] (M : (Spec (.of L)).Modules)
    (ell : (moduleSpecΓFunctor (R := .of L)).obj M →ₗ[L] L)
    (hell : Function.Surjective ell) : Epi (actualFieldPointModuleLineHom M ell) := by
  let F := moduleSpecΓFunctor (R := CommRingCat.of L)
  letI : F.Faithful := actualFieldPointModuleGamma_fullyFaithful.faithful
  have hMap : Epi (F.map (actualFieldPointModuleLineHom M ell)) := by
    rw [actualFieldPointModuleLineHom_gamma, ModuleCat.epi_iff_surjective]
    exact (affineGlobalSectionsUnitLinearEquiv (A := L)).symm.surjective.comp hell
  exact F.epi_of_epi_map hMap

end PfaffianDescent
