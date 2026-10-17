import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationMap
import PfaffianDescent.AffineFreeModuleBaseChange
import PfaffianDescent.SchemeModuleGlobalSectionsTop

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual structural square identifies the F-action on actual point
sections with restriction of the native E-moduleSpecGamma action. -/
def cubicClosedPointSerreSurfaceJetCotangent_pointNativeGammaOverLinearEquiv
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (p : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of F))
    (hp : p = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    (N : (Spec (CommRingCat.of E)).Modules) :
    SchemeModuleGlobalSectionsOver p N ≃ₗ[F]
      (ModuleCat.restrictScalars (algebraMap F E)).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of E)).obj N) := by
  let q := schemeModuleGlobalSectionsLinearEquivOpenTop p N
  let a : SchemeModuleOpenSectionsOver p N ⊤ ≃ₗ[F]
      (ModuleCat.restrictScalars (algebraMap F E)).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of E)).obj N) :=
    { toFun := fun s => s
      invFun := fun s => s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' c s := by
        let y : N.presheaf.obj (op ⊤) := s
        change (schemeOpenBaseRingHom p ⊤ c) • y =
          ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom (algebraMap F E c)) • y
        congr 1
        apply (Scheme.ΓSpecIso (CommRingCat.of E)).commRingCatIsoToRingEquiv.injective
        change (Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom
          (schemeOpenBaseRingHom p ⊤ c) =
          (Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom
            ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom (algebraMap F E c))
        rw [hp, schemeOpenBaseRingHom_top_apply, gammaSpec_baseRingHom_apply]
        simp }
  exact q.trans a

end PfaffianDescent
