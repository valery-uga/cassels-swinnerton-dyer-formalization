import PfaffianDescent.SchemeModuleGlobalSectionsTop
import PfaffianDescent.AffineQuotientPushforwardTilde

/- SOURCE ONLY / UNVERIFIED. Actual Gamma, with its tilde-adjunction scalar
structure, equals genuine morphism-valued sections at the SAME field point. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite BundleSectionZeroLocus
universe u

def actualFieldGammaSectionLinearEquiv
    {L : Type u} [Field L] (M : (Spec (.of L)).Modules) :
    SchemeModuleGlobalSectionsOver (𝟙 (Spec (.of L))) M ≃ₗ[L]
      (moduleSpecΓFunctor (R := .of L)).obj M where
  __ := schemeModuleGlobalSectionsAddEquivOpenTop (𝟙 (Spec (.of L))) M
  map_smul' c s := by
    let r : Γ(Spec (.of L), ⊤) := (Scheme.ΓSpecIso (.of L)).inv c
    have hval : (schemeModuleConstantEndomorphism (𝟙 (Spec (.of L))) c).app ⊤
        (1 : Γ(Spec (.of L), ⊤)) = r := by
      change unitEndomorphismValue (unitEndomorphismOfRegularFunction
        (affineFunctionHom (𝟙 (Spec (.of L))) c)) = r
      rw [unitEndomorphismValue_ofRegularFunction]
      simp only [affineFunctionHom, Scheme.Hom.id_appTop, Category.comp_id, r]
    change s.app ⊤ ((schemeModuleConstantEndomorphism (𝟙 (Spec (.of L))) c).app ⊤
      (1 : Γ(Spec (.of L), ⊤))) =
      r • s.app ⊤ (1 : Γ(Spec (.of L), ⊤))
    rw [hval]
    have hrone : r • (1 : Γ(Spec (.of L), ⊤)) = r := by
      change r * 1 = r
      exact mul_one r
    calc
      s.app ⊤ r = s.app ⊤ (r • (1 : Γ(Spec (.of L), ⊤))) :=
        congrArg (fun q : Γ(Spec (.of L), ⊤) => s.app ⊤ q) hrone.symm
      _ = r • s.app ⊤ (1 : Γ(Spec (.of L), ⊤)) :=
        Scheme.Modules.Hom.app_smul s r (1 : Γ(Spec (.of L), ⊤))

@[simp] lemma actualFieldGammaSectionLinearEquiv_comp
    {L : Type u} [Field L] {M N : (Spec (.of L)).Modules}
    (s : SchemeModuleGlobalSectionsOver (𝟙 (Spec (.of L))) M) (f : M ⟶ N) :
    actualFieldGammaSectionLinearEquiv N (s ≫ f) =
      (moduleSpecΓFunctor (R := .of L)).map f (actualFieldGammaSectionLinearEquiv M s) := rfl

end PfaffianDescent
