import PfaffianDescent.SchemeModuleGlobalSections
import PfaffianDescent.VoisinVeryAmpleQuadraticSections

/-!
# Sheaf-section multiplication in Voisin's fixed-component argument

This file connects multiplication of genuine global sections of module
sheaves to the bilinear linear-algebra endpoint for Voisin's degree-eight
fixed-component contradiction.
-/

namespace PfaffianDescent

open CategoryTheory AlgebraicGeometry MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- Multiply two genuine sheaf sections and then express the result in the
quadratic graded piece of a cubic surface. -/
noncomputable def cubicSurfaceSchemeModuleSectionProduct
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M N P : X.Modules) (e : schemeModuleTensor M N ≅ P)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (coordinate : SchemeModuleGlobalSectionsOver base P →ₗ[K]
      grading (equationIdeal p hp) 2) :
    SchemeModuleGlobalSectionsOver base M →ₗ[K]
      SchemeModuleGlobalSectionsOver base N →ₗ[K]
        grading (equationIdeal p hp) 2 :=
  (schemeModuleGlobalSectionProductLinearMap base M N P e).compr₂ coordinate

@[simp]
theorem cubicSurfaceSchemeModuleSectionProduct_apply
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M N P : X.Modules) (e : schemeModuleTensor M N ≅ P)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (coordinate : SchemeModuleGlobalSectionsOver base P →ₗ[K]
      grading (equationIdeal p hp) 2)
    (s : SchemeModuleGlobalSectionsOver base M)
    (t : SchemeModuleGlobalSectionsOver base N) :
    cubicSurfaceSchemeModuleSectionProduct base M N P e p hp coordinate s t =
      coordinate (schemeModuleGlobalSectionProduct base M N P e s t) := rfl

set_option linter.style.haveILetI false in
/-- Sheaf-theoretic form of Voisin's meeting fixed-component contradiction.
The product in every hypothesis is the genuine multiplication of global
sections induced by `M ⊗ N ≅ P`, followed by the chosen identification of
sections of `P` with cubic-surface quadrics. -/
theorem
    cubicSurface_degreeEight_fixedComponent_meets_contradiction_of_schemeModuleSections
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M N P : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base N)]
    (e : schemeModuleTensor M N ≅ P)
    (coordinate : SchemeModuleGlobalSectionsOver base P →ₗ[K]
      grading (equationIdeal p hp) 2)
    (a₀ : SchemeModuleGlobalSectionsOver base M)
    (b₀ : SchemeModuleGlobalSectionsOver base N)
    (ev : LinearMap.range
        ((cubicSurfaceSchemeModuleSectionProduct base M N P e p hp coordinate).flip b₀) →ₗ[K]
      (Fin 8 → K))
    (heval : Function.Surjective ev)
    (hsection : ∃ q : LinearMap.range
        ((cubicSurfaceSchemeModuleSectionProduct base M N P e p hp coordinate).flip b₀),
      q ≠ 0 ∧ ev q = 0)
    (htwo : 2 ≤ finrank K (SchemeModuleGlobalSectionsOver base N))
    (hmovingInjective : Function.Injective
      (cubicSurfaceSchemeModuleSectionProduct base M N P e p hp coordinate a₀))
    (hq0 : cubicSurfaceSchemeModuleSectionProduct base M N P e p hp coordinate a₀ b₀ ≠ 0)
    (hcross : ∀ a b,
      cubicSurfaceSchemeModuleSectionProduct base M N P e p hp coordinate a b₀ =
        cubicSurfaceSchemeModuleSectionProduct base M N P e p hp coordinate a₀ b →
      ∃ c : K, a = c • a₀ ∧ b = c • b₀)
    (x : cubicSurfaceAffinePoints p)
    (hfixedVanishes : ∀ a,
      cubicSurfacePointCoordinateRingEvaluation p hp x
        (cubicSurfaceSchemeModuleSectionProduct base M N P e p hp coordinate a b₀) = 0)
    (hmovingVanishes : ∀ b,
      cubicSurfacePointCoordinateRingEvaluation p hp x
        (cubicSurfaceSchemeModuleSectionProduct base M N P e p hp coordinate a₀ b) = 0) :
    False := by
  exact
    cubicSurface_degreeEight_fixedComponent_meets_contradiction_of_bilinearProduct
      p hp hne
      (cubicSurfaceSchemeModuleSectionProduct base M N P e p hp coordinate)
      a₀ b₀ ev heval hsection htwo hmovingInjective hq0 hcross x
      hfixedVanishes hmovingVanishes

end

end PfaffianDescent
