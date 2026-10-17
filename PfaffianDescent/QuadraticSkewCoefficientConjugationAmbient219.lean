import AllCharacteristics.HomogeneousProjectiveAmbient
import PfaffianDescent.GradedSurjection

/-! SOURCE ONLY. The actual semilinear projective ambient automorphism.
The inverse coefficient hom on coordinate rings sends vector points to σv. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.GeometricLines219
open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {E : Type u} [Field E]
attribute [local instance] MvPolynomial.gradedAlgebra

def coefficientConjugationGradedHom219 (σ : E ≃+* E) :
    homogeneousSubmodule (Fin 4) E →+*ᵍ homogeneousSubmodule (Fin 4) E where
  __ := MvPolynomial.map σ.toRingHom
  map_mem hp := hp.map σ.toRingHom

def coefficientConjugationAmbientIso219 (σ : E ≃+* E) :
    Proj (homogeneousSubmodule (Fin 4) E) ≅ Proj (homogeneousSubmodule (Fin 4) E) := by
  let F := coefficientConjugationGradedHom219 σ
  let G := coefficientConjugationGradedHom219 σ.symm
  have hF : Function.Surjective F := (MvPolynomial.mapEquiv (Fin 4) σ).surjective
  have hG : Function.Surjective G := (MvPolynomial.mapEquiv (Fin 4) σ.symm).surjective
  let hf := gradedSurjective_irrelevant_le F hF
  let hg := gradedSurjective_irrelevant_le G hG
  have hGF : G.comp F = GradedRingHom.id (homogeneousSubmodule (Fin 4) E) := by
    apply GradedRingHom.ext
    intro p
    exact (MvPolynomial.mapEquiv (Fin 4) σ).symm_apply_apply p
  have hFG : F.comp G = GradedRingHom.id (homogeneousSubmodule (Fin 4) E) := by
    apply GradedRingHom.ext
    intro p
    exact (MvPolynomial.mapEquiv (Fin 4) σ).apply_symm_apply p
  refine { hom := Proj.map G hg
           inv := Proj.map F hf
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · rw [← Proj.map_comp F G hf hg]
    simpa only [hGF] using (Proj.map_id (𝒜 := homogeneousSubmodule (Fin 4) E))
  · rw [← Proj.map_comp G F hg hf]
    simpa only [hFG] using (Proj.map_id (𝒜 := homogeneousSubmodule (Fin 4) E))

theorem coefficientConjugationAmbientIso_hom_ideal219
    (σ : E ≃+* E) (x : Proj (homogeneousSubmodule (Fin 4) E)) :
    ((coefficientConjugationAmbientIso219 σ).hom x).asHomogeneousIdeal.toIdeal =
      x.asHomogeneousIdeal.toIdeal.comap (MvPolynomial.map σ.symm.toRingHom) := by
  rfl

theorem actual_ambient_square_projective_image_eq219
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
    (a : Proj (homogeneousSubmodule (Fin 4) E) ≅ Proj (homogeneousSubmodule (Fin 4) E))
    (e : AllCharacteristics.HomogeneousProjective.scheme I ≅
      AllCharacteristics.HomogeneousProjective.scheme J)
    (hSquare : e.hom ≫ AllCharacteristics.HomogeneousProjective.quotientProjMap J =
      AllCharacteristics.HomogeneousProjective.quotientProjMap I ≫ a.hom) :
    Set.image a.hom (Set.range (AllCharacteristics.HomogeneousProjective.quotientProjMap I)) =
      Set.range (AllCharacteristics.HomogeneousProjective.quotientProjMap J) := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, ⟨u, rfl⟩, rfl⟩
    refine ⟨e.hom u, ?_⟩
    calc
      quotientProjMap J (e.hom u) = (e.hom ≫ quotientProjMap J) u :=
        (Scheme.Hom.comp_apply e.hom (quotientProjMap J) u).symm
      _ = (quotientProjMap I ≫ a.hom) u :=
        congrArg (fun f : scheme I ⟶ Proj (homogeneousSubmodule (Fin 4) E) => f u) hSquare
      _ = a.hom (quotientProjMap I u) := Scheme.Hom.comp_apply _ _ u
  · rintro x ⟨v, rfl⟩
    refine ⟨quotientProjMap I (e.inv v), ⟨e.inv v, rfl⟩, ?_⟩
    have he : e.hom (e.inv v) = v := by
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
      rfl
    calc
      a.hom (quotientProjMap I (e.inv v)) = (quotientProjMap I ≫ a.hom) (e.inv v) :=
        (Scheme.Hom.comp_apply _ _ _).symm
      _ = (e.hom ≫ quotientProjMap J) (e.inv v) :=
        congrArg (fun f : scheme I ⟶ Proj (homogeneousSubmodule (Fin 4) E) =>
          f (e.inv v)) hSquare.symm
      _ = quotientProjMap J (e.hom (e.inv v)) := Scheme.Hom.comp_apply _ _ _
      _ = quotientProjMap J v := congrArg (quotientProjMap J) he

end PfaffianDescent.QuadraticSkewRationality.GeometricLines219
