import PfaffianDescent.IncidenceQuotientMorphism
import PfaffianDescent.AlternatingSpanRestriction
import Mathlib.RingTheory.LocalProperties.Basic

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A]

lemma alternatingTripleEvaluation_exists (f : Spec (.of A) ⟶ alternatingTripleScheme K)
    (hf : f ≫ alternatingTripleToBase K = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    ∃ B : Fin 3 → AlternatingTwoForms A ((Fin 3 → A) × (Fin 3 → A)),
      alternatingTripleEvaluation K B = f := by
  obtain ⟨c, hc⟩ := polynomialSchemeEvaluation_exists K AlternatingTripleIndex f hf
  let B := fun k : Fin 3 => (alternatingCoordinates (incidenceAmbientBasis A)).symm (fun s => c (k, s))
  have he : alternatingTripleCoordinates B = c := by
    funext i
    exact congrFun ((alternatingCoordinates (incidenceAmbientBasis A)).apply_symm_apply (fun s => c (i.1, s))) i.2
  refine ⟨B, ?_⟩
  change polynomialSchemeEvaluation K AlternatingTripleIndex (alternatingTripleCoordinates B) = f
  rw [he]
  exact hc

lemma incidenceOriginalForm_restriction_zero (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (p : IncidenceGraphPoints A) (k : Fin 3) :
    alternatingRestriction A _ (grassmannianChartSubmodule A σ (LinearMap.toMatrix' p.1))
      (incidenceOriginalForm σ p k) = 0 := by
  apply alternatingTransport_isotropic (graphCoordinatePermutation A σ.symm)
    p.1.graph _ _ (p.2 k).1 (p.2 k).2
  simp only [grassmannianChartSubmodule, Matrix.toLin'_toMatrix']

/-- Every local-ring-valued incidence point satisfies the actual isotropy equations. -/
lemma incidence_scheme_isotropic_local [IsLocalRing A]
    (W : Module.Grassmannian A ((Fin 3 → A) × (Fin 3 → A)) 3)
    (B : Fin 3 → AlternatingTwoForms A ((Fin 3 → A) × (Fin 3 → A)))
    (f : Spec (.of A) ⟶ incidenceScheme K)
    (hW : f ≫ incidenceToGrassmannian K = grassmannianQuotientMorphism K W)
    (hB : f ≫ incidenceToTriples K = alternatingTripleEvaluation K B) :
    ∀ k, alternatingRestriction A _ W.toSubmodule (B k) = 0 := by
  have hf : f ≫ incidenceToBase K = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
    rw [← incidenceToTriples_toBase, ← Category.assoc, hB]
    exact alternatingTripleEvaluation_toBase K B
  obtain ⟨σ, p, hp⟩ := incidence_local_algebra_point K f hf
  have hQ : grassmannianChartQuotient A σ (LinearMap.toMatrix' p.1) = W := by
    apply grassmannianQuotientAlgebraPoint_injective K
    rw [grassmannianQuotientAlgebraPoint_chart]
    apply Subtype.ext
    calc
      _ = (incidenceChartEvaluation K p ≫ incidenceGraphToGrassmannianChart K) ≫
          grassmannianChartι K σ := by rw [incidenceChartEvaluation_toGraph]; rfl
      _ = (incidenceChartEvaluation K p ≫ incidenceChartι K σ) ≫ incidenceToGrassmannian K := by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun g => incidenceChartEvaluation K p ≫ g)
            (incidenceChartι_toGrassmannian K σ).symm).trans (Category.assoc _ _ _).symm)
      _ = _ := (congrArg (fun g => g ≫ incidenceToGrassmannian K) hp).trans hW
  have hT : (fun k => incidenceOriginalForm σ p k) = B := by
    apply alternatingTripleEvaluation_injective K
    exact (incidenceChartEvaluation_toTriples K σ p).symm.trans
      ((congrArg (fun g => incidenceChartEvaluation K p ≫ g)
        (incidenceChartι_toTriples K σ).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun g => g ≫ incidenceToTriples K) hp).trans hB)))
  intro k
  rw [← hQ, ← hT]
  exact incidenceOriginalForm_restriction_zero σ p k

/-- Scheme-theoretic incidence implies vanishing on the actual kernel over every coefficient ring. -/
theorem incidence_scheme_isotropic
    (W : Module.Grassmannian A ((Fin 3 → A) × (Fin 3 → A)) 3)
    (B : Fin 3 → AlternatingTwoForms A ((Fin 3 → A) × (Fin 3 → A)))
    (f : Spec (.of A) ⟶ incidenceScheme K)
    (hW : f ≫ incidenceToGrassmannian K = grassmannianQuotientMorphism K W)
    (hB : f ≫ incidenceToTriples K = alternatingTripleEvaluation K B) :
    ∀ k, alternatingRestriction A _ W.toSubmodule (B k) = 0 := by
  intro k
  apply (alternatingRestriction_eq_zero_iff_pairs _ _).mpr
  intro x hx y hy
  apply eq_zero_of_localization
  intro J hJ
  let φ := IsScalarTower.toAlgHom K A (Localization.AtPrime J)
  let WJ := grassmannianQuotientMap φ.toRingHom W
  let BJ := fun k => ambientAlternatingMap φ.toRingHom (B k)
  let fJ := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f
  have hw : fJ ≫ incidenceToGrassmannian K = grassmannianQuotientMorphism K WJ := by
    rw [show fJ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f from rfl,
      Category.assoc, hW]
    exact grassmannianQuotientMorphism_naturality K W φ
  have hb : fJ ≫ incidenceToTriples K = alternatingTripleEvaluation K BJ := by
    rw [show fJ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f from rfl,
      Category.assoc, hB]
    exact alternatingTripleEvaluation_map K φ B
  have hi := incidence_scheme_isotropic_local K WJ BJ fJ hw hb k
  have hxJ : graphCoefficientMap φ.toRingHom x ∈ WJ.toSubmodule :=
    Submodule.subset_span ⟨x, hx, rfl⟩
  have hyJ : graphCoefficientMap φ.toRingHom y ∈ WJ.toSubmodule :=
    Submodule.subset_span ⟨y, hy, rfl⟩
  have he := (alternatingRestriction_eq_zero_iff_pairs _ _).mp hi
    _ hxJ _ hyJ
  exact (ambientAlternatingMap_apply φ.toRingHom (B k) ![x, y]).symm.trans he

end
end PfaffianDescent
