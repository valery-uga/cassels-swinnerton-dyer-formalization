import PfaffianDescent.IncidenceCoordinateRecovery
import PfaffianDescent.AlternatingEvaluation
import PfaffianDescent.GrassmannianQuotientBaseChange

namespace PfaffianDescent
open Module TensorProduct
section
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

lemma incidenceAmbientBasis_graphCoefficientMap (i : Fin 6) (x : (Fin 3 → R) × (Fin 3 → R)) :
    (incidenceAmbientBasis S).coord i (graphCoefficientMap φ x) =
      φ ((incidenceAmbientBasis R).coord i x) := incidenceAmbientBasis_coord_map φ i x

/-- Coefficient extension of a function is a semilinear map. -/
def coefficientFunctionMap (ι : Type*) : (ι → R) →ₛₗ[φ] (ι → S) where
  toFun c := φ ∘ c
  map_add' x y := by funext i; exact map_add φ _ _
  map_smul' r x := by funext i; exact map_mul φ _ _

/-- Extend an actual ambient alternating form by extending its fifteen coefficients. -/
noncomputable def ambientAlternatingMap :
    AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)) →ₛₗ[φ]
      AlternatingTwoForms S ((Fin 3 → S) × (Fin 3 → S)) :=
  (alternatingCoordinates (incidenceAmbientBasis S)).symm.toLinearMap.comp
    ((coefficientFunctionMap φ (Set.powersetCard (Fin 6) 2)).comp
      (alternatingCoordinates (incidenceAmbientBasis R)).toLinearMap)

lemma ambientAlternatingMap_coordinates (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) :
    alternatingCoordinates (incidenceAmbientBasis S) (ambientAlternatingMap φ B) =
      φ ∘ alternatingCoordinates (incidenceAmbientBasis R) B :=
  (alternatingCoordinates (incidenceAmbientBasis S)).apply_symm_apply _

/-- Form evaluation commutes with arbitrary scalar extension, including nonflat extensions. -/
lemma ambientAlternatingMap_apply (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)))
    (v : Fin 2 → (Fin 3 → R) × (Fin 3 → R)) :
    ambientAlternatingMap φ B (graphCoefficientMap φ ∘ v) = φ (B v) := by
  rw [alternating_evaluation_coordinates (incidenceAmbientBasis S),
    alternating_evaluation_coordinates (incidenceAmbientBasis R), ambientAlternatingMap_coordinates, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [Function.comp_apply, incidenceAmbientBasis_graphCoefficientMap, map_mul]
  rw [RingHom.map_det]
  rfl

end
section
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- The ambient alternating-form coefficient extension is actual tensor-product base change. -/
noncomputable def ambientAlternatingTensorEquiv :
    S ⊗[R] AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[S]
      AlternatingTwoForms S ((Fin 3 → S) × (Fin 3 → S)) :=
  ((alternatingCoordinates (incidenceAmbientBasis R)).baseChange R S _ _).trans
    ((TensorProduct.piScalarRight R S S (Set.powersetCard (Fin 6) 2)).trans
      (alternatingCoordinates (incidenceAmbientBasis S)).symm)

lemma ambientAlternatingTensorEquiv_one_tmul
    (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) :
    ambientAlternatingTensorEquiv R S (1 ⊗ₜ[R] B) = ambientAlternatingMap (algebraMap R S) B := by
  apply (alternatingCoordinates (incidenceAmbientBasis S)).injective
  rw [ambientAlternatingMap_coordinates]
  rw [ambientAlternatingTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.baseChange_tmul]
  funext i
  simp [Algebra.smul_def, Function.comp_def]

end
end PfaffianDescent
