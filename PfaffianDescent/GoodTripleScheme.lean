import PfaffianDescent.GoodGraphCoordinates
import PfaffianDescent.BilinearAlternating
import PfaffianDescent.IncidenceProper

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
section
variable (R : Type*) [CommRing R]

lemma goodTriple_bilinear_isAlt (k : Fin 3) : (goodTriple k : Mat R 6).toBilin'.IsAlt := by
  fin_cases k <;> intro x <;>
    simp [Matrix.toBilin'_apply, goodTriple, Fin.sum_univ_six] <;> ring

/-- The displayed matrices as actual alternating forms in the global ambient basis. -/
noncomputable def goodAmbientAlternatingForm (k : Fin 3) :
    AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)) :=
  (alternatingOfBilinear (goodTriple k : Mat R 6).toBilin' (goodTriple_bilinear_isAlt R k)).compLinearMap
    (incidenceAmbientBasis R).equivFun.toLinearMap

lemma goodAmbientAlternatingForm_pair (k : Fin 3) (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodAmbientAlternatingForm R k ![x, y] =
      (goodTriple k : Mat R 6).toBilin' ((incidenceAmbientBasis R).equivFun x)
        ((incidenceAmbientBasis R).equivFun y) := by
  rw [goodAmbientAlternatingForm, alternating_comp_pair]
  rfl

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma matrixBilinear_map (φ : R →+* S) (M : Mat R 6) (x y : Fin 6 → R) :
    (M.map φ).toBilin' (φ ∘ x) (φ ∘ y) = φ (M.toBilin' x y) := by
  simp [Matrix.toBilin'_apply, map_sum, map_mul]

lemma incidenceAmbientBasis_coordinates_map (φ : R →+* S)
    (x : (Fin 3 → R) × (Fin 3 → R)) :
    (incidenceAmbientBasis S).equivFun (φ ∘ x.1, φ ∘ x.2) =
      φ ∘ (incidenceAmbientBasis R).equivFun x := by
  rw [incidenceAmbientBasis_coordinates, incidenceAmbientBasis_coordinates]
  funext i
  fin_cases i <;> rfl

lemma goodAmbientAlternatingForm_map (φ : R →+* S) (k : Fin 3)
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodAmbientAlternatingForm S k ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
      φ (goodAmbientAlternatingForm R k ![x, y]) := by
  rw [goodAmbientAlternatingForm_pair, goodAmbientAlternatingForm_pair,
    incidenceAmbientBasis_coordinates_map, incidenceAmbientBasis_coordinates_map]
  have ht : (goodTriple k : Mat R 6).map φ = goodTriple k := congrFun (goodTriple_map φ) k
  rw [← ht]
  exact matrixBilinear_map φ _ _ _

end
section
variable (R : Type*) [CommRing R]

/-- The forty-five coefficients of the displayed triple in the ambient alternating basis. -/
noncomputable def goodTripleSchemeCoefficients (k : AlternatingTripleIndex) : R :=
  alternatingCoordinates (incidenceAmbientBasis R) (goodAmbientAlternatingForm R k.1) k.2

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma goodTripleSchemeCoefficients_map (φ : R →+* S) (k : AlternatingTripleIndex) :
    goodTripleSchemeCoefficients S k = φ (goodTripleSchemeCoefficients R k) :=
  incidenceAmbientCoordinates_map φ _ _ (goodAmbientAlternatingForm_map φ k.1) k.2

end
universe u
section
variable (K : Type u) [CommRing K]

/-- The displayed integral triple defines a section of the actual parameter scheme. -/
noncomputable def goodTripleSection : Spec (.of K) ⟶ alternatingTripleScheme K :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := K) (goodTripleSchemeCoefficients K)).toRingHom)

lemma goodTripleSection_toBase : goodTripleSection K ≫ alternatingTripleToBase K = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := K) (goodTripleSchemeCoefficients K)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (AlternatingTripleRing K))) = _
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap K (AlternatingTripleRing K)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (R := K) (goodTripleSchemeCoefficients K)).toRingHom =
      𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    exact (MvPolynomial.aeval (R := K) (goodTripleSchemeCoefficients K)).comp_algebraMap
  rw [he, Spec.map_id]

/-- The actual scheme-theoretic fiber of the global incidence over the displayed triple. -/
noncomputable def goodIncidenceFiber : Scheme.{u} :=
  pullback (incidenceToTriples K) (goodTripleSection K)

noncomputable def goodIncidenceFiberToBase : goodIncidenceFiber K ⟶ Spec (.of K) :=
  pullback.snd _ _

instance goodIncidenceFiberToBase_proper [IsNoetherianRing K] :
    IsProper (goodIncidenceFiberToBase K) :=
  inferInstanceAs (IsProper (pullback.snd (incidenceToTriples K) (goodTripleSection K)))

end
end PfaffianDescent
