import PfaffianDescent.GoodTripleScheme

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
section
variable (R : Type*) [CommRing R]

/-- The first two displayed forms, with the third restriction set to zero. -/
noncomputable def goodPairAmbientAlternatingForm (k : Fin 3) :
    AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)) :=
  if k = 2 then 0 else goodAmbientAlternatingForm R k

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma goodPairAmbientAlternatingForm_map (φ : R →+* S) (k : Fin 3)
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodPairAmbientAlternatingForm S k ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
      φ (goodPairAmbientAlternatingForm R k ![x, y]) := by
  by_cases h : k = 2
  · simp [goodPairAmbientAlternatingForm, h]
  · simpa only [goodPairAmbientAlternatingForm, if_neg h] using goodAmbientAlternatingForm_map φ k x y

end
section
variable (R : Type*) [CommRing R]

/-- The forty-five coefficients of the displayed triple in the ambient alternating basis. -/
noncomputable def goodPairTripleSchemeCoefficients (k : AlternatingTripleIndex) : R :=
  alternatingCoordinates (incidenceAmbientBasis R) (goodPairAmbientAlternatingForm R k.1) k.2

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma goodPairTripleSchemeCoefficients_map (φ : R →+* S) (k : AlternatingTripleIndex) :
    goodPairTripleSchemeCoefficients S k = φ (goodPairTripleSchemeCoefficients R k) :=
  incidenceAmbientCoordinates_map φ _ _ (goodPairAmbientAlternatingForm_map φ k.1) k.2

end
universe u
section
variable (K : Type u) [CommRing K]

/-- The first two forms with the third form zero defines a section of the actual parameter scheme. -/
noncomputable def goodPairTripleSection : Spec (.of K) ⟶ alternatingTripleScheme K :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := K) (goodPairTripleSchemeCoefficients K)).toRingHom)

lemma goodPairTripleSection_toBase : goodPairTripleSection K ≫ alternatingTripleToBase K = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := K) (goodPairTripleSchemeCoefficients K)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (AlternatingTripleRing K))) = _
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap K (AlternatingTripleRing K)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (R := K) (goodPairTripleSchemeCoefficients K)).toRingHom =
      𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    exact (MvPolynomial.aeval (R := K) (goodPairTripleSchemeCoefficients K)).comp_algebraMap
  rw [he, Spec.map_id]

/-- The actual scheme-theoretic fiber of the global incidence over the first two forms with the third form zero. -/
noncomputable def goodPairIncidenceFiber : Scheme.{u} :=
  pullback (incidenceToTriples K) (goodPairTripleSection K)

noncomputable def goodPairIncidenceFiberToBase : goodPairIncidenceFiber K ⟶ Spec (.of K) :=
  pullback.snd _ _

instance goodPairIncidenceFiberToBase_proper [IsNoetherianRing K] :
    IsProper (goodPairIncidenceFiberToBase K) :=
  inferInstanceAs (IsProper (pullback.snd (incidenceToTriples K) (goodPairTripleSection K)))

end
end PfaffianDescent
