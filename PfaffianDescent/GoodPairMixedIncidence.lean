import PfaffianDescent.GoodPairMixedForms
import PfaffianDescent.GoodChartIncidencePoints

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R]

lemma goodMixedPairChart_original (ε : Fin 3 → Bool) (k : Fin 3) :
    alternatingTransport (graphCoordinatePermutation R (goodMixedChartPermutation ε).symm)
      (goodMixedPairChartAlternatingForm R ε k) = goodPairAmbientAlternatingForm R k := by
  unfold goodMixedPairChartAlternatingForm
  rw [← graphCoordinatePermutation_symm]
  exact (alternatingTransport (graphCoordinatePermutation R (goodMixedChartPermutation ε))).symm_apply_apply _

lemma goodMixedPairChart_diagonal_isotropic (ε : Fin 3 → Bool) (u : Fin 3 → R) (k : Fin 3) :
    alternatingRestriction R _ (Matrix.toLin' (Matrix.diagonal u)).graph
      (goodMixedPairChartAlternatingForm R ε k) = 0 := by
  apply (alternatingRestriction_graph_eq_zero_iff _ _).mpr
  intro i j
  fin_cases k
  · apply (goodMixedPairChartAlternatingForm_zero_graph_entry R ε (Matrix.diagonal u) i j).trans
    by_cases h : i = j
    · subst j; simp
    · simp [Matrix.diagonal, h, Ne.symm h]
  · apply (goodMixedPairChartAlternatingForm_one_graph_entry R ε (Matrix.diagonal u) i j).trans
    by_cases h : i = j
    · subst j; simp
    · simp [Matrix.diagonal, h, Ne.symm h]
  · exact congrArg (fun B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)) =>
      B ![(Pi.single i 1, Matrix.toLin' (Matrix.diagonal u) (Pi.single i 1)),
        (Pi.single j 1, Matrix.toLin' (Matrix.diagonal u) (Pi.single j 1))])
        (goodMixedPairChartAlternatingForm_two R ε)

/-- A triple of affine slopes determines an actual first-two-form isotropic incidence point
in any of the eight standard charts. -/
noncomputable def goodMixedPairAffinePoint (ε : Fin 3 → Bool) (u : Fin 3 → R) : IncidenceGraphPoints R :=
  ⟨Matrix.toLin' (Matrix.diagonal u), fun k =>
    ⟨goodMixedPairChartAlternatingForm R ε k, goodMixedPairChart_diagonal_isotropic R ε u k⟩⟩

lemma goodMixedPairAffinePoint_original (ε : Fin 3 → Bool) (u : Fin 3 → R) (k : Fin 3) :
    incidenceOriginalForm (goodMixedChartPermutation ε) (goodMixedPairAffinePoint R ε u) k =
      goodPairAmbientAlternatingForm R k := goodMixedPairChart_original R ε k

lemma goodMixedPairAffinePoint_coefficients (ε : Fin 3 → Bool) (u : Fin 3 → R) :
    incidenceOriginalCoefficients (goodMixedChartPermutation ε) (goodMixedPairAffinePoint R ε u) =
      goodPairTripleSchemeCoefficients R := by
  funext k
  unfold incidenceOriginalCoefficients goodPairTripleSchemeCoefficients
  rw [goodMixedPairAffinePoint_original]

lemma goodMixedPairIncidence_forms (ε : Fin 3 → Bool) (p : IncidenceGraphPoints R)
    (hc : incidenceOriginalCoefficients (goodMixedChartPermutation ε) p = goodPairTripleSchemeCoefficients R)
    (k : Fin 3) : (p.2 k).1 = goodMixedPairChartAlternatingForm R ε k := by
  have hb : incidenceOriginalForm (goodMixedChartPermutation ε) p k = goodPairAmbientAlternatingForm R k := by
    apply (alternatingCoordinates (incidenceAmbientBasis R)).injective
    funext s
    exact congrFun hc (k, s)
  apply (alternatingTransport (graphCoordinatePermutation R (goodMixedChartPermutation ε).symm)).injective
  exact hb.trans (goodMixedPairChart_original R ε k).symm

lemma goodMixedPairIncidence_diagonal (h2 : IsUnit (2 : R)) (ε : Fin 3 → Bool) (p : IncidenceGraphPoints R)
    (hc : incidenceOriginalCoefficients (goodMixedChartPermutation ε) p = goodPairTripleSchemeCoefficients R) :
    LinearMap.toMatrix' p.1 = Matrix.diagonal (fun i => LinearMap.toMatrix' p.1 i i) := by
  apply goodMixedPairChart_diagonal R h2 ε
  intro k
  rw [Matrix.toLin'_toMatrix', ← goodMixedPairIncidence_forms R ε p hc k]
  exact (p.2 k).2

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma goodMixedPairChart_map (φ : R →+* S) (ε : Fin 3 → Bool) (k : Fin 3)
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodMixedPairChartAlternatingForm S ε k ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
      φ (goodMixedPairChartAlternatingForm R ε k ![x, y]) :=
  alternatingTransport_permutation_map φ (goodMixedChartPermutation ε) _ _
    (goodPairAmbientAlternatingForm_map φ k) x y

end
section
variable (K : Type*) [CommRing K]

/-- Universal affine slopes, retained with their actual incidence forms. -/
noncomputable def goodMixedPairUniversalPoint (ε : Fin 3 → Bool) :
    IncidenceGraphPoints (MvPolynomial (Fin 3) K) :=
  goodMixedPairAffinePoint _ ε MvPolynomial.X

variable {A : Type*} [CommRing A] [Algebra K A]

noncomputable def goodMixedPairIncidenceLift (p : IncidenceGraphPoints A) :
    MvPolynomial (Fin 3) K →ₐ[K] A := MvPolynomial.aeval (fun i => LinearMap.toMatrix' p.1 i i)

lemma goodMixedPairIncidenceLift_x (p : IncidenceGraphPoints A) (i : Fin 3) :
    goodMixedPairIncidenceLift K p (MvPolynomial.X i) = LinearMap.toMatrix' p.1 i i :=
  MvPolynomial.aeval_X _ _

/-- Affine slopes recover every actual incidence point over the fixed pair, including all forms. -/
theorem goodMixedPairIncidenceLift_recovers (h2 : IsUnit (2 : A)) (ε : Fin 3 → Bool)
    (p : IncidenceGraphPoints A)
    (hc : incidenceOriginalCoefficients (goodMixedChartPermutation ε) p = goodPairTripleSchemeCoefficients A) :
    incidenceGraphPointMap (goodMixedPairIncidenceLift K p).toRingHom
      (goodMixedPairUniversalPoint K ε) = p := by
  let φ : MvPolynomial (Fin 3) K →+* A := (goodMixedPairIncidenceLift K p).toRingHom
  have hT : Matrix.map (Matrix.diagonal (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) K)) φ =
      LinearMap.toMatrix' p.1 := by
    rw [goodMixedPairIncidence_diagonal A h2 ε p hc]
    funext i j
    by_cases h : i = j
    · subst j
      simp only [Matrix.map_apply, Matrix.diagonal_apply_eq]
      exact goodMixedPairIncidenceLift_x K p i
    · simp [Matrix.diagonal, h]
  have hfg (a : Fin 3 → MvPolynomial (Fin 3) K) :
      p.1 (φ ∘ a) = φ ∘ (goodMixedPairUniversalPoint K ε).1 a := by
    have h := matrix_toLin_map_apply φ (Matrix.diagonal MvPolynomial.X) a
    rw [hT, Matrix.toLin'_toMatrix'] at h
    exact h
  have hB (k : Fin 3) (x y : (Fin 3 → MvPolynomial (Fin 3) K) × (Fin 3 → MvPolynomial (Fin 3) K)) :
      (p.2 k).1 ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
        φ (((goodMixedPairUniversalPoint K ε).2 k).1 ![x, y]) := by
    rw [goodMixedPairIncidence_forms A ε p hc k]
    exact goodMixedPairChart_map φ ε k x y
  apply (incidenceGraphPointCoordinates A).injective
  rw [incidenceGraphPointMap_coordinates]
  exact (incidenceGraphPointCoordinates_of_compatible φ (goodMixedPairUniversalPoint K ε) p hfg hB).symm

end
end PfaffianDescent
