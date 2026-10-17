import AllCharacteristics.AffineChartPresentation
import AllCharacteristics.PolynomialQuotientBaseChange

/-!
# Coefficient base change of projective coordinate charts

The explicit presentation of each homogeneous chart identifies its coefficient
base change with the corresponding chart of the coefficient-changed equations.
The result is an actual pullback square of affine schemes.
-/

open MvPolynomial CategoryTheory AlgebraicGeometry
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S : Type u} {σ : Type} [CommRing R] [CommRing S]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (f : R →+* S)
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
variable (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ S))
variable (h : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)

include h in
/-- The chart equations map to the chart equations after coefficient change. -/
theorem chartPresentationIdeal_map (j : σ) :
    (chartPresentationIdeal I j).map (MvPolynomial.map f) = chartPresentationIdeal J j := by
  simp only [chartPresentationIdeal, Ideal.map_sup, h, Ideal.map_span, Set.image_singleton,
    map_sub, map_X, map_one]

/-- The coefficient-changed presentation is the actual chart of the changed
homogeneous ideal. -/
noncomputable def chartBaseChangePresentationEquiv (j : σ) :
    (MvPolynomial σ S ⧸ (chartPresentationIdeal I j).map (MvPolynomial.map f)) ≃+*
      ChartRing J j :=
  (Ideal.quotEquivOfEq (chartPresentationIdeal_map f I J h j)).trans
    (chartPresentationEquiv J j)

/-- The coefficient-changed chart presentation preserves polynomial evaluation. -/
theorem chartBaseChangePresentationEquiv_mk (j : σ) (p : MvPolynomial σ S) :
    chartBaseChangePresentationEquiv f I J h j
      (Ideal.Quotient.mk ((chartPresentationIdeal I j).map (MvPolynomial.map f)) p) =
        p.eval₂ (chartBaseMap J j) (chartCoordinate J j) := by
  exact (congrArg (chartPresentationEquiv J j)
    (Ideal.quotEquivOfEq_mk (chartPresentationIdeal_map f I J h j) p)).trans
      (chartPresentationEquiv_mk J j p)

/-- The homomorphism between actual coordinate-chart rings induced by a
coefficient map. -/
noncomputable def chartCoefficientMap (j : σ) : ChartRing I j →+* ChartRing J j :=
  (chartBaseChangePresentationEquiv f I J h j).toRingHom.comp
    ((PolynomialQuotient.coefficientMap f (chartPresentationIdeal I j)).comp
      (chartPresentationEquiv I j).symm.toRingHom)

/-- The chart coefficient map acts by coefficient change in normalized
polynomial evaluation. -/
theorem chartCoefficientMap_eval (j : σ) (p : MvPolynomial σ R) :
    chartCoefficientMap f I J h j (p.eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
      (p.map f).eval₂ (chartBaseMap J j) (chartCoordinate J j) := by
  rw [← chartPresentationEquiv_mk I j p]
  change chartBaseChangePresentationEquiv f I J h j
    (PolynomialQuotient.coefficientMap f (chartPresentationIdeal I j)
      ((chartPresentationEquiv I j).symm
        (chartPresentationEquiv I j (Ideal.Quotient.mk _ p)))) = _
  rw [RingEquiv.symm_apply_apply, PolynomialQuotient.coefficientMap_mk,
    chartBaseChangePresentationEquiv_mk]

/-- The chart coefficient map sends a base coefficient to its scalar
extension. -/
theorem chartCoefficientMap_baseMap (j : σ) (r : R) :
    chartCoefficientMap f I J h j (chartBaseMap I j r) =
      chartBaseMap J j (f r) := by
  simpa only [eval₂_C, map_C] using
    chartCoefficientMap_eval f I J h j (C r)

/-- The normalized projective chart coordinates are unchanged by coefficient
extension. -/
theorem chartCoefficientMap_coordinate (j : σ) (i : σ) :
    chartCoefficientMap f I J h j (chartCoordinate I j i) =
      chartCoordinate J j i := by
  simpa only [eval₂_X, map_X] using
    chartCoefficientMap_eval f I J h j (X i)

/-- Actual chart coefficient maps form a categorical pushout of rings. -/
theorem isPushout_chartCoefficientMap (j : σ) :
    IsPushout (CommRingCat.ofHom (chartBaseMap I j)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (chartCoefficientMap f I J h j))
      (CommRingCat.ofHom (chartBaseMap J j)) := by
  apply (PolynomialQuotient.isPushout f (chartPresentationIdeal I j)).of_iso
    (Iso.refl _) (chartPresentationEquiv I j).toCommRingCatIso
    (Iso.refl _) (chartBaseChangePresentationEquiv f I J h j).toCommRingCatIso
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (chartPresentationEquiv_mk I j (C r)).trans (eval₂_C _ _ _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change chartBaseChangePresentationEquiv f I J h j
      (PolynomialQuotient.coefficientMap f (chartPresentationIdeal I j) x) =
      chartBaseChangePresentationEquiv f I J h j
        (PolynomialQuotient.coefficientMap f (chartPresentationIdeal I j)
          ((chartPresentationEquiv I j).symm ((chartPresentationEquiv I j) x)))
    rw [RingEquiv.symm_apply_apply]
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    exact (chartBaseChangePresentationEquiv_mk f I J h j (C s)).trans (eval₂_C _ _ _)

/-- The actual coordinate chart of the changed homogeneous equations is the
scheme-theoretic base change of the original coordinate chart. -/
theorem isPullback_chartCoefficientMap (j : σ) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartCoefficientMap f I J h j)))
      (Spec.map (CommRingCat.ofHom (chartBaseMap J j)))
      (Spec.map (CommRingCat.ofHom (chartBaseMap I j)))
      (Spec.map (CommRingCat.ofHom f)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_chartCoefficientMap f I J h j)

/-- A homogeneous hypersurface's defining ideal maps to the ideal of its
coefficient-changed equation. -/
theorem equationIdeal_map (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    (equationIdeal p hp).toIdeal.map (MvPolynomial.map f) =
      (equationIdeal (p.map f) (hp.map f)).toIdeal := by
  change (Ideal.span {p}).map (MvPolynomial.map f) = Ideal.span {p.map f}
  rw [Ideal.map_span, Set.image_singleton]

/-- Coefficient base change commutes with every actual coordinate chart of a
homogeneous hypersurface. -/
theorem isPullback_hypersurface_chart (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) (j : σ) :
    IsPullback (Spec.map (CommRingCat.ofHom
      (chartCoefficientMap f (equationIdeal p hp)
        (equationIdeal (p.map f) (hp.map f)) (equationIdeal_map f p hp) j)))
      (Spec.map (CommRingCat.ofHom
        (chartBaseMap (equationIdeal (p.map f) (hp.map f)) j)))
      (Spec.map (CommRingCat.ofHom (chartBaseMap (equationIdeal p hp) j)))
      (Spec.map (CommRingCat.ofHom f)) :=
  isPullback_chartCoefficientMap f (equationIdeal p hp)
    (equationIdeal (p.map f) (hp.map f)) (equationIdeal_map f p hp) j

end HomogeneousProjective
end AllCharacteristics
