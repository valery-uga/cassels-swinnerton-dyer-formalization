import AllCharacteristics.ProjectiveCoefficientMap
import AllCharacteristics.FiniteSubschemeFromImmersion

/-!
# Global coefficient base change for projective polynomial quotients

The coefficient-changed projective scheme is the actual base change of the
original projective scheme. The proof glues the affine chart pullback squares
using the global coefficient morphism and its exact inverse images of charts.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S : Type u} {σ : Type} [CommRing R] [CommRing S]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (f : R →+* S)
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
variable (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ S))
variable (h : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)

/-- The image of a coordinate chart is its standard projective basic open. -/
theorem chartι_opensRange (j : σ) :
    (chartι I j).opensRange = Proj.basicOpen (grading I) (coordinate I j) :=
  Proj.opensRange_awayι (grading I) (coordinate I j) (coordinate_mem I j) (by decide : 0 < 1)

/-- The inverse image of a coordinate chart is the same coordinate chart
after coefficient change. -/
theorem projectiveCoefficientMap_preimage_chart (j : σ) :
    projectiveCoefficientMap f I J h ⁻¹ᵁ (chartι I j).opensRange =
      (chartι J j).opensRange := by
  rw [chartι_opensRange, chartι_opensRange]
  change Proj.map (gradedCoefficientMap f I J h)
    (irrelevant_le_map_gradedCoefficientMap f I J h) ⁻¹ᵁ
      Proj.basicOpen (grading I) (coordinate I j) = Proj.basicOpen (grading J) (coordinate J j)
  rw [Proj.map_preimage_basicOpen, gradedCoefficientMap_coordinate]

/-- The coefficient-changed chart is the inverse-image chart of the global
projective coefficient morphism, as an actual Cartesian square. -/
theorem isPullback_projectiveCoefficientMap_chart (j : σ) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartCoefficientMap f I J h j)))
      (chartι J j) (chartι I j) (projectiveCoefficientMap f I J h) :=
  IsOpenImmersion.isPullback _ _ _ _ (chartι_projectiveCoefficientMap f I J h j)
    (projectiveCoefficientMap_preimage_chart f I J h j)

/-- Formation of the whole projective polynomial quotient commutes with
coefficient change over arbitrary commutative rings. -/
theorem isPullback_projectiveCoefficientMap :
    IsPullback (projectiveCoefficientMap f I J h) (toBase J) (toBase I)
      (Spec.map (CommRingCat.ofHom f)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (coordinateOpenCover I).openCover
  intro j
  change σ at j
  change IsPullback (pullback.snd (projectiveCoefficientMap f I J h) (chartι I j))
    (pullback.fst (projectiveCoefficientMap f I J h) (chartι I j) ≫ toBase J)
    (chartι I j ≫ toBase I) (Spec.map (CommRingCat.ofHom f))
  have hc := (isPullback_projectiveCoefficientMap_chart f I J h j).flip
  have hb := isPullback_chartCoefficientMap f I J h j
  rw [← chartι_toBase I j, ← chartι_toBase J j] at hb
  apply hb.of_iso hc.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using hc.isoPullback_hom_snd.symm
  · simpa only [Iso.refl_hom, Category.comp_id, Category.assoc] using
      congrArg (fun a ↦ a ≫ toBase J) hc.isoPullback_hom_fst.symm
  · simp
  · simp

/-- The global projective base-change isomorphism, from the scheme of the
changed equations to the actual categorical pullback. -/
noncomputable def projectiveBaseChangeIso :
    scheme J ≅ pullback (toBase I) (Spec.map (CommRingCat.ofHom f)) :=
  (isPullback_projectiveCoefficientMap f I J h).isoPullback

/-- The base-change isomorphism retains the global coefficient morphism. -/
theorem projectiveBaseChangeIso_hom_fst :
    (projectiveBaseChangeIso f I J h).hom ≫
      pullback.fst (toBase I) (Spec.map (CommRingCat.ofHom f)) =
        projectiveCoefficientMap f I J h :=
  (isPullback_projectiveCoefficientMap f I J h).isoPullback_hom_fst

/-- The base-change isomorphism is over the new coefficient spectrum. -/
theorem projectiveBaseChangeIso_hom_snd :
    (projectiveBaseChangeIso f I J h).hom ≫
      pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom f)) = toBase J :=
  (isPullback_projectiveCoefficientMap f I J h).isoPullback_hom_snd

/-- The hypersurface of a coefficient-changed homogeneous polynomial is the
whole scheme-theoretic base change of the original hypersurface. -/
noncomputable def hypersurfaceBaseChangeIso (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) :
    hypersurface (p.map f) (hp.map f) ≅
      pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom f)) :=
  projectiveBaseChangeIso f (equationIdeal p hp) (equationIdeal (p.map f) (hp.map f))
    (equationIdeal_map f p hp)

/-- The hypersurface base-change isomorphism preserves its coefficient map. -/
theorem hypersurfaceBaseChangeIso_hom_snd (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) :
    (hypersurfaceBaseChangeIso f p hp).hom ≫
      pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom f)) =
        hypersurfaceToBase (p.map f) (hp.map f) :=
  projectiveBaseChangeIso_hom_snd f (equationIdeal p hp)
    (equationIdeal (p.map f) (hp.map f)) (equationIdeal_map f p hp)

/-- Transport a finite flat subscheme of an actual hypersurface base change
to the hypersurface defined by the coefficient-changed equation.  This is
the scheme-level bridge needed to apply the cubic residual construction over
a configuration function field. -/
noncomputable def hypersurfaceFiniteSubschemeOfCoefficientBaseChange
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) {n : ℕ}
    (D : FiniteSubschemeDatum
      (pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom f))) n) :
    FiniteSubschemeDatum (hypersurfaceToBase (p.map f) (hp.map f)) n :=
  FiniteSubschemeDatum.transportAlongAmbientIso
    (hypersurfaceToBase (p.map f) (hp.map f))
    (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom f)))
    (hypersurfaceBaseChangeIso f p hp)
    (hypersurfaceBaseChangeIso_hom_snd f p hp) D

/-- The coefficient-change transport preserves the étaleness of a finite
subscheme over the coefficient field. -/
theorem hypersurfaceFiniteSubschemeOfCoefficientBaseChange_toBase_etale
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) {n : ℕ}
    (D : FiniteSubschemeDatum
      (pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom f))) n)
    [Etale (D.val.subschemeι ≫
      pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom f)))] :
    Etale ((hypersurfaceFiniteSubschemeOfCoefficientBaseChange f p hp D).val.subschemeι ≫
      hypersurfaceToBase (p.map f) (hp.map f)) := by
  exact FiniteSubschemeDatum.transportAlongAmbientIso_toBase_etale
    (hypersurfaceToBase (p.map f) (hp.map f))
    (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom f)))
    (hypersurfaceBaseChangeIso f p hp)
    (hypersurfaceBaseChangeIso_hom_snd f p hp) D

end HomogeneousProjective
end AllCharacteristics
