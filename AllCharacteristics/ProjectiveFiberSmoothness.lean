import AllCharacteristics.ProjectiveChartBaseChange
import AllCharacteristics.SmoothSpecialFiber

/-!
# Smoothness of the actual fiber from the coefficient-changed equations

The chart base-change theorem identifies the affine charts of the actual
pullback with those of the coefficient-changed projective scheme. Smoothness
can therefore be checked on these charts without requiring a global Proj
base-change isomorphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S : Type u} {σ : Type} [CommRing R] [CommRing S]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Smoothness of a projective scheme defined by the changed homogeneous
ideal implies smoothness of the actual base-changed structure morphism. -/
theorem smooth_pullback_of_smooth_changed_ideal
    (f : R →+* S)
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ S))
    (h : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)
    [Smooth (toBase J)] :
    Smooth (pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom f))) := by
  have : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth.{u})
    ((coordinateOpenCover I).openCover.pullback₂
      (pullback.fst (toBase I) (Spec.map (CommRingCat.ofHom f))))).mpr
  intro j
  change σ at j
  have hc : Smooth (Spec.map (CommRingCat.ofHom (chartBaseMap J j))) := by
    rw [← chartι_toBase]
    infer_instance
  have hp := isPullback_chartCoefficientMap f I J h j
  have hs : Smooth (pullback.snd
      (Spec.map (CommRingCat.ofHom (chartBaseMap I j)))
      (Spec.map (CommRingCat.ofHom f))) := by
    rw [← hp.isoPullback_inv_snd]
    infer_instance
  have ht : Smooth (pullback.snd (chartι I j ≫ toBase I)
      (Spec.map (CommRingCat.ofHom f))) := by
    rw [chartι_toBase]
    exact hs
  change Smooth (pullback.snd (chartι I j)
    (pullback.fst (toBase I) (Spec.map (CommRingCat.ofHom f))) ≫
      pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom f)))
  rw [← pullbackRightPullbackFstIso_hom_snd]
  infer_instance

/-- Smoothness of the equation obtained by changing coefficients implies
smoothness of the actual hypersurface fiber. This holds over arbitrary rings. -/
theorem smooth_hypersurface_pullback_of_smooth_map
    (f : R →+* S) (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    [Smooth (hypersurfaceToBase (p.map f) (hp.map f))] :
    Smooth (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom f))) := by
  have : Smooth (toBase (equationIdeal (p.map f) (hp.map f))) :=
    inferInstanceAs (Smooth (hypersurfaceToBase (p.map f) (hp.map f)))
  exact smooth_pullback_of_smooth_changed_ideal f (equationIdeal p hp)
    (equationIdeal (p.map f) (hp.map f)) (equationIdeal_map f p hp)

/-- Smoothness is preserved when the homogeneous equations are mapped along
any coefficient homomorphism. -/
theorem smooth_toBase_of_smooth_original_ideal
    (f : R →+* S)
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ S))
    (h : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)
    [Smooth (toBase I)] : Smooth (toBase J) := by
  have : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth.{u})
    (coordinateOpenCover J).openCover).mpr
  intro j
  change σ at j
  change Smooth (chartι J j ≫ toBase J)
  rw [chartι_toBase]
  have hc : Smooth (Spec.map (CommRingCat.ofHom (chartBaseMap I j))) := by
    rw [← chartι_toBase]
    infer_instance
  exact MorphismProperty.of_isPullback (P := @Smooth.{u})
    (isPullback_chartCoefficientMap f I J h j) hc

/-- Mapping a smooth homogeneous hypersurface's coefficients preserves
smoothness in every characteristic. -/
theorem smooth_hypersurfaceToBase_map
    (f : R →+* S) (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    [Smooth (hypersurfaceToBase p hp)] :
    Smooth (hypersurfaceToBase (p.map f) (hp.map f)) := by
  have : Smooth (toBase (equationIdeal p hp)) :=
    inferInstanceAs (Smooth (hypersurfaceToBase p hp))
  exact smooth_toBase_of_smooth_original_ideal f (equationIdeal p hp)
    (equationIdeal (p.map f) (hp.map f)) (equationIdeal_map f p hp)

/-- Equal homogeneous equations define the same smoothness statement,
independently of the proofs of homogeneity. -/
theorem smooth_hypersurfaceToBase_congr
    (p q : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d)
    (h : p = q) : Smooth (hypersurfaceToBase p hp) ↔ Smooth (hypersurfaceToBase q hq) := by
  subst q
  rfl

end HomogeneousProjective
end AllCharacteristics
