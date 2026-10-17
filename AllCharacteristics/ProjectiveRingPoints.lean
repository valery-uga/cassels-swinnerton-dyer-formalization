import AllCharacteristics.ProjectivePoints

/-!
# Affine-ring-valued points from unit coordinates

Homogeneous coordinates with a specified unit coordinate define a point of the
actual projective scheme over any commutative target ring. This allows finite
nonreduced algebras to supply projective points and hence fundamental cycles.
-/

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R A : Type u} {σ : Type} [CommRing R] [CommRing A]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A solution of a homogeneous ideal over a ring gives an actual scheme
point when one of its homogeneous coordinates is a unit. -/
theorem point_of_unit_coordinates
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) (f : R →+* A)
    (x : σ → A) (j : σ) (hx : IsUnit (x j))
    (he : ∀ p : MvPolynomial σ R, p ∈ I.toIdeal → p.eval₂ f x = 0) :
    ∃ q : Spec (.of A) ⟶ scheme I, q ≫ toBase I = Spec.map (CommRingCat.ofHom f) := by
  let e : CoordinateRing I →+* A := Ideal.Quotient.lift I.toIdeal
    (MvPolynomial.eval₂Hom f x) he
  have hej : e (coordinate I j) = x j := MvPolynomial.eval₂Hom_X' f x j
  have hunit : IsUnit (e (coordinate I j)) := hej.symm ▸ hx
  let L := Localization (.powers (coordinate I j))
  let l : L →+* A := IsLocalization.Away.lift (coordinate I j) hunit
  let g : ChartRing I j →+* A := l.comp (algebraMap (ChartRing I j) L)
  have hg : g.comp (chartBaseMap I j) = f := by
    ext r
    change l ((chartBaseMap I j r).val) = f r
    have hb : (chartBaseMap I j r).val =
        algebraMap (CoordinateRing I) L (algebraMap R (CoordinateRing I) r) :=
      GradedChart.val_baseMap (grading I) r
    rw [hb]
    change IsLocalization.Away.lift (coordinate I j) hunit
      (algebraMap (CoordinateRing I) L (algebraMap R (CoordinateRing I) r)) = f r
    rw [IsLocalization.Away.lift_eq]
    exact MvPolynomial.eval₂_C f x r
  refine ⟨Spec.map (CommRingCat.ofHom g) ≫ chartι I j, ?_⟩
  rw [Category.assoc, chartι_toBase, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (g.comp (chartBaseMap I j))) =
    Spec.map (CommRingCat.ofHom f)
  exact congrArg (fun h : R →+* A ↦ Spec.map (CommRingCat.ofHom h)) hg

/-- A solution of a homogeneous equation over a ring gives a point of its
actual projective hypersurface when one coordinate is a unit. -/
theorem hypersurface_point_of_unit_coordinates (f : R →+* A)
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (x : σ → A) (j : σ) (hx : IsUnit (x j)) (he : p.eval₂ f x = 0) :
    ∃ q : Spec (.of A) ⟶ hypersurface p hp,
      q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom f) := by
  have hI : (equationIdeal p hp).toIdeal ≤ RingHom.ker (MvPolynomial.eval₂Hom f x) := by
    apply Ideal.span_le.mpr
    intro a ha
    have ha' : a = p := Set.mem_singleton_iff.mp ha
    subst a
    exact he
  exact point_of_unit_coordinates (equationIdeal p hp) f x j hx (fun a ha ↦ hI ha)

end HomogeneousProjective
end AllCharacteristics
