import AllCharacteristics.ProjectivePointCoordinates

/-!
# Field-valued points of projective polynomial quotients

A nonzero solution of the homogeneous defining ideal gives a genuine scheme
point, using localization on a coordinate chart. Together with coordinate
extraction this gives the equivalence needed to connect algebraic descent with
proper specialization.
-/

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))

/-- A nonzero solution of a homogeneous ideal gives a point of its actual
projective scheme over the specified coefficient map. -/
theorem point_of_coordinates {k : Type u} [Field k] (f : R →+* k)
    (x : σ → k) (hx : x ≠ 0)
    (he : ∀ p : MvPolynomial σ R, p ∈ I.toIdeal → p.eval₂ f x = 0) :
    ∃ q : Spec (.of k) ⟶ scheme I, q ≫ toBase I = Spec.map (CommRingCat.ofHom f) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  let e : CoordinateRing I →+* k := Ideal.Quotient.lift I.toIdeal
    (MvPolynomial.eval₂Hom f x) he
  have hej : e (coordinate I j) = x j := MvPolynomial.eval₂Hom_X' f x j
  have hunit : IsUnit (e (coordinate I j)) := by
    rw [hej]
    exact isUnit_iff_ne_zero.mpr hj
  let L := Localization (.powers (coordinate I j))
  let l : L →+* k := IsLocalization.Away.lift (coordinate I j) hunit
  let g : ChartRing I j →+* k := l.comp (algebraMap (ChartRing I j) L)
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
  exact congrArg (fun h : R →+* k ↦ Spec.map (CommRingCat.ofHom h)) hg

/-- Field-valued points of a homogeneous projective quotient are equivalent,
for existence, to nonzero solutions of its defining ideal. -/
theorem has_point_iff_coordinates {k : Type u} [Field k] (f : R →+* k) :
    (∃ q : Spec (.of k) ⟶ scheme I, q ≫ toBase I = Spec.map (CommRingCat.ofHom f)) ↔
      ∃ x : σ → k, x ≠ 0 ∧ ∀ p : MvPolynomial σ R, p ∈ I.toIdeal → p.eval₂ f x = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    exact homogeneous_coordinates_of_point I f q hq
  · rintro ⟨x, hx, he⟩
    exact point_of_coordinates I f x hx he

/-- A nonzero solution of a homogeneous equation gives a point of its actual
projective hypersurface over the same field. -/
theorem hypersurface_point_of_coordinates {k : Type u} [Field k]
    (f : R →+* k) (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (x : σ → k) (hx : x ≠ 0) (he : p.eval₂ f x = 0) :
    ∃ q : Spec (.of k) ⟶ hypersurface p hp,
      q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom f) := by
  have hI : (equationIdeal p hp).toIdeal ≤ RingHom.ker (MvPolynomial.eval₂Hom f x) := by
    apply Ideal.span_le.mpr
    intro a ha
    have ha' : a = p := Set.mem_singleton_iff.mp ha
    subst a
    exact he
  exact point_of_coordinates (equationIdeal p hp) f x hx (fun a ha ↦ hI ha)

/-- The scheme-theoretic and coordinate definitions of existence of a point on
a projective hypersurface agree over every field. -/
theorem hypersurface_has_point_iff_coordinates {k : Type u} [Field k]
    (f : R →+* k) (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    (∃ q : Spec (.of k) ⟶ hypersurface p hp,
      q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom f)) ↔
      ∃ x : σ → k, x ≠ 0 ∧ p.eval₂ f x = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    exact hypersurface_coordinates_of_point f p hp q hq
  · rintro ⟨x, hx, he⟩
    exact hypersurface_point_of_coordinates f p hp x hx he

end HomogeneousProjective
end AllCharacteristics
