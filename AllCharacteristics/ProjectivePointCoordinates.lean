import AllCharacteristics.CoordinateCharts
import AllCharacteristics.GradedChartCoordinates

/-!
# Homogeneous coordinates of field-valued projective scheme points

The comparison uses the actual affine coordinate cover of `Proj` and the actual
homogeneous localization rings, including compatibility with the coefficient
map. It therefore connects scheme points to homogeneous polynomial equations.
-/

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))

/-- The normalized coordinates on the chart where coordinate `j` is nonzero. -/
noncomputable def chartCoordinate (j i : σ) : ChartRing I j :=
  GradedChart.normalized (grading I) (coordinate_mem I j) (coordinate I i) (coordinate_mem I i)

/-- The distinguished coordinate on its own chart is one. -/
theorem chartCoordinate_self (j : σ) : chartCoordinate I j j = 1 :=
  GradedChart.normalized_self (grading I) (coordinate_mem I j)

/-- The coordinate functions on every chart satisfy each homogeneous equation
in the defining ideal. -/
theorem eval₂_chartCoordinate_eq_zero (j : σ) (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) (hI : p ∈ I.toIdeal) :
    p.eval₂ (chartBaseMap I j) (chartCoordinate I j) = 0 := by
  apply GradedChart.eval₂_normalized_eq_zero (grading I) (coordinate_mem I j)
    (coordinate I) (coordinate_mem I) p hp
  have he := congrFun (MvPolynomial.mk_eq_eval₂ I.toIdeal) p
  exact he.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hI)

/-- All equations in the homogeneous defining ideal vanish on the normalized
chart coordinates, by decomposition into homogeneous components. -/
theorem eval₂_chartCoordinate_eq_zero_of_mem (j : σ) (p : MvPolynomial σ R)
    (hI : p ∈ I.toIdeal) : p.eval₂ (chartBaseMap I j) (chartCoordinate I j) = 0 := by
  classical
  let 𝒜 := MvPolynomial.homogeneousSubmodule σ R
  rw [← DirectSum.sum_support_decompose 𝒜 p, MvPolynomial.eval₂_sum]
  apply Finset.sum_eq_zero
  intro n _
  exact eval₂_chartCoordinate_eq_zero I j (DirectSum.decompose 𝒜 p n)
    (DirectSum.decompose 𝒜 p n).2 (I.isHomogeneous n hI)

 /-- A field-valued projective point in a specified affine chart is represented
by a chart-ring homomorphism, and reconstructing that homomorphism gives the
original projective point. -/
theorem exists_chart_hom_eq_of_point_of_mem_range {k : Type u} [Field k] (f : R →+* k)
    (q : Spec (.of k) ⟶ scheme I)
    (hq : q ≫ toBase I = Spec.map (CommRingCat.ofHom f)) (j : σ)
    (hj : q (IsLocalRing.closedPoint k) ∈ Set.range (chartι I j)) :
    ∃ g : ChartRing I j →+* k,
      g.comp (chartBaseMap I j) = f ∧
        Spec.map (CommRingCat.ofHom g) ≫ chartι I j = q := by
  obtain ⟨y, hy⟩ := hj
  have hrange : Set.range q ⊆ Set.range (chartι I j) := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    exact ⟨y, hy.trans (congrArg q hp).symm⟩
  let qU := IsOpenImmersion.lift (chartι I j) q hrange
  let g := Spec.preimage qU
  have hU : qU ≫ Spec.map (CommRingCat.ofHom (chartBaseMap I j)) =
      Spec.map (CommRingCat.ofHom f) := by
    rw [← chartι_toBase, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact hq
  refine ⟨g.hom, ?_⟩
  have hg : Spec.map g = qU := Spec.map_preimage qU
  have he : CommRingCat.ofHom (chartBaseMap I j) ≫ g = CommRingCat.ofHom f := by
    apply Spec.map_injective
    rw [Spec.map_comp, hg]
    exact hU
  refine ⟨congrArg CommRingCat.Hom.hom he, ?_⟩
  change Spec.map g ≫ chartι I j = q
  rw [hg]
  exact IsOpenImmersion.lift_fac _ _ _

/-- Two affine-chart homomorphisms which reconstruct the same projective
point are equal.  This gives the coordinate-level uniqueness needed when a
field-valued point is compared through two projective constructions. -/
theorem chart_hom_eq_of_projective_eq {A : Type u} [CommRing A]
    (g h : ChartRing I j →+* A)
    (hgh : Spec.map (CommRingCat.ofHom g) ≫ chartι I j =
      Spec.map (CommRingCat.ofHom h) ≫ chartι I j) :
    g = h := by
  have hs : Spec.map (CommRingCat.ofHom g) = Spec.map (CommRingCat.ofHom h) :=
    (cancel_mono (chartι I j)).mp hgh
  have hc : CommRingCat.ofHom g = CommRingCat.ofHom h := Spec.map_injective hs
  exact congrArg CommRingCat.Hom.hom hc

/-- A field-valued projective point factors through one of the actual affine
coordinate charts and gives a chart-ring homomorphism over the coefficient map. -/
theorem exists_chart_hom_eq_of_point {k : Type u} [Field k] (f : R →+* k)
    (q : Spec (.of k) ⟶ scheme I)
    (hq : q ≫ toBase I = Spec.map (CommRingCat.ofHom f)) :
    ∃ j : σ, ∃ g : ChartRing I j →+* k,
      g.comp (chartBaseMap I j) = f ∧
        Spec.map (CommRingCat.ofHom g) ≫ chartι I j = q := by
  obtain ⟨j, y, hy⟩ := exists_coordinate_chart I (q (IsLocalRing.closedPoint k))
  obtain ⟨g, hg, hqg⟩ :=
    exists_chart_hom_eq_of_point_of_mem_range I f q hq j ⟨y, hy⟩
  exact ⟨j, g, hg, hqg⟩

/-- A field-valued projective point factors through one of the actual affine
coordinate charts and gives a chart-ring homomorphism over the coefficient map. -/
theorem exists_chart_hom_of_point {k : Type u} [Field k] (f : R →+* k)
    (q : Spec (.of k) ⟶ scheme I)
    (hq : q ≫ toBase I = Spec.map (CommRingCat.ofHom f)) :
    ∃ j : σ, ∃ g : ChartRing I j →+* k, g.comp (chartBaseMap I j) = f := by
  obtain ⟨j, g, hg, _⟩ := exists_chart_hom_eq_of_point I f q hq
  exact ⟨j, g, hg⟩

/-- An actual field-valued point has nonzero homogeneous coordinates satisfying
all homogeneous equations in the defining ideal. -/
theorem homogeneous_coordinates_of_point {k : Type u} [Field k] (f : R →+* k)
    (q : Spec (.of k) ⟶ scheme I)
    (hq : q ≫ toBase I = Spec.map (CommRingCat.ofHom f)) :
    ∃ x : σ → k, x ≠ 0 ∧ ∀ p : MvPolynomial σ R,
      p ∈ I.toIdeal → p.eval₂ f x = 0 := by
  obtain ⟨j, g, hg⟩ := exists_chart_hom_of_point I f q hq
  refine ⟨fun i ↦ g (chartCoordinate I j i), ?_, ?_⟩
  · intro hx
    have hj := congrFun hx j
    exact one_ne_zero (by simpa only [chartCoordinate_self, map_one, Pi.zero_apply] using hj)
  · intro p hI
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j p hI)
    rw [MvPolynomial.hom_eval₂, hg, map_zero] at h
    exact h

/-- A point of the actual projective hypersurface supplies a nonzero solution
of its defining equation over the same field. -/
theorem hypersurface_coordinates_of_point {k : Type u} [Field k]
    (f : R →+* k) (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (q : Spec (.of k) ⟶ hypersurface p hp)
    (hq : q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom f)) :
    ∃ x : σ → k, x ≠ 0 ∧ p.eval₂ f x = 0 := by
  obtain ⟨x, hx, he⟩ := homogeneous_coordinates_of_point (equationIdeal p hp) f q hq
  exact ⟨x, hx, he p (Ideal.subset_span (Set.mem_singleton p))⟩

end HomogeneousProjective
end AllCharacteristics
