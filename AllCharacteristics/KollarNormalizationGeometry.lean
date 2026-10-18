import AllCharacteristics.KollarNormalizationAlgebra
import AllCharacteristics.Unirationality
import PfaffianDescent.SmoothCubicFieldPointChartGradient
import PfaffianDescent.CubicClosedPointSerreSurfaceCoordinatesChange



noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace AllCharacteristics
open PfaffianDescent HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- A rational section of the actual smooth cubic has a smooth nonzero
homogeneous coordinate vector over the same field. -/
theorem exists_smooth_cubic_coordinates_of_section
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (s : Spec (.of K) ⟶ hypersurface F hF)
    (hs : s ≫ hypersurfaceToBase F hF = 𝟙 _) :
    ∃ p : Fin 4 → K, IsSmoothCubicCoordinatePoint F p := by
  obtain ⟨j, g, hg⟩ := exists_chart_hom_of_point (equationIdeal F hF)
    (RingHom.id K) s (by simpa [hypersurfaceToBase] using hs)
  let p : Fin 4 → K := fun i => g (chartCoordinate (equationIdeal F hF) j i)
  have hp0 : p ≠ 0 := by
    intro h
    have hj := congrFun h j
    have h10 : (1 : K) = 0 := by
      simpa only [p, chartCoordinate_self, map_one, Pi.zero_apply] using hj
    exact (one_ne_zero : (1 : K) ≠ 0) h10
  have he : F.eval p = 0 := by
    have h := congrArg g (eval₂_chartCoordinate_eq_zero (equationIdeal F hF) j F hF
      (Ideal.subset_span (Set.mem_singleton F)))
    rw [MvPolynomial.hom_eval₂, hg, map_zero] at h
    exact h
  obtain ⟨a, ha⟩ := smoothCubic_fieldPoint_chart_exists_nonzero_retained_partial
    F hF hF0 j g (by simpa using hg)
  refine ⟨p, hp0, he, a.1, ?_⟩
  simpa only [p, Algebra.algebraMap_self, MvPolynomial.eval₂_id] using ha

namespace HomogeneousProjective

/-- Unirationality transports along an actual isomorphism over the field. -/
theorem isUnirationalOver_of_iso
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (x : X ⟶ Spec (.of K)) (y : Y ⟶ Spec (.of K))
    (e : X ≅ Y) (he : e.hom ≫ y = x)
    (hX : IsUnirationalOver K X x) : IsUnirationalOver K Y y := by
  obtain ⟨n, f, hf, hb⟩ := hX
  letI : f.IsDominant := hf
  let g := f.representative.compHom e.hom
  refine ⟨n, g.toRationalMap, ?_, ?_⟩
  · rw [g.isDominant_toRationalMap_iff]
    change IsDominant (f.representative.hom ≫ e.hom)
    infer_instance
  · have hg : g.compHom y = f.representative.compHom x := by
      refine Scheme.PartialMap.ext (g.compHom y)
        (f.representative.compHom x) (by rfl) ?_
      simp [g, Scheme.PartialMap.compHom, Category.assoc, he]
    rw [← Scheme.RationalMap.compHom_toRationalMap, hg,
      Scheme.RationalMap.compHom_toRationalMap,
      f.toRationalMap_representative]
    exact hb

theorem isUnirationalOver_iff_of_iso
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (x : X ⟶ Spec (.of K)) (y : Y ⟶ Spec (.of K))
    (e : X ≅ Y) (he : e.hom ≫ y = x) :
    IsUnirationalOver K X x ↔ IsUnirationalOver K Y y := by
  constructor
  · exact isUnirationalOver_of_iso x y e he
  · apply isUnirationalOver_of_iso y x e.symm
    change e.inv ≫ x = y
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- The cubic coordinate normalization changes unirationality by an actual
field-compatible scheme isomorphism. -/
theorem isUnirationalOver_linearSubstitution_iff
    {K : Type u} [Field K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    IsUnirationalOver K
        (hypersurface (linearSubstitution M F) (linearSubstitution_homogeneous M hF))
        (hypersurfaceToBase (linearSubstitution M F) (linearSubstitution_homogeneous M hF)) ↔
      IsUnirationalOver K (hypersurface F hF) (hypersurfaceToBase F hF) := by
  exact (isUnirationalOver_iff_of_iso _ _
    (cubicClosedPointSerreSurfaceCoordinates_schemeIso M hM F hF)
    (cubicClosedPointSerreSurfaceCoordinates_schemeIso_toBase M hM F hF)).symm

end HomogeneousProjective

/-- The complete normalization data required by the generic Kollár-line
construction. Every field and all characteristics are allowed. -/
structure KollarNormalizedCubic
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) where
  matrix : Matrix (Fin 4) (Fin 4) K
  isUnit_det : IsUnit matrix.det
  cubic : Cubic K 4
  equation : cubic.toMvPolynomial = linearSubstitution matrix F
  point_eval : cubic.eval (kollarBasePoint K) = 0
  secant_ne_zero : cubic.mixed (kollarBasePoint K)
    (kollarAffineLineDirection K (fun _ => 0)) ≠ 0

/-- Smoothness of the actual normalized cubic is inherited from the given
smooth projective hypersurface. -/
instance KollarNormalizedCubic.smooth
    {K : Type u} [Field K]
    {F : MvPolynomial (Fin 4) K} {hF : F.IsHomogeneous 3}
    [Smooth (hypersurfaceToBase F hF)] (N : KollarNormalizedCubic F hF) :
    Smooth (hypersurfaceToBase (linearSubstitution N.matrix F)
      (linearSubstitution_homogeneous N.matrix hF)) :=
  cubicClosedPointSerreSurfaceCoordinates_smooth N.matrix N.isUnit_det F hF

/-- A rational section constructs normalization data internally; no good
frame or normalized equation is supplied as a hypothesis. -/
theorem nonempty_kollarNormalizedCubic_of_section
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (s : Spec (.of K) ⟶ hypersurface F hF)
    (hs : s ≫ hypersurfaceToBase F hF = 𝟙 _) :
    Nonempty (KollarNormalizedCubic F hF) := by
  obtain ⟨p, hp⟩ := exists_smooth_cubic_coordinates_of_section F hF hF0 s hs
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor_any_characteristic F hF
  have hp' : IsSmoothCubicCoordinatePoint c.toMvPolynomial p := by
    rw [hc]
    exact hp
  obtain ⟨M, hM, -, he, hd⟩ := exists_kollar_coordinate_normalization c p hp'
  refine ⟨⟨M, hM, c.compLinear M, ?_, he, hd⟩⟩
  rw [Cubic.toMvPolynomial_compLinear_any_characteristic, hc]

/-- A theorem for normalized smooth cubics applies to an arbitrary nonzero
smooth cubic and its actual rational section. The normalization and its
smoothness are constructed internally, and the conclusion is transported
back along the actual projective scheme isomorphism. -/
theorem isUnirationalOver_of_normalized_cubic_theorem
    {K : Type u} [Field K]
    (normalized : ∀ (G : MvPolynomial (Fin 4) K) (hG : G.IsHomogeneous 3)
      [Smooth (hypersurfaceToBase G hG)]
      (c : Cubic K 4) (hc : c.toMvPolynomial = G)
      (hp : c.eval (kollarBasePoint K) = 0)
      (hd : c.mixed (kollarBasePoint K)
        (kollarAffineLineDirection K (fun _ => 0)) ≠ 0),
      IsUnirationalOver K (hypersurface G hG) (hypersurfaceToBase G hG))
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (s : Spec (.of K) ⟶ hypersurface F hF)
    (hs : s ≫ hypersurfaceToBase F hF = 𝟙 _) :
    IsUnirationalOver K (hypersurface F hF) (hypersurfaceToBase F hF) := by
  let N := Classical.choice (nonempty_kollarNormalizedCubic_of_section F hF hF0 s hs)
  have hn := normalized (linearSubstitution N.matrix F)
    (linearSubstitution_homogeneous N.matrix hF)
    N.cubic N.equation N.point_eval N.secant_ne_zero
  exact (isUnirationalOver_linearSubstitution_iff N.matrix N.isUnit_det F hF).mp hn

end AllCharacteristics
