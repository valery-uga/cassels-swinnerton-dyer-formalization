import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridPoints
import PfaffianDescent.VoisinProjectiveVectorSchemePoint
import PfaffianDescent.VoisinFiniteAlgebraRationalPointSplit

/-! # The native grid is geometrically split and reduced -/

noncomputable section
open AlgebraicGeometry CategoryTheory Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_grid_geometric_finite
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    IsFinite (toBase (voisinDegreeTenSelectedAvoidance_gridIdeal
      (p.map (algebraMap K L)) (hp.map (algebraMap K L)))) := by
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p
      (voisinDegreeTenSelectedAvoidance_gridCubic K 1)
      (voisinDegreeTenSelectedAvoidance_gridCubic K 2) hp
      (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1)
      (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2))) :=
    voisinDegreeTenSelectedAvoidance_grid_intersection_finite p hp hno
  have h := tripleCompleteIntersection_isFinite_coefficientExtension (K := L) p
    (voisinDegreeTenSelectedAvoidance_gridCubic K 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic K 2) hp
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2)
  have hJ : tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap K L))
      ((voisinDegreeTenSelectedAvoidance_gridCubic K 1).map (algebraMap K L))
      ((voisinDegreeTenSelectedAvoidance_gridCubic K 2).map (algebraMap K L))
      (hp.map (algebraMap K L))
      ((voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1).map (algebraMap K L))
      ((voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2).map (algebraMap K L)) =
      voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
        (hp.map (algebraMap K L)) := by
    apply HomogeneousIdeal.ext
    change Ideal.span ({p.map (algebraMap K L),
      (voisinDegreeTenSelectedAvoidance_gridCubic K 1).map (algebraMap K L),
      (voisinDegreeTenSelectedAvoidance_gridCubic K 2).map (algebraMap K L)} :
      Set (MvPolynomial (Fin 4) L)) =
      Ideal.span ({p.map (algebraMap K L),
        voisinDegreeTenSelectedAvoidance_gridCubic L 1,
        voisinDegreeTenSelectedAvoidance_gridCubic L 2} : Set (MvPolynomial (Fin 4) L))
    rw [voisinDegreeTenSelectedAvoidance_gridCubic_map,
      voisinDegreeTenSelectedAvoidance_gridCubic_map]
  rwa [hJ] at h

set_option backward.isDefEq.respectTransparency false in
/-- The geometric grid's twenty-seven distinct normalized vectors give
twenty-seven distinct native rational point morphisms. -/
theorem voisinDegreeTenSelectedAvoidance_grid_geometric_point_morphisms
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ t : Fin 27 → (Spec (.of L) ⟶ scheme
        (voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
          (hp.map (algebraMap K L)))),
      Function.Injective t ∧ ∀ i, t i ≫ toBase
        (voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
          (hp.map (algebraMap K L))) =
        Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
  obtain ⟨x, hxin, hx0, hxzero, -⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_twenty_seven_grid_points (L := L) p hp hno
  let J := voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
    (hp.map (algebraMap K L))
  let t := fun i : Fin 27 => projectiveUnitVectorSchemePointAt J (x i) (hxzero i) 0 (hx0 i)
  refine ⟨t, ?_, ?_⟩
  · intro i j hij
    exact hxin (projectiveUnitVectorSchemePointAt_injective J 0
      (hxzero i) (hxzero j) (hx0 i) (hx0 j) hij)
  · intro i
    exact projectiveUnitVectorSchemePointAt_toBase J (x i) (hxzero i) 0 (hx0 i)

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_grid_geometric_rank_twenty_seven
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    letI := voisinDegreeTenSelectedAvoidance_grid_geometric_finite (L := L) p hp hno
    finiteSchemeRank (toBase (voisinDegreeTenSelectedAvoidance_gridIdeal
      (p.map (algebraMap K L)) (hp.map (algebraMap K L)))) = 27 := by
  let J := voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
    (hp.map (algebraMap K L))
  letI : IsFinite (toBase J) :=
    voisinDegreeTenSelectedAvoidance_grid_geometric_finite (L := L) p hp hno
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap K L)) (voisinDegreeTenSelectedAvoidance_gridCubic L 1)
      (voisinDegreeTenSelectedAvoidance_gridCubic L 2) (hp.map (algebraMap K L))
      (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous L 1)
      (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous L 2))) :=
    voisinDegreeTenSelectedAvoidance_grid_geometric_finite (L := L) p hp hno
  obtain ⟨t, -, -⟩ :=
    voisinDegreeTenSelectedAvoidance_grid_geometric_point_morphisms (L := L) p hp hno
  have hnonempty : Nonempty (scheme J) :=
    ⟨t 0 (IsLocalRing.closedPoint L)⟩
  have hrel := tripleCompleteIntersection_isRelPrime_of_finite_of_nonempty_algClosed
    (p.map (algebraMap K L)) (voisinDegreeTenSelectedAvoidance_gridCubic L 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic L 2) (hp.map (algebraMap K L))
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous L 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous L 2) (by decide) hnonempty
  have hregular := third_regular_of_finite_degrees
    (p.map (algebraMap K L)) (voisinDegreeTenSelectedAvoidance_gridCubic L 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic L 2) (hp.map (algebraMap K L))
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous L 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous L 2)
    (by decide) (by decide) hnonempty
  exact triple_cubic_intersection_length_twenty_seven
    (p.map (algebraMap K L)) (voisinDegreeTenSelectedAvoidance_gridCubic L 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic L 2) (hp.map (algebraMap K L))
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous L 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous L 2)
    (by
      intro hz
      exact voisinDegreeTenSelectedAvoidance_cubic_ne_zero_of_no_section p hp hno
        (MvPolynomial.map_injective (algebraMap K L) (algebraMap K L).injective
          (by simpa using hz)))
    (voisinDegreeTenSelectedAvoidance_gridCubic_one_ne_zero L) hrel hregular

set_option backward.isDefEq.respectTransparency false in
/-- The literal base-changed complete intersection is étale; its rank is
exhausted by the explicit twenty-seven distinct geometric points. -/
theorem voisinDegreeTenSelectedAvoidance_grid_geometric_etale
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    Etale (toBase (voisinDegreeTenSelectedAvoidance_gridIdeal
      (p.map (algebraMap K L)) (hp.map (algebraMap K L)))) := by
  let J := voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
    (hp.map (algebraMap K L))
  letI : IsFinite (toBase J) :=
    voisinDegreeTenSelectedAvoidance_grid_geometric_finite (L := L) p hp hno
  obtain ⟨t, htinj, htbase⟩ :=
    voisinDegreeTenSelectedAvoidance_grid_geometric_point_morphisms (L := L) p hp hno
  exact finiteScheme_etale_of_full_rational_points (toBase J) t htbase htinj
    (voisinDegreeTenSelectedAvoidance_grid_geometric_rank_twenty_seven (L := L) p hp hno)

set_option backward.isDefEq.respectTransparency false in
/-- Reducedness belongs to the actual projective complete-intersection
scheme, obtained from its literal split global coordinate algebra. -/
theorem voisinDegreeTenSelectedAvoidance_grid_geometric_reduced
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    IsReduced (scheme (voisinDegreeTenSelectedAvoidance_gridIdeal
      (p.map (algebraMap K L)) (hp.map (algebraMap K L)))) := by
  let J := voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
    (hp.map (algebraMap K L))
  letI : IsFinite (toBase J) :=
    voisinDegreeTenSelectedAvoidance_grid_geometric_finite (L := L) p hp hno
  letI : IsAffine (scheme J) := isAffine_of_isAffineHom (toBase J)
  letI := finiteSchemeCoefficientAlgebra (toBase J)
  obtain ⟨t, htinj, htbase⟩ :=
    voisinDegreeTenSelectedAvoidance_grid_geometric_point_morphisms (L := L) p hp hno
  let e := finiteSchemeCoefficient_equiv_pi_of_full_rational_points
    (toBase J) t htbase htinj
    (voisinDegreeTenSelectedAvoidance_grid_geometric_rank_twenty_seven (L := L) p hp hno)
  letI : _root_.IsReduced Γ(scheme J, ⊤) :=
    isReduced_of_injective e.toRingHom e.injective
  exact isReduced_of_isAffine_isReduced (scheme J)

end PfaffianDescent
