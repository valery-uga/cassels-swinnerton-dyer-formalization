import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceConcreteGrid
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import PfaffianDescent.TripleCompleteIntersectionLength

/-! # The actual grid complete intersection has degree twenty-seven -/

noncomputable section
open AlgebraicGeometry CategoryTheory Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

theorem voisinDegreeTenSelectedAvoidance_gridCubic_one_ne_zero
    (K : Type u) [Field K] : voisinDegreeTenSelectedAvoidance_gridCubic K 1 ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (![0, 1, 0, 0] : Fin 4 → K)) h
  simpa [voisinDegreeTenSelectedAvoidance_gridCubic,
    voisinDegreeTenSelectedAvoidance_gridPlane] using he

theorem voisinDegreeTenSelectedAvoidance_gridCubic_one_infinity_eval
    (K : Type u) [Field K] :
    (voisinDegreeTenSelectedAvoidance_gridCubic K 1).eval
      (voisinDegreeTenSelectedAvoidance_gridInfinity K) = 0 := by
  simp [voisinDegreeTenSelectedAvoidance_gridCubic,
    voisinDegreeTenSelectedAvoidance_gridPlane,
    voisinDegreeTenSelectedAvoidance_gridInfinity]

theorem voisinDegreeTenSelectedAvoidance_cubic_ne_zero_of_no_section
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) : p ≠ 0 := by
  have hne := voisinDegreeTenSelectedAvoidance_eval_ne_zero_of_no_section p hp hno
    (voisinDegreeTenSelectedAvoidance_gridInfinity K) (by
      intro h
      have h3 := congrFun h 3
      simpa [voisinDegreeTenSelectedAvoidance_gridInfinity] using h3)
  intro hp0
  simp [hp0] at hne

/-- The surface cubic and first explicit grid cubic are relatively prime.
The excluded rational infinity point separates their scalar spans. -/
theorem voisinDegreeTenSelectedAvoidance_grid_first_relPrime
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    IsRelPrime p (voisinDegreeTenSelectedAvoidance_gridCubic K 1) := by
  have hp0 := voisinDegreeTenSelectedAvoidance_cubic_ne_zero_of_no_section p hp hno
  apply (irreducible_of_smooth_homogeneous_cubic_of_field p hp hp0).isRelPrime_iff_not_dvd.mpr
  intro hdiv
  obtain ⟨a, ha⟩ := homogeneous_dvd_same_degree_eq_smul hp
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1) hp0
    (voisinDegreeTenSelectedAvoidance_gridCubic_one_ne_zero K) hdiv
  have he := congrArg
    (MvPolynomial.eval (voisinDegreeTenSelectedAvoidance_gridInfinity K)) ha
  have hpinf := voisinDegreeTenSelectedAvoidance_eval_ne_zero_of_no_section p hp hno
    (voisinDegreeTenSelectedAvoidance_gridInfinity K) (by
      intro h
      have h3 := congrFun h 3
      simpa [voisinDegreeTenSelectedAvoidance_gridInfinity] using h3)
  rw [voisinDegreeTenSelectedAvoidance_gridCubic_one_infinity_eval] at he
  have ha0 : a = 0 := (mul_eq_zero.mp (by simpa using he.symm)).resolve_right hpinf
  exact voisinDegreeTenSelectedAvoidance_gridCubic_one_ne_zero K (by simpa [ha0] using ha)

/-- The literal homogeneous ideal of the fixed cubic and the two explicit
grid cubics. -/
def voisinDegreeTenSelectedAvoidance_gridIdeal
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) :=
  tripleCompleteIntersectionHomogeneousIdeal p
    (voisinDegreeTenSelectedAvoidance_gridCubic K 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic K 2) hp
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2)

theorem voisinDegreeTenSelectedAvoidance_grid_intersection_finite
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    IsFinite (toBase (voisinDegreeTenSelectedAvoidance_gridIdeal p hp)) :=
  triple_cubic_intersection_finite p
    (voisinDegreeTenSelectedAvoidance_gridCubic K 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic K 2) hp
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2)
    (voisinDegreeTenSelectedAvoidance_cubic_ne_zero_of_no_section p hp hno)
    (voisinDegreeTenSelectedAvoidance_gridCubic_one_ne_zero K)
    (voisinDegreeTenSelectedAvoidance_grid_first_relPrime p hp hno)
    (voisinDegreeTenSelectedAvoidance_concrete_grid_third_regular p hp hno)

/-- The actual complete-intersection structure map has rank twenty-seven.
All properness inputs are discharged by the explicit grid construction. -/
theorem voisinDegreeTenSelectedAvoidance_grid_intersection_rank_twenty_seven
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    letI : IsFinite (toBase (voisinDegreeTenSelectedAvoidance_gridIdeal p hp)) :=
      voisinDegreeTenSelectedAvoidance_grid_intersection_finite p hp hno
    finiteSchemeRank (toBase (voisinDegreeTenSelectedAvoidance_gridIdeal p hp)) = 27 := by
  letI : IsFinite (toBase (voisinDegreeTenSelectedAvoidance_gridIdeal p hp)) :=
    voisinDegreeTenSelectedAvoidance_grid_intersection_finite p hp hno
  exact triple_cubic_intersection_length_twenty_seven p
    (voisinDegreeTenSelectedAvoidance_gridCubic K 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic K 2) hp
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2)
    (voisinDegreeTenSelectedAvoidance_cubic_ne_zero_of_no_section p hp hno)
    (voisinDegreeTenSelectedAvoidance_gridCubic_one_ne_zero K)
    (voisinDegreeTenSelectedAvoidance_grid_first_relPrime p hp hno)
    (voisinDegreeTenSelectedAvoidance_concrete_grid_third_regular p hp hno)

end PfaffianDescent
