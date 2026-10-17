import AllCharacteristics.CubicMultiplicity
import PfaffianDescent.CubicSecant

namespace AllCharacteristics
open PfaffianDescent

universe u

/-- Smooth homogeneous cubic coordinates admit a direction not contained in
their tangent hyperplane. -/
theorem exists_tangent_direction_of_isSmoothCubicCoordinatePoint
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p) :
    ∃ d : Fin 4 → K, c.mixed p d ≠ 0 := by
  obtain ⟨-, -, i, hi⟩ := hs
  refine ⟨Pi.single i 1, ?_⟩
  rw [Cubic.mixed_eq_sum_pderiv_eval]
  simpa [Pi.single_apply] using hi

/-- The tangent linear form of smooth cubic coordinates is nonzero. -/
theorem tangentLinear_ne_zero_of_isSmoothCubicCoordinatePoint
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p) :
    Cubic.tangentLinear c p ≠ 0 := by
  obtain ⟨d, hd⟩ := exists_tangent_direction_of_isSmoothCubicCoordinatePoint c p hs
  intro h
  apply hd
  have := LinearMap.congr_fun h d
  simpa using this

end AllCharacteristics

namespace AllCharacteristics
open PfaffianDescent

universe u

/-- The tangent hyperplane at a smooth point of a cubic surface has dimension
three. -/
theorem tangentLinear_ker_finrank_of_isSmoothCubicCoordinatePoint
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p) :
    Module.finrank K (LinearMap.ker (Cubic.tangentLinear c p)) = 3 := by
  have hne : Cubic.tangentLinear c p ≠ 0 :=
    tangentLinear_ne_zero_of_isSmoothCubicCoordinatePoint c p hs
  have hsurj := surjective_of_nonzero_of_finrank_eq_one (Module.finrank_self K) hne
  have h := (Cubic.tangentLinear c p).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj] at h
  simp only [finrank_top, Module.finrank_self] at h
  rw [Module.finrank_pi, Fintype.card_fin] at h
  omega

end AllCharacteristics

namespace AllCharacteristics
open PfaffianDescent

universe u

/-- A three-coordinate basis for the tangent hyperplane at a smooth cubic
coordinate point. -/
noncomputable def tangentLinearKerBasis
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p) :
    Module.Basis (Fin 3) K (LinearMap.ker (Cubic.tangentLinear c p)) :=
  Module.finBasisOfFinrankEq K (LinearMap.ker (Cubic.tangentLinear c p))
    (tangentLinear_ker_finrank_of_isSmoothCubicCoordinatePoint c p hs)

/-- Each vector in the tangent-hyperplane basis is a tangent direction. -/
theorem tangentLinearKerBasis_mem
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p) (i : Fin 3) :
    c.mixed p ((tangentLinearKerBasis c p hs i).1) = 0 :=
  (tangentLinearKerBasis c p hs i).property

/-- The tangent residual point associated to every basis direction lies on the
cubic. -/
theorem eval_tangentResidualPoint_tangentLinearKerBasis
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hp : c.eval p = 0)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p) (i : Fin 3) :
    c.eval (Cubic.tangentResidualPoint c p
      ((tangentLinearKerBasis c p hs i).1)) = 0 := by
  apply Cubic.eval_tangentResidualPoint
  · exact hp
  · exact tangentLinearKerBasis_mem c p hs i

end AllCharacteristics

namespace AllCharacteristics
open PfaffianDescent
open scoped BigOperators

universe u

noncomputable def tangentDirectionOfCoordinates
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    (u : Fin 3 → K) : Fin 4 → K :=
  ∑ i, u i • ((tangentLinearKerBasis c p hs i).1)

theorem tangentDirectionOfCoordinates_mem
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    (u : Fin 3 → K) :
    c.mixed p (tangentDirectionOfCoordinates c p hs u) = 0 := by
  rw [tangentDirectionOfCoordinates]
  change Cubic.tangentLinear c p (∑ i, u i • ((tangentLinearKerBasis c p hs i).1)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul]
  have hb : Cubic.tangentLinear c p ((tangentLinearKerBasis c p hs i).1) = 0 :=
    (tangentLinearKerBasis c p hs i).property
  rw [hb, smul_zero]

theorem tangentDirectionOfCoordinates_eq_zero_iff
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    (u : Fin 3 → K) :
    tangentDirectionOfCoordinates c p hs u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hsub : ∑ i, u i • tangentLinearKerBasis c p hs i = 0 := by
      apply Subtype.ext
      exact h
    apply funext
    intro i
    exact Fintype.linearIndependent_iff.mp
      (tangentLinearKerBasis c p hs).linearIndependent u hsub i
  · intro h
    subst u
    simp [tangentDirectionOfCoordinates]

theorem eval_tangentResidualPoint_tangentDirectionOfCoordinates
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hp : c.eval p = 0)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    (u : Fin 3 → K) :
    c.eval (Cubic.tangentResidualPoint c p
      (tangentDirectionOfCoordinates c p hs u)) = 0 :=
  Cubic.eval_tangentResidualPoint c p _ hp
    (tangentDirectionOfCoordinates_mem c p hs u)


end AllCharacteristics

namespace AllCharacteristics
open PfaffianDescent
open scoped BigOperators
universe u

noncomputable def tangentDirectionOfCoordinatesMap
    {K S : Type u} [Field K] [Field S] (f : K →+* S)
    (c : Cubic K 4) (p : Fin 4 → K)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    (u : Fin 3 → S) : Fin 4 → S :=
  ∑ i, u i • fun j ↦ f ((tangentLinearKerBasis c p hs i).1 j)

theorem tangentDirectionOfCoordinatesMap_mem
    {K S : Type u} [Field K] [Field S] (f : K →+* S)
    (c : Cubic K 4) (p : Fin 4 → K)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    (u : Fin 3 → S) :
    (c.map f).mixed (fun j ↦ f (p j))
      (tangentDirectionOfCoordinatesMap f c p hs u) = 0 := by
  rw [tangentDirectionOfCoordinatesMap]
  change Cubic.tangentLinear (c.map f) (fun j ↦ f (p j))
    (∑ i, u i • fun j ↦ f ((tangentLinearKerBasis c p hs i).1 j)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul]
  have hb : Cubic.tangentLinear (c.map f) (fun j ↦ f (p j))
      (fun j ↦ f ((tangentLinearKerBasis c p hs i).1 j)) = 0 := by
    rw [Cubic.tangentLinear_apply, Cubic.mixed_map,
      tangentLinearKerBasis_mem c p hs i, map_zero]
  rw [hb, smul_zero]

theorem eval_tangentResidualPoint_tangentDirectionOfCoordinatesMap
    {K S : Type u} [Field K] [Field S] (f : K →+* S)
    (c : Cubic K 4) (p : Fin 4 → K)
    (hp : c.eval p = 0)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    (u : Fin 3 → S) :
    (c.map f).eval (Cubic.tangentResidualPoint (c.map f) (fun j ↦ f (p j))
      (tangentDirectionOfCoordinatesMap f c p hs u)) = 0 := by
  apply Cubic.eval_tangentResidualPoint
  · rw [Cubic.eval_map, hp, map_zero]
  · exact tangentDirectionOfCoordinatesMap_mem f c p hs u

end AllCharacteristics
namespace AllCharacteristics
open PfaffianDescent
universe u

noncomputable def tangentPointInKernel
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hp : c.eval p = 0) :
    LinearMap.ker (Cubic.tangentLinear c p) :=
  ⟨p, Cubic.self_mem_tangentLinear_ker c p hp⟩

theorem tangentPointInKernel_ne_zero
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hp0 : p ≠ 0) (hp : c.eval p = 0) :
    tangentPointInKernel c p hp ≠ 0 := by
  intro h
  apply hp0
  exact congrArg Subtype.val h

theorem tangentLinearKer_quotient_span_point_finrank
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hp0 : p ≠ 0) (hp : c.eval p = 0)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p) :
    Module.finrank K
      ((LinearMap.ker (Cubic.tangentLinear c p)) ⧸
        K ∙ tangentPointInKernel c p hp) = 2 := by
  have hdim := tangentLinear_ker_finrank_of_isSmoothCubicCoordinatePoint c p hs
  have hq := Submodule.finrank_quotient_add_finrank
    (K ∙ tangentPointInKernel c p hp)
  rw [finrank_span_singleton (tangentPointInKernel_ne_zero c p hp0 hp), hdim] at hq
  omega

end AllCharacteristics
namespace AllCharacteristics
open PfaffianDescent
universe u

/-- The tangent hyperplane has a three-vector frame beginning with the cubic
point itself. -/
theorem exists_tangentLinearKer_frame_with_point
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hp0 : p ≠ 0) (hp : c.eval p = 0)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p) :
    ∃ d e : LinearMap.ker (Cubic.tangentLinear c p),
      LinearIndependent K
        (Fin.snoc (Fin.snoc (![tangentPointInKernel c p hp] :
          Fin 1 → LinearMap.ker (Cubic.tangentLinear c p)) d) e) := by
  let z : LinearMap.ker (Cubic.tangentLinear c p) := tangentPointInKernel c p hp
  have hz : z ≠ 0 := tangentPointInKernel_ne_zero c p hp0 hp
  have hdim := tangentLinear_ker_finrank_of_isSmoothCubicCoordinatePoint c p hs
  have hsingle : LinearIndependent K (![z] : Fin 1 →
      LinearMap.ker (Cubic.tangentLinear c p)) :=
    LinearIndependent.of_subsingleton 0 hz
  obtain ⟨d, hd⟩ := exists_linearIndependent_snoc_of_lt_finrank hsingle
    (by omega : 1 < Module.finrank K (LinearMap.ker (Cubic.tangentLinear c p)))
  let w : Fin 2 → LinearMap.ker (Cubic.tangentLinear c p) :=
    Fin.snoc (![z] : Fin 1 → LinearMap.ker (Cubic.tangentLinear c p)) d
  have hw : LinearIndependent K w := hd
  obtain ⟨e, he⟩ := exists_linearIndependent_snoc_of_lt_finrank hw
    (by omega : 2 < Module.finrank K (LinearMap.ker (Cubic.tangentLinear c p)))
  exact ⟨d, e, he⟩

end AllCharacteristics
