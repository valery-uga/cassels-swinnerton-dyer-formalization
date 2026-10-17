import AllCharacteristics.SmoothClosedPointFiber
import AllCharacteristics.CubicFiberDegreeThree
import AllCharacteristics.CubicFiberDescent
import AllCharacteristics.HomogeneousRegularSpecialization

/-!
# Cubic specialization from actual smooth special-fiber points

The finite residue extension and its point are lifted inside the proof. A
prime-to-three special point supplies a signed degree-one cycle on every cubic
fiber. For degree four or five, characteristic-zero descent followed by regular
specialization supplies a point of the residue cubic.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
open HomogeneousProjective
universe u

/-- A prime-to-three closed point of a smooth special cubic fiber supplies a
signed degree-one cycle on every field-valued fiber. The finite free lift and
the degree-three cycle are constructed within the proof. -/
theorem cubic_smooth_fiber_exists_zeroCycle_degree_one
    {R k K : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [Field K]
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (b : R →+* k) (hb : Function.Surjective b)
    (x : closedPoints
      (pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)) : Scheme.{u}))
    (hx : Nat.Coprime
      ((pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))).residueDegree x.1) 3)
    (g : R →+* K) :
    ∃ z : ZeroCycle
        (pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom g))),
      ZeroCycle.degree
        (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom g))) z = 1 := by
  let f := pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom g))
  obtain ⟨w, hw⟩ := exists_effectiveZeroCycle_fiber_of_smooth_closedPoint b hb
    (hypersurfaceToBase p hp) x (Spec.map (CommRingCat.ofHom g))
  have hc : Nat.Coprime (EffectiveZeroCycle.degree f w) 3 := hw.symm ▸ hx
  obtain ⟨y, _, hy⟩ := EffectiveZeroCycle.exists_coprime_degree f w hc
  obtain ⟨z₃, hz₃⟩ := hypersurface_fiber_exists_zeroCycle_degree_three 0 1 (by decide) p hp g
  exact ZeroCycle.exists_degree_one_of_coprime f z₃ hz₃ y hy

/-- A degree-four or degree-five special point of a smooth cubic family over
a complete regular local ring gives a residue-field point whenever the
fraction field has characteristic zero. No lifted subscheme is assumed. -/
theorem specialize_smooth_cubic_closedPoint_degree_four_or_five
    {R K : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (pullback (hypersurfaceToBase p hp)
      (Spec.map (CommRingCat.ofHom (residue R))) : Scheme.{u}))
    (hx : (pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom (residue R)))).residueDegree x.1 = 4 ∨
      (pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom (residue R)))).residueDegree x.1 = 5) :
    ∃ y : Fin 4 → ResidueField R, y ≠ 0 ∧ p.eval₂ (residue R) y = 0 := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_fiber_of_smooth_closedPoint
    (residue R) residue_surjective (hypersurfaceToBase p hp) x
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  have hd := hx.imp (hz.trans ·) (hz.trans ·)
  obtain ⟨y, hy, he⟩ := hypersurface_fiber_coordinates_of_effective_degree_four_or_five
    p hp (algebraMap R K) z hd
  exact specialize_homogeneous_equation_regularLocal p hp y hy he

end AllCharacteristics
