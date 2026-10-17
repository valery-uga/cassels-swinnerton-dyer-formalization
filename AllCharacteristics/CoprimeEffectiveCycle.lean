import AllCharacteristics.CubicDegreeThreeCycle

/-!
# Constructing a degree-one cycle from a prime-to-three effective degree

Bézout coefficients combine any signed cycle of degree coprime to three with
a degree-three cycle. On a cubic surface the latter cycle is constructed,
so a finite-extension point of any prime-to-three degree suffices to produce
a signed degree-one cycle over the same coefficient field.
-/

open AlgebraicGeometry
namespace AllCharacteristics
universe u

/-- Bézout combines a cycle of prime-to-three degree with a degree-three
cycle to construct a signed degree-one cycle. -/
theorem ZeroCycle.exists_degree_one_of_coprime_degree
    {X Y : Scheme.{u}} (f : X ⟶ Y) (z z₃ : ZeroCycle X) (n : ℕ)
    (hz : ZeroCycle.degree f z = (n : ℤ)) (hz₃ : ZeroCycle.degree f z₃ = 3)
    (hn : Nat.Coprime n 3) :
    ∃ w : ZeroCycle X, ZeroCycle.degree f w = 1 := by
  refine ⟨Nat.gcdA n 3 • z + Nat.gcdB n 3 • z₃, ?_⟩
  have hb := Nat.gcd_eq_gcd_ab n 3
  have hg : Nat.gcd n 3 = 1 := hn
  rw [hg] at hb
  simp only [map_add, map_smul, hz, hz₃, smul_eq_mul]
  simpa only [Nat.cast_one, Nat.cast_ofNat, mul_comm] using hb.symm

/-- An effective cycle of degree coprime to three on an actual cubic
surface gives a signed degree-one cycle over every field. -/
theorem cubicSurface_zeroCycle_degree_one_of_effective_coprime
    {k : Type u} [Field k] (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : EffectiveZeroCycle (HomogeneousProjective.hypersurface p hp))
    (hz : Nat.Coprime (EffectiveZeroCycle.degree
      (HomogeneousProjective.hypersurfaceToBase p hp) z) 3) :
    ∃ w : ZeroCycle (HomogeneousProjective.hypersurface p hp),
      ZeroCycle.degree (HomogeneousProjective.hypersurfaceToBase p hp) w = 1 := by
  obtain ⟨z₃, hz₃⟩ := HomogeneousProjective.hypersurface_exists_zeroCycle_degree_three
    0 1 (by decide) p hp
  exact ZeroCycle.exists_degree_one_of_coprime_degree
    (HomogeneousProjective.hypersurfaceToBase p hp) z.toZeroCycle z₃ _
    (EffectiveZeroCycle.degree_toZeroCycle _ z) hz₃ hz

end AllCharacteristics
