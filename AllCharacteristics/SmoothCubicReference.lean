import AllCharacteristics.HypersurfaceJacobianSmooth

/-!
# Explicit smooth cubic surfaces over every field

We verify the two auxiliary cubics used in the Cassels--Swinnerton-Dyer
argument.  Away from characteristic three the Fermat cubic is smooth.  In
characteristic three we use

`X₀³ + X₀X₁² + X₁X₂² + X₂X₃²`.

The proofs are explicit Bézout certificates for the partial derivatives on
each normalized projective chart.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective

universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A field admits a nonzero homogeneous cubic equation defining a smooth
projective surface. -/
def SmoothCubicReferenceFor (k : Type u) [Field k] : Prop :=
  ∃ q : MvPolynomial (Fin 4) k, ∃ hq : q.IsHomogeneous 3,
    q ≠ 0 ∧ Smooth (hypersurfaceToBase q hq)

/-- A three-generator Bézout certificate for a normalized chart. -/
theorem span_chartPDeriv_eq_top_of_three_certificate
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (i₁ i₂ i₃ : Fin 4) (hi₁ : i₁ ≠ j) (hi₂ : i₂ ≠ j) (hi₃ : i₃ ≠ j)
    (a b c₁ c₂ c₃ : MvPolynomial (Fin 4) k)
    (hcert :
      a * p + b * (X j - 1) + c₁ * pderiv i₁ p +
          c₂ * pderiv i₂ p + c₃ * pderiv i₃ p = 1) :
    Ideal.span (Set.range (chartPDeriv p hp j)) = ⊤ := by
  classical
  let I : Ideal (ChartRing (equationIdeal p hp) j) :=
    Ideal.span (Set.range (chartPDeriv p hp j))
  let e := eval₂Hom (chartBaseMap (equationIdeal p hp) j)
    (chartCoordinate (equationIdeal p hp) j)
  have hp_mem : p ∈ (equationIdeal p hp).toIdeal := by
    change p ∈ Ideal.span {p}
    exact Ideal.subset_span (Set.mem_singleton p)
  have hpzero : e p = 0 :=
    eval₂_chartCoordinate_eq_zero_of_mem (equationIdeal p hp) j p hp_mem
  have hjzero : e (X j - 1) = 0 := by
    simp [e, chartCoordinate_self]
  have he := congrArg e hcert
  simp only [map_add, map_mul, map_one] at he
  rw [hpzero, hjzero, mul_zero, mul_zero, zero_add, zero_add] at he
  have hd₁ : e (pderiv i₁ p) ∈ I := by
    change chartPDeriv p hp j ⟨i₁, hi₁⟩ ∈ I
    exact Ideal.subset_span (Set.mem_range_self _)
  have hd₂ : e (pderiv i₂ p) ∈ I := by
    change chartPDeriv p hp j ⟨i₂, hi₂⟩ ∈ I
    exact Ideal.subset_span (Set.mem_range_self _)
  have hd₃ : e (pderiv i₃ p) ∈ I := by
    change chartPDeriv p hp j ⟨i₃, hi₃⟩ ∈ I
    exact Ideal.subset_span (Set.mem_range_self _)
  rw [Ideal.eq_top_iff_one]
  change (1 : ChartRing (equationIdeal p hp) j) ∈ I
  rw [← he]
  exact I.add_mem (I.add_mem (I.mul_mem_left _ hd₁) (I.mul_mem_left _ hd₂))
    (I.mul_mem_left _ hd₃)

/-- The Fermat cubic, used when three is invertible. -/
noncomputable def fermatCubic (k : Type u) [Field k] : MvPolynomial (Fin 4) k :=
  X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 + X 3 ^ 3

theorem fermatCubic_isHomogeneous : (fermatCubic k).IsHomogeneous 3 := by
  simp only [fermatCubic]
  exact (((isHomogeneous_X_pow (R := k) (0 : Fin 4) 3).add
    (isHomogeneous_X_pow (R := k) (1 : Fin 4) 3)).add
      (isHomogeneous_X_pow (R := k) (2 : Fin 4) 3)).add
        (isHomogeneous_X_pow (R := k) (3 : Fin 4) 3)

theorem fermatCubic_ne_zero : fermatCubic k ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval fun i : Fin 4 => if i = 0 then 1 else 0) h
  simp [fermatCubic] at he

/-- The Fermat cubic is smooth whenever three is nonzero. -/
theorem smooth_fermatCubic (h3 : (3 : k) ≠ 0) :
    Smooth (hypersurfaceToBase (fermatCubic k) fermatCubic_isHomogeneous) := by
  have hC3 : (C (3 : k)⁻¹ : MvPolynomial (Fin 4) k) * 3 = 1 := by
    have hnat : (C (3 : k) : MvPolynomial (Fin 4) k) = 3 :=
      map_natCast C 3
    rw [← hnat, ← C_mul]
    simp [h3]
  apply smooth_hypersurface_of_chart_pderiv_span
  intro j
  fin_cases j
  · apply span_chartPDeriv_eq_top_of_three_certificate
      (fermatCubic k) fermatCubic_isHomogeneous 0 1 2 3
      (by decide) (by decide) (by decide)
      1 (-(X 0 ^ 2 + X 0 + 1))
      (-(C (3 : k)⁻¹ * X 1)) (-(C (3 : k)⁻¹ * X 2))
      (-(C (3 : k)⁻¹ * X 3))
    simp [fermatCubic]
    linear_combination -(X 1 ^ 3 + X 2 ^ 3 + X 3 ^ 3) * hC3
  · apply span_chartPDeriv_eq_top_of_three_certificate
      (fermatCubic k) fermatCubic_isHomogeneous 1 0 2 3
      (by decide) (by decide) (by decide)
      1 (-(X 1 ^ 2 + X 1 + 1))
      (-(C (3 : k)⁻¹ * X 0)) (-(C (3 : k)⁻¹ * X 2))
      (-(C (3 : k)⁻¹ * X 3))
    simp [fermatCubic]
    linear_combination -(X 0 ^ 3 + X 2 ^ 3 + X 3 ^ 3) * hC3
  · apply span_chartPDeriv_eq_top_of_three_certificate
      (fermatCubic k) fermatCubic_isHomogeneous 2 0 1 3
      (by decide) (by decide) (by decide)
      1 (-(X 2 ^ 2 + X 2 + 1))
      (-(C (3 : k)⁻¹ * X 0)) (-(C (3 : k)⁻¹ * X 1))
      (-(C (3 : k)⁻¹ * X 3))
    simp [fermatCubic]
    linear_combination -(X 0 ^ 3 + X 1 ^ 3 + X 3 ^ 3) * hC3
  · apply span_chartPDeriv_eq_top_of_three_certificate
      (fermatCubic k) fermatCubic_isHomogeneous 3 0 1 2
      (by decide) (by decide) (by decide)
      1 (-(X 3 ^ 2 + X 3 + 1))
      (-(C (3 : k)⁻¹ * X 0)) (-(C (3 : k)⁻¹ * X 1))
      (-(C (3 : k)⁻¹ * X 2))
    simp [fermatCubic]
    linear_combination -(X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3) * hC3

/-- The replacement cubic in characteristic three. -/
noncomputable def characteristicThreeCubic (k : Type u) [Field k] :
    MvPolynomial (Fin 4) k :=
  X 0 ^ 3 + X 0 * X 1 ^ 2 + X 1 * X 2 ^ 2 + X 2 * X 3 ^ 2

theorem characteristicThreeCubic_isHomogeneous :
    (characteristicThreeCubic k).IsHomogeneous 3 := by
  simp only [characteristicThreeCubic]
  exact (((isHomogeneous_X_pow (R := k) (0 : Fin 4) 3).add
    ((isHomogeneous_X k (0 : Fin 4)).mul
      (isHomogeneous_X_pow (R := k) (1 : Fin 4) 2))).add
      ((isHomogeneous_X k (1 : Fin 4)).mul
        (isHomogeneous_X_pow (R := k) (2 : Fin 4) 2))).add
          ((isHomogeneous_X k (2 : Fin 4)).mul
            (isHomogeneous_X_pow (R := k) (3 : Fin 4) 2))

theorem characteristicThreeCubic_ne_zero : characteristicThreeCubic k ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval fun i : Fin 4 => if i = 0 then 1 else 0) h
  simp [characteristicThreeCubic] at he

/-- The replacement cubic is smooth in characteristic three. -/
theorem smooth_characteristicThreeCubic [CharP k 3] :
    Smooth (hypersurfaceToBase (characteristicThreeCubic k)
      characteristicThreeCubic_isHomogeneous) := by
  have hnat3 : (C (3 : k) : MvPolynomial (Fin 4) k) = 3 :=
    map_natCast C 3
  have h3poly : (3 : MvPolynomial (Fin 4) k) = 0 := by
    rw [← hnat3, show (3 : k) = 0 from CharP.cast_eq_zero k 3, map_zero]
  have h2poly : (2 : MvPolynomial (Fin 4) k) = -1 := by
    linear_combination h3poly
  apply smooth_hypersurface_of_chart_pderiv_span
  intro j
  fin_cases j
  · apply span_chartPDeriv_eq_top_of_three_certificate
      (characteristicThreeCubic k) characteristicThreeCubic_isHomogeneous
      0 1 2 3 (by decide) (by decide) (by decide)
      1 (-(X 0 ^ 2 + X 0 + 1)) (X 1) (-X 2) 0
    simp [characteristicThreeCubic, h2poly]
    linear_combination (X 1 * X 2 ^ 2) * h3poly
  · apply span_chartPDeriv_eq_top_of_three_certificate
      (characteristicThreeCubic k) characteristicThreeCubic_isHomogeneous
      1 0 2 3 (by decide) (by decide) (by decide)
      0 (-(X 1 + 1)) 1 0 0
    simp [characteristicThreeCubic, h3poly, h2poly]
    ring
  · apply span_chartPDeriv_eq_top_of_three_certificate
      (characteristicThreeCubic k) characteristicThreeCubic_isHomogeneous
      2 0 1 3 (by decide) (by decide) (by decide)
      0 (-(X 0 * X 1 * X 2 + X 0 * X 1 + X 2 + 1))
      (X 0 ^ 2) (X 0 * X 1 + 1) 0
    simp [characteristicThreeCubic, h3poly, h2poly]
    ring
  · apply span_chartPDeriv_eq_top_of_three_certificate
      (characteristicThreeCubic k) characteristicThreeCubic_isHomogeneous
      3 0 1 2 (by decide) (by decide) (by decide)
      0 (-(X 1 * X 2 * X 3 + X 1 * X 2 + X 3 + 1))
      (X 2 ^ 2) 0 (X 1 * X 2 + 1)
    simp [characteristicThreeCubic, h3poly, h2poly]
    ring

/-- Every field has an explicit nonzero smooth cubic surface. -/
theorem smoothCubicReferenceFor (k : Type u) [Field k] :
    SmoothCubicReferenceFor k := by
  by_cases h3 : (3 : k) = 0
  · letI : CharP k 3 :=
      (CharP.charP_iff_prime_eq_zero (by decide)).2 h3
    exact ⟨characteristicThreeCubic k, characteristicThreeCubic_isHomogeneous,
      characteristicThreeCubic_ne_zero, smooth_characteristicThreeCubic⟩
  · exact ⟨fermatCubic k, fermatCubic_isHomogeneous,
      fermatCubic_ne_zero, smooth_fermatCubic h3⟩

end HomogeneousProjective
end AllCharacteristics
