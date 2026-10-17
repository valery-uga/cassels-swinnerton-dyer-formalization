import PfaffianDescent.QuadraticSecant
import PfaffianDescent.QuarticBinaryForms

/-! SOURCE ONLY / UNVERIFIED. Literal quadratic-times-linear factorization
of the original binary cubic restriction. The linear residual point includes
infinity. No residual point, factorization or dimension certificate is input. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial
open scoped BigOperators
universe u
variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- A moved element of a quadratic extension is itself a quadratic generator.
The basis and both coefficient identities are derived, not supplied. -/
theorem movedQuadraticElement_generator [FiniteDimensional k E]
    (hdeg : finrank k E = 2) (sigma : E ≃ₐ[k] E)
    (alpha : E) (hAlpha : alpha ≠ sigma alpha) :
    (∀ z : E, ∃ a b : k, z = algebraMap k E a + algebraMap k E b * alpha) ∧
    (∀ a b : k, algebraMap k E a + algebraMap k E b * alpha = 0 → a = 0 ∧ b = 0) := by
  classical
  let f := algebraMap k E
  have hLI : LinearIndependent k ![(1 : E), alpha] := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hc' : f (c 0) + f (c 1) * alpha = 0 := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Algebra.smul_def, mul_one] using hc
    have hSigma := congrArg sigma hc'
    have hf (a : k) : sigma (f a) = f a := sigma.commutes a
    simp only [map_add, map_mul, hf, map_zero] at hSigma
    have hc1 : c 1 = 0 := by
      apply f.injective
      rw [map_zero]
      apply (mul_eq_zero.mp (show f (c 1) * (alpha - sigma alpha) = 0 by
        linear_combination hc' - hSigma)).resolve_right (sub_ne_zero.mpr hAlpha)
    have hc0 : c 0 = 0 := by
      apply f.injective
      simpa only [hc1, map_zero, zero_mul, add_zero] using hc'
    fin_cases i
    · exact hc0
    · exact hc1
  let b := basisOfLinearIndependentOfCardEqFinrank hLI
    (show Fintype.card (Fin 2) = finrank k E by simp [hdeg])
  have hb : (b : Fin 2 → E) = ![1, alpha] :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  refine ⟨?_, ?_⟩
  · intro z
    refine ⟨b.repr z 0, b.repr z 1, ?_⟩
    have h := (b.sum_repr z).symm
    rw [Fin.sum_univ_two] at h
    simpa only [hb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Algebra.smul_def, mul_one] using h
  · intro a c h
    have hh : ∑ i : Fin 2, ![a, c] i • ![(1 : E), alpha] i = 0 := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Algebra.smul_def, mul_one] using h
    have he := Fintype.linearIndependent_iff.mp hLI ![a, c] hh
    exact ⟨he 0, he 1⟩

/-- The actual ground quadratic factor cutting out the chosen conjugate pair. -/
def quadraticSecantBinaryFactor (r s : k) : MvPolynomial (Fin 2) k :=
  X 1 ^ 2 - C s * X 0 * X 1 - C r * X 0 ^ 2

/-- The actual linear residual factor, without choosing an affine chart. -/
def quadraticSecantResidualLinearFactor (c d s : k) : MvPolynomial (Fin 2) k :=
  C d * X 1 + C (c + s * d) * X 0

/-- The SAME restriction factors by the actual chosen quadratic point and
its conjugate. When it is nonzero the residual linear factor determines a
nonzero GROUND projective point, including its possible point at infinity. -/
theorem binaryCubic_chosenQuadratic_residual [FiniteDimensional k E]
    (hdeg : finrank k E = 2) (sigma : E ≃ₐ[k] E)
    (alpha : E) (hAlpha : alpha ≠ sigma alpha)
    (H : MvPolynomial (Fin 2) k) (hH : H.IsHomogeneous 3)
    (hRoot : aeval ![1, alpha] H = (0 : E)) :
    ∃ r s c d : k,
      alpha ^ 2 = algebraMap k E r + algebraMap k E s * alpha ∧
      H = quadraticSecantBinaryFactor r s * quadraticSecantResidualLinearFactor c d s ∧
      MvPolynomial.map (algebraMap k E) (quadraticSecantBinaryFactor r s) =
        (X 1 - C alpha * X 0) * (X 1 - C (sigma alpha) * X 0) ∧
      (H = 0 ∨
        (H ≠ 0 ∧
          let w : Fin 2 → k := ![d, -(c + s * d)]
          w ≠ 0 ∧ aeval w (quadraticSecantResidualLinearFactor c d s) = 0 ∧
            aeval w H = 0)) := by
  classical
  let f := algebraMap k E
  obtain ⟨hspan, hind⟩ := movedQuadraticElement_generator hdeg sigma alpha hAlpha
  obtain ⟨r, s, hrs⟩ := hspan (alpha ^ 2)
  obtain ⟨a, b, c, d, hExpansion⟩ := QuarticNet.binary_cubic_expansion H hH
  have hRoot' : f a + alpha * f b + alpha ^ 2 * f c + alpha ^ 3 * f d = 0 := by
    rw [hExpansion] at hRoot
    simpa only [map_add, map_mul, map_pow, aeval_C, aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_pow,
      one_mul, mul_comm, mul_left_comm, mul_assoc] using hRoot
  have he : f (a + r * c + r * s * d) +
      f (b + s * c + (r + s ^ 2) * d) * alpha = 0 := by
    simp only [map_add, map_mul, map_pow]
    linear_combination hRoot' - (f c + (alpha + f s) * f d) * hrs
  obtain ⟨h0, h1⟩ := hind _ _ he
  have ha : a = -(r * c + r * s * d) := by linear_combination h0
  have hb : b = -(s * c + (r + s ^ 2) * d) := by linear_combination h1
  have hFactor : H = quadraticSecantBinaryFactor r s *
      quadraticSecantResidualLinearFactor c d s := by
    rw [hExpansion, ha, hb]
    simp only [quadraticSecantBinaryFactor, quadraticSecantResidualLinearFactor,
      map_neg, map_add, map_mul, map_pow]
    ring
  have hSigma := congrArg sigma hrs
  simp only [map_add, map_mul, map_pow, sigma.commutes] at hSigma
  have hTrace : f s = alpha + sigma alpha := by
    have h := (mul_eq_zero.mp
      (show (alpha - sigma alpha) * (alpha + sigma alpha - f s) = 0 by
        linear_combination hrs - hSigma)).resolve_left (sub_ne_zero.mpr hAlpha)
    linear_combination -h
  have hNorm : f r = -(alpha * sigma alpha) := by
    rw [hTrace] at hrs
    linear_combination -hrs
  have hConjugateFactor : MvPolynomial.map f (quadraticSecantBinaryFactor r s) =
      (X 1 - C alpha * X 0) * (X 1 - C (sigma alpha) * X 0) := by
    simp only [quadraticSecantBinaryFactor, map_sub, map_mul, map_pow,
      MvPolynomial.map_X, MvPolynomial.map_C, hTrace, hNorm, map_add, map_neg, map_mul]
    ring
  refine ⟨r, s, c, d, hrs, hFactor, hConjugateFactor, ?_⟩
  by_cases hz : H = 0
  · exact Or.inl hz
  · right
    refine ⟨hz, ?_⟩
    dsimp only
    have hw : (![d, -(c + s * d)] : Fin 2 → k) ≠ 0 := by
      intro h
      have hd : d = 0 := by simpa only [Matrix.cons_val_zero, Pi.zero_apply] using congrFun h 0
      have hc : c = 0 := by
        have hh := congrFun h 1
        change -(c + s * d) = 0 at hh
        simpa only [hd, mul_zero, add_zero, neg_eq_zero] using hh
      apply hz
      rw [hFactor]
      simp only [quadraticSecantResidualLinearFactor, hc, hd, mul_zero, add_zero,
        map_zero, zero_mul, mul_zero]
    have hLinear : aeval (![d, -(c + s * d)] : Fin 2 → k)
        (quadraticSecantResidualLinearFactor c d s) = 0 := by
      simp only [quadraticSecantResidualLinearFactor, map_add, map_mul, aeval_C,
        aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Algebra.algebraMap_self, RingHom.id_apply]
      ring
    refine ⟨hw, hLinear, ?_⟩
    rw [hFactor, map_mul, hLinear, mul_zero]

end PfaffianDescent
