import PfaffianDescent.CorayAffineSurfaceJetExactKernel
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Original ground-polynomial surjectivity onto an actual residue full jet

At a finite separable residue extension, actual minimal polynomials of the
retained coordinates provide pure tangent basis jets. Actual surjectivity of
residue evaluation lifts their nonzero derivative inverses and all remaining
coefficients. No jet-surjectivity or cotangent-rank certificate is supplied.

STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open MvPolynomial TrivSqZeroExt

universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M]

/-- Actual first-order evaluation of a univariate ground polynomial in the
residue-field square-zero algebra, proved by polynomial induction. -/
theorem groundPolynomial_firstOrder_taylor
    (f : Polynomial K) (a : M) (v : Fin 2 → M) :
    Polynomial.aeval (inl a + inr v : CubicSurfaceFirstJet M) f =
      inl (Polynomial.aeval a f) +
        inr ((Polynomial.aeval a f.derivative) • v) := by
  induction f using Polynomial.induction_on with
  | C c => simp [TrivSqZeroExt.algebraMap_eq_inl']
  | add f g hf hg =>
    rw [map_add, hf, hg]
    apply TrivSqZeroExt.ext <;>
      simp [Polynomial.derivative_add, add_smul]
  | monomial n c h =>
    have hpoly : Polynomial.C c * Polynomial.X ^ (n + 1) =
        (Polynomial.C c * Polynomial.X ^ n) * Polynomial.X := by
      rw [pow_succ, mul_assoc]
    rw [hpoly, map_mul, h, Polynomial.aeval_X]
    rw [Polynomial.derivative_mul (f := Polynomial.C c * Polynomial.X ^ n)
      (g := Polynomial.X)]
    simp only [map_add, map_mul, Polynomial.derivative_X, map_one,
      Polynomial.aeval_X, mul_one]
    apply TrivSqZeroExt.ext
    · simp
    · simp only [snd_mul, snd_add, fst_add, fst_inl, fst_inr, snd_inl, snd_inr,
        add_zero, zero_add, op_smul_eq_smul, add_smul, smul_smul]
      simp only [mul_comm, add_comm]

/-- The actual jet map has ORIGINAL ground polynomials as its source. -/
def groundAffineSurfaceJetMap
    (p : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3) :
    MvPolynomial (Fin 3) K →ₐ[K] CubicSurfaceFirstJet M :=
  MvPolynomial.aeval (R := K)
    (affineNormalizedSurfaceJetCoordinates (MvPolynomial.map (algebraMap K M) p) x pivot)

/-- Comparison with actual coefficient extension is proved, not assumed. -/
theorem groundAffineSurfaceJetMap_apply_map
    (p q : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3) :
    groundAffineSurfaceJetMap p x pivot q =
      affineNormalizedSurfaceJetMap (MvPolynomial.map (algebraMap K M) p) x pivot
        (MvPolynomial.map (algebraMap K M) q) := by
  change MvPolynomial.eval₂ (algebraMap K (CubicSurfaceFirstJet M)) _ q =
    MvPolynomial.eval₂ (algebraMap M (CubicSurfaceFirstJet M)) _
      (MvPolynomial.map (algebraMap K M) q)
  rw [MvPolynomial.eval₂_map]
  rfl

/-- Its actual residue value is ORIGINAL ground polynomial evaluation. -/
theorem groundAffineSurfaceJetMap_fst
    (p q : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3) :
    (groundAffineSurfaceJetMap p x pivot q).fst = q.eval₂ (algebraMap K M) x := by
  rw [groundAffineSurfaceJetMap_apply_map, affineNormalizedSurfaceJetMap_fst,
    MvPolynomial.eval_map]

/-- Retained coordinate jets have the literal free tangent basis. -/
theorem groundAffineSurfaceJetMap_free_coordinate
    (p : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3) (r : Fin 2) :
    groundAffineSurfaceJetMap p x pivot (X (pivot.succAbove r)) =
      inl (x (pivot.succAbove r)) + inr (Pi.single r 1) := by
  simp [groundAffineSurfaceJetMap, affineNormalizedSurfaceJetCoordinates,
    affineNormalizedSurfaceRows]

/-- Minimal-polynomial roots and their actual nonzero derivatives construct
an ORIGINAL ground polynomial with each pure free tangent basis jet. -/
theorem groundAffineSurfaceJetMap_pure_basis_preimage
    [CharZero K] [FiniteDimensional K M]
    (p : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3)
    (heval : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K M) x))
    (r : Fin 2) :
    ∃ f : MvPolynomial (Fin 3) K,
      groundAffineSurfaceJetMap p x pivot f = inr (Pi.single r 1) := by
  classical
  let mu := minpoly K (x (pivot.succAbove r))
  let d : M := Polynomial.aeval (x (pivot.succAbove r)) mu.derivative
  have hroot : Polynomial.aeval (x (pivot.succAbove r)) mu = 0 := minpoly.aeval _ _
  have hd : d ≠ 0 :=
    (Algebra.IsSeparable.isSeparable K (x (pivot.succAbove r))).aeval_derivative_ne_zero hroot
  have hmu : groundAffineSurfaceJetMap p x pivot
      (Polynomial.aeval (X (pivot.succAbove r) : MvPolynomial (Fin 3) K) mu) =
      inr (d • Pi.single r 1) := by
    rw [← Polynomial.aeval_algHom_apply, groundAffineSurfaceJetMap_free_coordinate,
      groundPolynomial_firstOrder_taylor, hroot]
    simp only [inl_zero, zero_add]
    rfl
  obtain ⟨g, hg⟩ := heval d⁻¹
  change g.eval₂ (algebraMap K M) x = d⁻¹ at hg
  refine ⟨g * Polynomial.aeval (X (pivot.succAbove r) : MvPolynomial (Fin 3) K) mu, ?_⟩
  apply TrivSqZeroExt.ext
  · simp [map_mul, hmu]
  · simp [map_mul, hmu, TrivSqZeroExt.snd_mul,
      groundAffineSurfaceJetMap_fst, hg, smul_smul, inv_mul_cancel₀ hd,
      mul_inv_cancel₀ hd, op_smul_eq_smul]

/-- Actual residue lifts multiply pure basis jets into every pure tangent
jet, without requiring constants from the extension in the source. -/
theorem groundAffineSurfaceJetMap_pure_preimage
    [CharZero K] [FiniteDimensional K M]
    (p : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3)
    (heval : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K M) x))
    (v : Fin 2 → M) :
    ∃ f : MvPolynomial (Fin 3) K,
      groundAffineSurfaceJetMap p x pivot f = inr v := by
  classical
  choose f hf using groundAffineSurfaceJetMap_pure_basis_preimage p x pivot heval
  choose g hg using (fun r : Fin 2 => heval (v r))
  change ∀ r : Fin 2, (g r).eval₂ (algebraMap K M) x = v r at hg
  have hprod (r : Fin 2) :
      groundAffineSurfaceJetMap p x pivot (g r * f r) = inr (v r • Pi.single r 1) := by
    apply TrivSqZeroExt.ext
    · simp [map_mul, hf]
    · simp [map_mul, hf, TrivSqZeroExt.snd_mul,
        groundAffineSurfaceJetMap_fst, hg, op_smul_eq_smul]
  refine ⟨∑ r : Fin 2, g r * f r, ?_⟩
  rw [map_sum]
  simp_rw [hprod]
  apply TrivSqZeroExt.ext
  · simp
  · funext r
    fin_cases r <;>
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]

/-- ORIGINAL ground polynomials surject onto the entire actual residue full
jet: lift the desired value and then correct its two actual derivatives. -/
theorem groundAffineSurfaceJetMap_surjective
    [CharZero K] [FiniteDimensional K M]
    (p : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3)
    (heval : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K M) x)) :
    Function.Surjective (groundAffineSurfaceJetMap p x pivot) := by
  intro z
  obtain ⟨f, hf⟩ := heval z.fst
  change f.eval₂ (algebraMap K M) x = z.fst at hf
  obtain ⟨g, hg⟩ := groundAffineSurfaceJetMap_pure_preimage p x pivot heval
    (z.snd - (groundAffineSurfaceJetMap p x pivot f).snd)
  refine ⟨f + g, ?_⟩
  apply TrivSqZeroExt.ext
  · simp [map_add, hg, groundAffineSurfaceJetMap_fst, hf]
  · simp [map_add, hg]

/-- At an actual ground hypersurface point, the ORIGINAL defining equation
vanishes in the actual normalized residue jet. -/
theorem groundAffineSurfaceJetMap_equation_zero
    (p : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv pivot p).eval₂ (algebraMap K M) x ≠ 0) :
    groundAffineSurfaceJetMap p x pivot p = 0 := by
  rw [groundAffineSurfaceJetMap_apply_map]
  exact affineNormalizedSurfaceJetCoordinates_equation_zero _ x pivot
    (by simpa only [MvPolynomial.eval_map] using hp)
    (by simpa only [MvPolynomial.pderiv_map, MvPolynomial.eval_map] using hpivot)

end PfaffianDescent.Coray
