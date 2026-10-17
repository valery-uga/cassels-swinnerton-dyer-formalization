import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNormalization

noncomputable section
open AlgebraicGeometry MvPolynomial TrivSqZeroExt
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]

/-- Literal jet residues commute with every polynomial evaluation. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_fst_aeval
    (J : Fin 4 → CubicSurfaceFirstJet K) (q : MvPolynomial (Fin 4) K) :
    (aeval J q).fst = aeval (fun j => (J j).fst) q := by
  have h : (TrivSqZeroExt.fstHom K K (Fin 2 → K)).comp (aeval J) =
      aeval (fun j => (J j).fst) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp
  exact DFunLike.congr_fun h q

/-- The common linear-form value is an actual jet unit as soon as its
actual vector residue is nonzero. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_ell_jet_isUnit
    (ell : MvPolynomial (Fin 4) K) (J : Fin 4 → CubicSurfaceFirstJet K)
    (h : aeval (fun j => (J j).fst) ell ≠ 0) : IsUnit (aeval J ell) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst,
    cubicClosedPointSerreSurfaceJetCotangent_fst_aeval, isUnit_iff_ne_zero]
  exact h

/-- The inverse jet unit has the inverse of the literal linear-form residue. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_normalizingUnit_fst
    (ell : MvPolynomial (Fin 4) K) (J : Fin 4 → CubicSurfaceFirstJet K)
    (hunit : IsUnit (aeval J ell)) :
    (↑hunit.unit⁻¹ : CubicSurfaceFirstJet K).fst =
      (aeval (fun j => (J j).fst) ell)⁻¹ := by
  have hmul : (↑hunit.unit⁻¹ : CubicSurfaceFirstJet K).fst * (aeval J ell).fst = 1 := by
    have h := congrArg (fun z : CubicSurfaceFirstJet K => z.fst) hunit.val_inv_mul
    simpa only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_one] using h
  have hn : (aeval J ell).fst ≠ 0 :=
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hunit).ne_zero
  rw [← cubicClosedPointSerreSurfaceJetCotangent_fst_aeval]
  exact (mul_eq_one_iff_eq_inv₀ hn).mp hmul

/-- The normalized cubic ideal derivative is exactly ell(x)^(-3) times
its original J.snd derivative. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_derivative_scalar
    (ell : MvPolynomial (Fin 4) K) (J : Fin 4 → CubicSurfaceFirstJet K)
    (hunit : IsUnit (aeval J ell)) (q : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 3)
    (hqzero : aeval (fun j => (J j).fst) q = 0) :
    (aeval (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet ell J hunit) q).snd =
      (aeval (fun j => (J j).fst) ell)⁻¹ ^ 3 • (aeval J q).snd := by
  rw [cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_derivative ell J hunit q hq
      (by rw [cubicClosedPointSerreSurfaceJetCotangent_fst_aeval]; exact hqzero),
    cubicClosedPointSerreSurfaceJetCotangent_normalizingUnit_fst]

/-- Normalization retains the literal normalized vector residue. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_fst
    (ell : MvPolynomial (Fin 4) K) (J : Fin 4 → CubicSurfaceFirstJet K)
    (hunit : IsUnit (aeval J ell)) (j : Fin 4) :
    (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet ell J hunit j).fst =
      (aeval (fun k => (J k).fst) ell)⁻¹ * (J j).fst := by
  change ((↑hunit.unit⁻¹ : CubicSurfaceFirstJet K) * J j).fst = _
  rw [TrivSqZeroExt.fst_mul, cubicClosedPointSerreSurfaceJetCotangent_normalizingUnit_fst]

end PfaffianDescent
