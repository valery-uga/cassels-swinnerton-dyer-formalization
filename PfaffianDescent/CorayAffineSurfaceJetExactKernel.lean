import PfaffianDescent.CorayAffineSurfaceJetCompleteness

/-!
# The actual first infinitesimal neighbourhood of an affine surface point

Canonical free coordinates provide explicit preimages for the full jet.
The previously constructed completeness implication is combined with direct
square-zero multiplication to identify its kernel exactly. The actual quotient
is then isomorphic to the three-dimensional first-jet algebra.

STATUS: UNVERIFIED source draft. Root owns all compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open MvPolynomial TrivSqZeroExt Module

universe u
variable {M : Type u} [Field M]

/-- The literal normalized full-jet evaluation algebra homomorphism. -/
def affineNormalizedSurfaceJetMap
    (p : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3) :
    MvPolynomial (Fin 3) M →ₐ[M] CubicSurfaceFirstJet M :=
  aeval (affineNormalizedSurfaceJetCoordinates p x pivot)

/-- Each actual free-coordinate difference maps to its prescribed basis jet. -/
theorem affineNormalizedSurfaceJetMap_free_difference
    (p : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3) (r : Fin 2) :
    affineNormalizedSurfaceJetMap p x pivot
        (X (pivot.succAbove r) - C (x (pivot.succAbove r))) =
      inr (Pi.single r 1) := by
  simp [affineNormalizedSurfaceJetMap, affineNormalizedSurfaceJetCoordinates,
    affineNormalizedSurfaceRows, TrivSqZeroExt.algebraMap_eq_inl]

/-- The canonical full jet is surjective, with an explicit polynomial
preimage for every value and pair of derivatives. -/
theorem affineNormalizedSurfaceJetMap_surjective
    (p : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3) :
    Function.Surjective (affineNormalizedSurfaceJetMap p x pivot) := by
  classical
  intro z
  refine ⟨C z.fst + ∑ r : Fin 2,
    C (z.snd r) * (X (pivot.succAbove r) - C (x (pivot.succAbove r))), ?_⟩
  simp only [map_add, map_sum, map_mul,
    affineNormalizedSurfaceJetMap_free_difference]
  apply TrivSqZeroExt.ext
  · simp [affineNormalizedSurfaceJetMap, affineNormalizedSurfaceJetCoordinates,
      affineNormalizedSurfaceRows, TrivSqZeroExt.algebraMap_eq_inl]
  · funext r
    fin_cases r <;>
      simp [affineNormalizedSurfaceJetMap, affineNormalizedSurfaceJetCoordinates,
        affineNormalizedSurfaceRows, Fin.sum_univ_two,
        TrivSqZeroExt.algebraMap_eq_inl, Pi.single_apply]

/-- The jet value is actual polynomial evaluation at the point. -/
theorem affineNormalizedSurfaceJetMap_fst
    (p q : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3) :
    (affineNormalizedSurfaceJetMap p x pivot q).fst = eval x q := by
  unfold affineNormalizedSurfaceJetMap affineNormalizedSurfaceJetCoordinates
  rw [cubicClosedPointSerreSurfaceJets_taylor]
  simp

/-- Products of two point-ideal elements vanish in the actual full jet. -/
theorem affinePoint_square_le_normalizedSurfaceJet_kernel
    (p : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3) :
    affinePointIdeal x ^ 2 ≤
      RingHom.ker (affineNormalizedSurfaceJetMap p x pivot).toRingHom := by
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro f hf g hg
  change affineNormalizedSurfaceJetMap p x pivot (f * g) = 0
  rw [map_mul]
  have hfzero : (affineNormalizedSurfaceJetMap p x pivot f).fst = 0 := by
    rw [affineNormalizedSurfaceJetMap_fst]
    exact hf
  have hgzero : (affineNormalizedSurfaceJetMap p x pivot g).fst = 0 := by
    rw [affineNormalizedSurfaceJetMap_fst]
    exact hg
  apply TrivSqZeroExt.ext
  · simp [TrivSqZeroExt.fst_mul, hfzero, hgzero]
  · simp [TrivSqZeroExt.snd_mul, hfzero, hgzero]

/-- Exact kernel equality, with both directions genuinely proved. -/
theorem affineNormalizedSurfaceJetMap_kernel
    (p : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : eval x p = 0) (hpivot : eval x (pderiv pivot p) ≠ 0) :
    RingHom.ker (affineNormalizedSurfaceJetMap p x pivot).toRingHom =
      affinePointIdeal x ^ 2 ⊔ Ideal.span ({p} : Set (MvPolynomial (Fin 3) M)) := by
  apply le_antisymm
  · intro q hq
    exact affineNormalizedSurfaceJet_zero_mem_square_sup_equation p q x pivot hp hpivot hq
  · apply sup_le
    · exact affinePoint_square_le_normalizedSurfaceJet_kernel p x pivot
    · apply Ideal.span_le.mpr
      intro q hq
      have hqp : q = p := Set.mem_singleton_iff.mp hq
      rw [hqp]
      exact affineNormalizedSurfaceJetCoordinates_equation_zero p x pivot hp hpivot

/-- The literal first infinitesimal surface-point quotient is the actual
full jet algebra, via its actual evaluation map. -/
def affineSurfacePointFirstOrderEquiv
    (p : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : eval x p = 0) (hpivot : eval x (pderiv pivot p) ≠ 0) :
    (MvPolynomial (Fin 3) M ⧸
      (affinePointIdeal x ^ 2 ⊔ Ideal.span ({p} : Set (MvPolynomial (Fin 3) M)))) ≃ₐ[M]
      CubicSurfaceFirstJet M :=
  (Ideal.quotientEquivAlgOfEq M
    (affineNormalizedSurfaceJetMap_kernel p x pivot hp hpivot).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (affineNormalizedSurfaceJetMap_surjective p x pivot))

/-- The isomorphism sends actual polynomial classes to actual jet evaluations. -/
theorem affineSurfacePointFirstOrderEquiv_mk
    (p q : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : eval x p = 0) (hpivot : eval x (pderiv pivot p) ≠ 0) :
    affineSurfacePointFirstOrderEquiv p x pivot hp hpivot
      (Ideal.Quotient.mk
        (affinePointIdeal x ^ 2 ⊔ Ideal.span ({p} : Set (MvPolynomial (Fin 3) M))) q) =
      affineNormalizedSurfaceJetMap p x pivot q := by
  rfl

/-- The actual first-order surface-point quotient has dimension three over
the point field, proved through the constructed actual algebra isomorphism. -/
theorem affineSurfacePointFirstOrder_finrank
    (p : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : eval x p = 0) (hpivot : eval x (pderiv pivot p) ≠ 0) :
    finrank M (MvPolynomial (Fin 3) M ⧸
      (affinePointIdeal x ^ 2 ⊔ Ideal.span ({p} : Set (MvPolynomial (Fin 3) M)))) = 3 := by
  rw [(affineSurfacePointFirstOrderEquiv p x pivot hp hpivot).toLinearEquiv.finrank_eq]
  change finrank M (M × (Fin 2 → M)) = 3
  simp [Module.finrank_prod, Module.finrank_pi_fintype]

end PfaffianDescent.Coray
