import PfaffianDescent.CubicElevenPointCanonicalJetMinor

/-!
Jacobian-pivot tangent rows with denominators cleared. Their entries are
polynomial in the gradient, so they specialize from the actual universal
configuration coordinate ring without a field or an inverse operation.
-/

noncomputable section
namespace PfaffianDescent

open MvPolynomial Module TrivSqZeroExt
open AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective AllCharacteristics.UniversalHomogeneous

universe u v

def cubicPolynomialTangentRow
    {R : Type u} [CommRing R] (anchor : Fin 4) (g : Fin 4 → R) (pivot : Fin 3) :
    Fin 4 → Fin 2 → R :=
  Fin.insertNth anchor 0 (Fin.insertNth pivot
    (fun t => -g (anchor.succAbove (pivot.succAbove t)))
    (fun t => g (anchor.succAbove pivot) • Pi.single t 1))

@[simp] theorem cubicPolynomialTangentRow_diag
    {R : Type u} [CommRing R] (anchor : Fin 4) (g : Fin 4 → R) (pivot : Fin 3) :
    cubicPolynomialTangentRow anchor g pivot anchor = 0 := by
  simp [cubicPolynomialTangentRow]

@[simp] theorem cubicPolynomialTangentRow_free
    {R : Type u} [CommRing R] (anchor : Fin 4) (g : Fin 4 → R)
    (pivot : Fin 3) (t : Fin 2) :
    cubicPolynomialTangentRow anchor g pivot (anchor.succAbove (pivot.succAbove t)) =
      g (anchor.succAbove pivot) • Pi.single t 1 := by
  simp [cubicPolynomialTangentRow]

theorem cubicPolynomialTangentRow_gradient_zero
    {R : Type u} [CommRing R] (anchor : Fin 4) (g : Fin 4 → R) (pivot : Fin 3) :
    ∑ j, g j • cubicPolynomialTangentRow anchor g pivot j = 0 := by
  classical
  rw [Fin.sum_univ_succAbove _ anchor]
  simp only [cubicPolynomialTangentRow_diag, smul_zero, zero_add]
  simp only [cubicPolynomialTangentRow, Fin.insertNth_apply_succAbove]
  rw [Fin.sum_univ_succAbove _ pivot]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  funext t
  simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases t <;> simp <;> ring

theorem cubicPolynomialTangentRow_map
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (f : R →+* S) (anchor : Fin 4) (g : Fin 4 → R) (pivot : Fin 3) :
    (fun j t => f (cubicPolynomialTangentRow anchor g pivot j t)) =
      cubicPolynomialTangentRow anchor (fun j => f (g j)) pivot := by
  classical
  funext j t
  by_cases hj : j = anchor
  · subst j
    simp
  obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hj
  by_cases hr : r = pivot
  · subst r
    simp [cubicPolynomialTangentRow]
  obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hr
  by_cases hts : t = s <;>
    simp [cubicPolynomialTangentRow, Pi.single_apply, smul_eq_mul, hts]

theorem cubicPolynomialTangentRow_eq_scaled_native
    {K : Type u} [Field K] (anchor : Fin 4) (g : Fin 4 → K) (pivot : Fin 3)
    (hpivot : g (anchor.succAbove pivot) ≠ 0) :
    cubicPolynomialTangentRow anchor g pivot = fun j =>
      g (anchor.succAbove pivot) • cubicClosedPointSerreSurfaceJets_row anchor
        (fun r => g (anchor.succAbove r)) pivot j := by
  funext j t
  by_cases hj : j = anchor
  · subst j
    simp
  obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hj
  by_cases hr : r = pivot
  · subst r
    simp [cubicPolynomialTangentRow, cubicClosedPointSerreSurfaceJets_row,
      smul_eq_mul]
    field_simp
  obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hr
  simp [cubicPolynomialTangentRow, cubicClosedPointSerreSurfaceJets_row]

/-- Clearing the actual nonzero gradient pivots preserves full
interpolation by an invertible change in the square-zero directions. -/
theorem cubicFullJetCoordinates_surjective_polynomialTangentRows
    {K : Type u} [Field K]
    (x : Fin 11 → Fin 4 → K) (anchor : Fin 3 → Fin 4)
    (g : Fin 3 → Fin 4 → K) (pivot : Fin 3 → Fin 3)
    (hpivot : ∀ i, g i ((anchor i).succAbove (pivot i)) ≠ 0)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction x
      (cubicFullJetCoordinates x (fun i => cubicClosedPointSerreSurfaceJets_row
        (anchor i) (fun r => g i ((anchor i).succAbove r)) (pivot i))))) :
    Function.Surjective (cubicElevenPointFullJetRestriction x
      (cubicFullJetCoordinates x (fun i => cubicPolynomialTangentRow
        (anchor i) (g i) (pivot i)))) := by
  let T : Fin 3 → (Fin 2 → K) →ₗ[K] (Fin 2 → K) := fun i =>
    LinearMap.lsmul K (Fin 2 → K) (g i ((anchor i).succAbove (pivot i)))⁻¹
  refine cubicElevenPointFullJetRestriction_surjective_of_frameMap x
    (cubicFullJetCoordinates x (fun i => cubicClosedPointSerreSurfaceJets_row
      (anchor i) (fun r => g i ((anchor i).succAbove r)) (pivot i)))
    (cubicFullJetCoordinates x (fun i => cubicPolynomialTangentRow
      (anchor i) (g i) (pivot i))) T ?_ ?_ hfull
  · intro i
    exact smul_right_injective _ (inv_ne_zero (hpivot i))
  · intro i j
    apply TrivSqZeroExt.ext
    · simp [cubicFullJetCoordinates]
    · simp only [TrivSqZeroExt.snd_map, cubicFullJetCoordinates, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      rw [cubicPolynomialTangentRow_eq_scaled_native (anchor i) (g i) (pivot i) (hpivot i)]
      change cubicClosedPointSerreSurfaceJets_row (anchor i)
        (fun r => g i ((anchor i).succAbove r)) (pivot i) j =
        (g i ((anchor i).succAbove (pivot i)))⁻¹ •
          (g i ((anchor i).succAbove (pivot i)) •
            cubicClosedPointSerreSurfaceJets_row (anchor i)
              (fun r => g i ((anchor i).succAbove r)) (pivot i) j)
      rw [inv_smul_smul₀ (hpivot i)]

/-- The actual smooth-cubic witness uses tangent entries polynomial in
its coordinates and the cubic coefficients, ready for generic transport. -/
theorem exists_cubicSurfaceElevenPoint_native_polynomialJetMinor
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (x : Fin 11 → Fin 4 → K) (anchor : Fin 11 → Fin 4)
      (pivot : Fin 3 → Fin 3) (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3),
      (∀ i, x i (anchor i) = 1) ∧ (∀ i, aeval (x i) p = 0) ∧
      (∀ i j, i ≠ j → ∀ a : K, a • x i ≠ x j) ∧
      (∀ i, aeval (x (i.castAdd 8))
        (pderiv ((anchor (i.castAdd 8)).succAbove (pivot i)) p) ≠ 0) ∧
      IsUnit (homogeneousFullJetEvaluationMinor m x (fun i =>
        cubicPolynomialTangentRow (anchor (i.castAdd 8))
          (fun j => aeval (x (i.castAdd 8)) (pderiv j p)) (pivot i))).det := by
  obtain ⟨x, anchor, pivot, m, hx, hpx, hdir, hpivot, hm⟩ :=
    exists_cubicSurfaceElevenPoint_native_canonicalJetMinor p hp hp0
  let g : Fin 3 → Fin 4 → K := fun i j => aeval (x (i.castAdd 8)) (pderiv j p)
  have hfull := cubicFullJetCoordinates_interpolation_of_unitMinor x
    (fun i => cubicClosedPointSerreSurfaceJets_row (anchor (i.castAdd 8))
      (fun r => g i ((anchor (i.castAdd 8)).succAbove r)) (pivot i)) m hm
  have hfull' := cubicFullJetCoordinates_surjective_polynomialTangentRows x
    (fun i => anchor (i.castAdd 8)) g pivot hpivot hfull
  let J := cubicFullJetCoordinates x (fun i => cubicPolynomialTangentRow
    (anchor (i.castAdd 8)) (g i) (pivot i))
  have hresidue : ∀ i j, (J i j).fst = x (i.castAdd 8) j := by
    intros
    simp [J, cubicFullJetCoordinates]
  obtain ⟨m', hm'⟩ := exists_unit_homogeneousFullJetEvaluationMinor_of_fullJets
    x J hresidue hfull'
  refine ⟨x, anchor, pivot, m', hx, hpx, hdir, hpivot, ?_⟩
  simpa [J, cubicFullJetCoordinates, g] using hm'

end PfaffianDescent
