import PfaffianDescent.QuarticTangentRescaling

/-! SOURCE ONLY, UNVERIFIED. Algebraic comparison of independently supplied
coordinate-frame and epsilon representatives. All zero entries are retained.
The change formula is an INTERNAL adapter input; a final original-Z consumer
must derive it from its actual source and ambient presentation squares. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
variable {K : Type*} [Field K]

/-- Columns in the supplied frame are c(i) times canonical column rho(i).
The independent epsilon parameter scales row i by epsilon(i). -/
def suppliedFrameTangent (U : Fin 4 → Fin 4 → K)
    (rho : Equiv.Perm (Fin 4)) (c epsilon : Fin 4 → K) : Fin 4 → Fin 4 → K :=
  fun i j => epsilon i * c i * U (rho i) (rho j) / c j

/-- The square on the column scalar is essential for transferring skewness. -/
def canonicalFrameWeights (rho : Equiv.Perm (Fin 4))
    (c epsilon lambda : Fin 4 → K) : Fin 4 → K :=
  fun r => lambda (rho.symm r) * epsilon (rho.symm r) * c (rho.symm r) ^ 2

theorem suppliedFrameTangent_weight_factor
    (U : Fin 4 → Fin 4 → K) (rho : Equiv.Perm (Fin 4))
    (c epsilon lambda : Fin 4 → K) (hc : ∀ i, c i ≠ 0) (i j : Fin 4) :
    canonicalFrameWeights rho c epsilon lambda (rho i) * U (rho i) (rho j) =
      c i * c j * (lambda i * suppliedFrameTangent U rho c epsilon i j) := by
  simp only [canonicalFrameWeights, rho.symm_apply_apply, suppliedFrameTangent]
  field_simp [hc j]
  <;> ring

theorem suppliedFrameTangent_zero_iff
    (U : Fin 4 → Fin 4 → K) (rho : Equiv.Perm (Fin 4))
    (c epsilon : Fin 4 → K) (hc : ∀ i, c i ≠ 0)
    (hepsilon : ∀ i, epsilon i ≠ 0) (i j : Fin 4) :
    suppliedFrameTangent U rho c epsilon i j = 0 ↔ U (rho i) (rho j) = 0 := by
  simp [suppliedFrameTangent, hc, hepsilon]

theorem canonicalFrameWeights_ne_zero_iff
    (rho : Equiv.Perm (Fin 4)) (c epsilon lambda : Fin 4 → K)
    (hc : ∀ i, c i ≠ 0) (hepsilon : ∀ i, epsilon i ≠ 0) :
    canonicalFrameWeights rho c epsilon lambda ≠ 0 ↔ lambda ≠ 0 := by
  constructor
  · intro h hzero
    apply h
    subst lambda
    funext r
    simp [canonicalFrameWeights]
  · intro h hzero
    apply h
    funext i
    have hi := congrFun hzero (rho i)
    simpa [canonicalFrameWeights, hc, hepsilon] using hi

/-- This permits zero individual weights. No all-nonzero conclusion is
inferred from the weighted condition in lem:uij-skew-symmetric. -/
theorem suppliedFrameTangent_weighted_skew_iff
    (U : Fin 4 → Fin 4 → K) (rho : Equiv.Perm (Fin 4))
    (c epsilon lambda : Fin 4 → K) (hc : ∀ i, c i ≠ 0) :
    (∀ i j, lambda i * suppliedFrameTangent U rho c epsilon i j =
      -(lambda j * suppliedFrameTangent U rho c epsilon j i)) ↔
    (∀ r s, canonicalFrameWeights rho c epsilon lambda r * U r s =
      -(canonicalFrameWeights rho c epsilon lambda s * U s r)) := by
  constructor
  · intro h r s
    let i := rho.symm r
    let j := rho.symm s
    have hs := h i j
    have hi := suppliedFrameTangent_weight_factor U rho c epsilon lambda hc i j
    have hj := suppliedFrameTangent_weight_factor U rho c epsilon lambda hc j i
    have hh : canonicalFrameWeights rho c epsilon lambda (rho i) * U (rho i) (rho j) =
        -(canonicalFrameWeights rho c epsilon lambda (rho j) * U (rho j) (rho i)) := by
      rw [hi, hj, hs]
      ring
    simpa only [i, j, rho.apply_symm_apply] using hh
  · intro h i j
    have hh := h (rho i) (rho j)
    rw [suppliedFrameTangent_weight_factor U rho c epsilon lambda hc i j,
      suppliedFrameTangent_weight_factor U rho c epsilon lambda hc j i] at hh
    apply mul_left_cancel₀ (mul_ne_zero (hc i) (hc j))
    calc
      c i * c j * (lambda i * suppliedFrameTangent U rho c epsilon i j) =
          -(c j * c i * (lambda j * suppliedFrameTangent U rho c epsilon j i)) := hh
      _ = c i * c j * (-(lambda j * suppliedFrameTangent U rho c epsilon j i)) := by ring

/-- Literal supplied skewness and a missing edge produce the legitimate
nonzero row rescaling needed by the original matching/C4 consumer. -/
theorem suppliedFrameTangent_skew_missing_to_canonical
    (U V : Fin 4 → Fin 4 → K) (rho : Equiv.Perm (Fin 4))
    (c epsilon : Fin 4 → K) (hc : ∀ i, c i ≠ 0)
    (hepsilon : ∀ i, epsilon i ≠ 0)
    (hV : V = suppliedFrameTangent U rho c epsilon)
    (hskew : ∀ i j, V i j = -V j i)
    (hmissing : ∃ i j, i ≠ j ∧ V i j = 0) :
    ∃ l : Fin 4 → K, (∀ r, l r ≠ 0) ∧
      (∀ r s, rescaleTangentDirections l U r s =
        -rescaleTangentDirections l U s r) ∧
      (∃ r s, r ≠ s ∧ U r s = 0) := by
  subst V
  let l := canonicalFrameWeights rho c epsilon (fun _ => 1)
  refine ⟨l, ?_, ?_, ?_⟩
  · intro r
    simp [l, canonicalFrameWeights, hc, hepsilon]
  · have hs := (suppliedFrameTangent_weighted_skew_iff U rho c epsilon
        (fun _ => 1) hc).mp (by simpa using hskew)
    simpa only [l, rescaleTangentDirections] using hs
  · obtain ⟨i, j, hij, hz⟩ := hmissing
    exact ⟨rho i, rho j, fun h => hij (rho.injective h),
      (suppliedFrameTangent_zero_iff U rho c epsilon hc hepsilon i j).mp hz⟩

end PfaffianDescent.QuarticNet
