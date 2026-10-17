import PfaffianDescent.CorayAffineSurfaceJetCompleteness
import PfaffianDescent.CubicNormalizedSurfaceTangentJets

/-!
# Actual normalized projective jets give affine point-square membership

The coordinate-one substitution is made directly in three indexed variables.
Its derivative and jet compatibility are proved, rather than supplied as a
coordinate-comparison certificate.

STATUS: UNVERIFIED source draft. Root owns all compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open MvPolynomial TrivSqZeroExt

universe u
variable {M : Type u} [Field M]

/-- Set the anchor coordinate equal to one; retain actual Fin3 coordinates. -/
def normalizedAffineEquation (anchor : Fin 4) :
    MvPolynomial (Fin 4) M →ₐ[M] MvPolynomial (Fin 3) M :=
  aeval (Fin.insertNth anchor 1 X)

/-- Coordinate-one substitution commutes with every retained partial. -/
theorem normalizedAffineEquation_partial
    (anchor : Fin 4) (i : Fin 3) (p : MvPolynomial (Fin 4) M) :
    pderiv i (normalizedAffineEquation anchor p) =
      normalizedAffineEquation anchor (pderiv (anchor.succAbove i) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [normalizedAffineEquation, pderiv_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      rw [map_mul, pderiv_mul, hp, pderiv_mul, map_add, map_mul, map_mul]
      by_cases hj : j = anchor
      · subst j
        simp [normalizedAffineEquation, pderiv_one,
          pderiv_X_of_ne (Fin.succAbove_ne anchor i).symm]
      · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hj
        simp [normalizedAffineEquation, pderiv_X, Pi.single_apply,
          Fin.succAbove_right_inj]

/-- Evaluation after elimination is literal homogeneous-coordinate
evaluation at any point whose anchor coordinate equals one. -/
theorem normalizedAffineEquation_evaluation
    (anchor : Fin 4) (x : Fin 4 → M) (hx : x anchor = 1) :
    (aeval (R := M) (fun i => x (anchor.succAbove i))).comp
      (normalizedAffineEquation (M := M) anchor) = aeval (R := M) x := by
  classical
  apply MvPolynomial.algHom_ext
  intro j
  by_cases hj : j = anchor
  · subst j
    simp [normalizedAffineEquation, hx]
  · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [normalizedAffineEquation]

/-- The actual affine gradient is the retained actual projective gradient. -/
theorem normalizedAffineEquation_partial_evaluation
    (anchor : Fin 4) (x : Fin 4 → M) (hx : x anchor = 1)
    (p : MvPolynomial (Fin 4) M) (i : Fin 3) :
    eval (fun r => x (anchor.succAbove r))
        (pderiv i (normalizedAffineEquation anchor p)) =
      eval x (pderiv (anchor.succAbove i) p) := by
  rw [normalizedAffineEquation_partial]
  exact AlgHom.congr_fun (normalizedAffineEquation_evaluation anchor x hx)
    (pderiv (anchor.succAbove i) p)

/-- The normalized two-direction affine coordinates are exactly the retained
coordinates of the existing native projective Jacobian-pivot jet. -/
theorem normalizedAffineEquation_jet_coordinate
    (anchor : Fin 4) (x : Fin 4 → M) (hx : x anchor = 1)
    (p : MvPolynomial (Fin 4) M) (pivot : Fin 3) (i : Fin 3) :
    affineNormalizedSurfaceJetCoordinates (normalizedAffineEquation anchor p)
        (fun r => x (anchor.succAbove r)) pivot i =
      cubicNormalizedSurfacePoint_tangentJet p anchor x pivot (anchor.succAbove i) := by
  unfold affineNormalizedSurfaceJetCoordinates affineNormalizedSurfaceRows
    cubicNormalizedSurfacePoint_tangentJet cubicClosedPointSerreSurfaceJets_row
  simp_rw [normalizedAffineEquation_partial_evaluation anchor x hx]
  simp only [Fin.insertNth_apply_succAbove, MvPolynomial.aeval_eq_eval]

/-- The full actual jet commutes with the actual coordinate-one polynomial
map, including the distinguished coordinate and both tangent directions. -/
theorem normalizedAffineEquation_jet_evaluation
    (anchor : Fin 4) (x : Fin 4 → M) (hx : x anchor = 1)
    (p : MvPolynomial (Fin 4) M) (pivot : Fin 3) :
    (aeval (R := M) (affineNormalizedSurfaceJetCoordinates (normalizedAffineEquation anchor p)
      (fun r => x (anchor.succAbove r)) pivot)).comp
        (normalizedAffineEquation (M := M) anchor) =
      aeval (R := M) (cubicNormalizedSurfacePoint_tangentJet p anchor x pivot) := by
  classical
  apply MvPolynomial.algHom_ext
  intro j
  by_cases hj : j = anchor
  · subst j
    simp [normalizedAffineEquation, cubicNormalizedSurfacePoint_tangentJet,
      cubicClosedPointSerreSurfaceJets_row, hx]
  · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hj
    simpa [normalizedAffineEquation] using
      normalizedAffineEquation_jet_coordinate anchor x hx p pivot r

/-- Actual normalized projective full-jet vanishing gives membership in the
affine point square modulo the actual eliminated surface equation. -/
theorem normalizedProjectiveJet_zero_mem_affine_square_sup_equation
    (p q : MvPolynomial (Fin 4) M) (anchor : Fin 4)
    (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3)
    (hp : eval x p = 0)
    (hpivot : eval x (pderiv (anchor.succAbove pivot) p) ≠ 0)
    (hq : aeval (cubicNormalizedSurfacePoint_tangentJet p anchor x pivot) q = 0) :
    normalizedAffineEquation anchor q ∈
      affinePointIdeal (fun i => x (anchor.succAbove i)) ^ 2 ⊔
        Ideal.span ({normalizedAffineEquation anchor p} :
          Set (MvPolynomial (Fin 3) M)) := by
  have hvalue : eval (fun i => x (anchor.succAbove i))
      (normalizedAffineEquation anchor p) = 0 := by
    exact (AlgHom.congr_fun (normalizedAffineEquation_evaluation anchor x hx) p).trans hp
  have hpartial : eval (fun i => x (anchor.succAbove i))
      (pderiv pivot (normalizedAffineEquation anchor p)) ≠ 0 := by
    rwa [normalizedAffineEquation_partial_evaluation anchor x hx]
  have hjet : aeval
      (affineNormalizedSurfaceJetCoordinates (normalizedAffineEquation anchor p)
        (fun i => x (anchor.succAbove i)) pivot)
      (normalizedAffineEquation anchor q) = 0 := by
    exact (AlgHom.congr_fun (normalizedAffineEquation_jet_evaluation anchor x hx p pivot) q).trans hq
  exact affineNormalizedSurfaceJet_zero_mem_square_sup_equation
    (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q)
    (fun i => x (anchor.succAbove i)) pivot hvalue hpartial hjet

/-- Coordinate-one substitution commutes with actual coefficient base change. -/
theorem normalizedAffineEquation_coefficients_map
    {K : Type u} [Field K] (f : K →+* M)
    (anchor : Fin 4) (q : MvPolynomial (Fin 4) K) :
    normalizedAffineEquation anchor (MvPolynomial.map f q) =
      MvPolynomial.map f (normalizedAffineEquation anchor q) := by
  classical
  induction q using MvPolynomial.induction_on with
  | C c => simp [normalizedAffineEquation]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X q j hq =>
      simp only [map_mul]
      rw [hq]
      congr 1
      by_cases hj : j = anchor
      · subst j
        simp [normalizedAffineEquation]
      · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hj
        simp [normalizedAffineEquation]

/-- The base-changed polynomial's actual full jet is exactly the original
ground polynomial's evaluation through the composite coefficient map. -/
theorem normalizedProjectiveJet_baseChange_evaluation
    {K : Type u} [Field K] (f : K →+* M)
    (q : MvPolynomial (Fin 4) K) (p : MvPolynomial (Fin 4) M)
    (anchor : Fin 4) (x : Fin 4 → M) (pivot : Fin 3) :
    aeval (cubicNormalizedSurfacePoint_tangentJet p anchor x pivot)
        (MvPolynomial.map f q) =
      q.eval₂ ((algebraMap M (CubicSurfaceFirstJet M)).comp f)
        (cubicNormalizedSurfacePoint_tangentJet p anchor x pivot) := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]

/-- Ground equations over K evaluated at an actual M-point and its full
normalized jet give the proved affine-square conclusion after coefficient
base change. No supplied coordinate or completeness certificate is used. -/
theorem normalizedProjectiveGroundJet_zero_mem_affine_square_sup_equation
    {K : Type u} [Field K] (f : K →+* M)
    (p q : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3)
    (hp : p.eval₂ f x = 0)
    (hpivot : (pderiv (anchor.succAbove pivot) p).eval₂ f x ≠ 0)
    (hq : q.eval₂ ((algebraMap M (CubicSurfaceFirstJet M)).comp f)
      (cubicNormalizedSurfacePoint_tangentJet (MvPolynomial.map f p) anchor x pivot) = 0) :
    normalizedAffineEquation anchor (MvPolynomial.map f q) ∈
      affinePointIdeal (fun i => x (anchor.succAbove i)) ^ 2 ⊔
        Ideal.span ({normalizedAffineEquation anchor (MvPolynomial.map f p)} :
          Set (MvPolynomial (Fin 3) M)) := by
  apply normalizedProjectiveJet_zero_mem_affine_square_sup_equation
    (MvPolynomial.map f p) (MvPolynomial.map f q) anchor x hx pivot
  · simpa only [MvPolynomial.eval_map] using hp
  · simpa only [MvPolynomial.pderiv_map, MvPolynomial.eval_map] using hpivot
  · simpa only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map] using hq

end PfaffianDescent.Coray
