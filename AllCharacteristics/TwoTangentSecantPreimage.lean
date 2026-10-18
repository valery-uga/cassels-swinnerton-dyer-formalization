import AllCharacteristics.SecantPolarQuadricLift

/-! Construct tangent directions whose residual secant
is the prescribed generic target. All avoidance hypotheses concern the
fixed centers/target or the fixed common line, never an unknown preimage. -/

noncomputable section
namespace PfaffianDescent.Cubic

section Ring
variable {R : Type*} [CommRing R] {n : ℕ}

theorem mixed_smul_left (c : Cubic R n) (p d : Vec R n) (a : R) :
    c.mixed (a • p) d = a ^ 2 * c.mixed p d := by
  simp only [mixed, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem secantPolarValue_smul_right
    (c : Cubic R n) (U : Vec R n →ₗ[R] R) (z v : Vec R n) (a : R) :
    secantPolarValue c U z (a • v) = a ^ 2 * secantPolarValue c U z v := by
  simp only [secantPolarValue, U.map_smul, mixed_smul_right, mixed_smul_left,
    smul_eq_mul]
  ring

theorem secantResidualPoint_smul_pair
    (c : Cubic R n) (u v : Vec R n) (a b : R) :
    secantResidualPoint c (a • u) (b • v) =
      (a ^ 2 * b ^ 2) • secantResidualPoint c u v := by
  funext i
  simp only [secantResidualPoint, mixed_smul_left, mixed_smul_right,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem projectionDirection_smul_left
    (V : Vec R n →ₗ[R] R) (z u : Vec R n) (r : R) :
    projectionDirection V (r • z) u = r • projectionDirection V z u := by
  funext i
  simp only [projectionDirection, V.map_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem projectionDirection_swap
    (V : Vec R n →ₗ[R] R) (z u : Vec R n) :
    projectionDirection V z u = -projectionDirection V u z := by
  funext i
  simp only [projectionDirection, Pi.sub_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

end Ring

section Field
variable {K : Type*} [Field K]

/-- Reversing the plane-intersection construction also satisfies its polar
quadric. This excludes either tangency center by a known-target condition. -/
theorem secantPolarValue_zero_of_secantResidual_eq_smul
    (c : Cubic K 4) (V : Vec K 4 →ₗ[K] K) (z u v : Vec K 4) (r : K)
    (hu : c.eval u = 0) (hv : c.eval v = 0) (hz : c.eval z = 0)
    (hVv : V v = 0) (hVu : V u ≠ 0) (hVz : V z ≠ 0) (hr : r ≠ 0)
    (hsec : secantResidualPoint c u v = r • z) :
    secantPolarValue c V z u = 0 := by
  have hproj : r • projectionDirection V z u =
      (V u * c.mixed u v) • v := by
    rw [← projectionDirection_smul_left, ← hsec, projectionDirection_swap,
      projectionDirection_secantResidualPoint c V u v hVv]
    simp only [neg_smul, neg_mul, neg_neg]
  have heval : c.eval (projectionDirection V z u) = 0 := by
    have he := congrArg c.eval hproj
    rw [eval_smul, eval_smul, hv, mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 3 hr)
  rw [eval_projectionDirection_eq_secantPolarValue c V z u hz hu] at heval
  exact (mul_eq_zero.mp heval).resolve_left (mul_ne_zero hVz hVu)

def tangentCoordinateCoefficients (c : Cubic K 4) (p : Vec K 4) : Fin 4 → K :=
  fun i ↦ (MvPolynomial.pderiv i c.toMvPolynomial).eval p

theorem coordinateLinearMap_tangentCoordinateCoefficients
    (c : Cubic K 4) (p : Vec K 4) :
    coordinateLinearMap (tangentCoordinateCoefficients c p) = tangentLinear c p := by
  apply LinearMap.ext
  intro x
  rw [tangentLinear_apply, AllCharacteristics.Cubic.mixed_eq_sum_pderiv_eval]
  change (∑ i, (MvPolynomial.pderiv i c.toMvPolynomial).eval p * x i) =
    ∑ i, x i * (MvPolynomial.pderiv i c.toMvPolynomial).eval p
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Actual two-tangent secant preimages. The polynomial nonvanishing
conditions are precisely those supplied by a generic target of an integral
cubic: two tangent linear forms, two center polar quadrics, and the tangent
linear forms at the finitely many points of the common plane line. -/
theorem exists_two_tangentResidual_secant_preimage
    [IsAlgClosed K]
    (c : Cubic K 4) (hc : c.toMvPolynomial.IsHomogeneous 3)
    (p q z : Vec K 4)
    (hp : c.eval p = 0) (hq : c.eval q = 0) (hz : c.eval z = 0)
    (hUz : c.mixed p z ≠ 0) (hVz : c.mixed q z ≠ 0)
    (hcenterP : secantPolarValue c (tangentLinear c q) z p ≠ 0)
    (hcenterQ : secantPolarValue c (tangentLinear c p) z q ≠ 0)
    (hnoP : NoContainedLineThrough c p)
    (hnoQ : NoContainedLineThrough c q)
    (hnoZ : NoContainedLineThrough c z)
    (M : Matrix (Fin 4) (Fin 3) K)
    (hM : Function.Injective M.mulVec)
    (hVM : ∀ x : Fin 3 → K, c.mixed q (M.mulVec x) = 0)
    (havoid : ∀ x : Fin 3 → K, x ≠ 0 → c.eval (M.mulVec x) = 0 →
      c.mixed p (M.mulVec x) = 0 → c.mixed (M.mulVec x) z ≠ 0) :
    ∃ (dp dq : Vec K 4) (r : K),
      c.mixed p dp = 0 ∧ c.mixed q dq = 0 ∧ r ≠ 0 ∧
      tangentResidualPoint c p dp ≠ 0 ∧ tangentResidualPoint c q dq ≠ 0 ∧
      secantResidualPoint c (tangentResidualPoint c p dp)
        (tangentResidualPoint c q dq) = r • z := by
  let a := tangentCoordinateCoefficients c p
  have hU : coordinateLinearMap a = tangentLinear c p :=
    coordinateLinearMap_tangentCoordinateCoefficients c p
  obtain ⟨u, v, r, hu0, hv0, hu, hv, hUu, hVv, hUv, hVu, hr, hsec⟩ :=
    exists_secant_preimage_of_plane_polar_intersection c hc a (tangentLinear c q) z
      hz hVz M hM hVM (by simpa only [hU, tangentLinear_apply] using hUz)
      (by simpa only [hU, tangentLinear_apply] using havoid) hnoZ
  rw [hU] at hUu hUv
  change c.mixed p u = 0 at hUu
  change c.mixed p v ≠ 0 at hUv
  change c.mixed q v = 0 at hVv
  change c.mixed q u ≠ 0 at hVu
  have hpolarV : secantPolarValue c (tangentLinear c q) z u = 0 :=
    secantPolarValue_zero_of_secantResidual_eq_smul c (tangentLinear c q)
      z u v r hu hv hz hVv hVu hVz hr hsec
  have hpolarU : secantPolarValue c (tangentLinear c p) z v = 0 := by
    apply secantPolarValue_zero_of_secantResidual_eq_smul c (tangentLinear c p)
      z v u (-r) hv hu hz hUu hUv hUz (neg_ne_zero.mpr hr)
    rw [secantResidualPoint_swap, hsec, neg_smul]
  have hindP : LinearIndependent K ![p, u] := by
    rw [linearIndependent_fin2]
    refine ⟨hu0, ?_⟩
    intro b hb
    change b • u = p at hb
    apply hcenterP
    rw [← hb, secantPolarValue_smul_right, hpolarV, mul_zero]
  have hindQ : LinearIndependent K ![q, v] := by
    rw [linearIndependent_fin2]
    refine ⟨hv0, ?_⟩
    intro b hb
    change b • v = q at hb
    apply hcenterQ
    rw [← hb, secantPolarValue_smul_right, hpolarU, mul_zero]
  have hmp : c.mixed u p ≠ 0 := by
    intro hm
    obtain ⟨s, t, hst⟩ := hnoP u hindP
    exact hst ((mixed_reverse_eq_zero_iff_line_contained c p u hp hu hUu).mp hm s t)
  have hmq : c.mixed v q ≠ 0 := by
    intro hm
    obtain ⟨s, t, hst⟩ := hnoQ v hindQ
    exact hst ((mixed_reverse_eq_zero_iff_line_contained c q v hq hv hVv).mp hm s t)
  refine ⟨u, v, ((-c.mixed u p) ^ 2 * (-c.mixed v q) ^ 2) * r,
    hUu, hVv, ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (neg_ne_zero.mpr hmp))
      (pow_ne_zero 2 (neg_ne_zero.mpr hmq))) hr
  · rw [tangentResidualPoint_of_eval_zero c p u hu]
    exact smul_ne_zero (neg_ne_zero.mpr hmp) hu0
  · rw [tangentResidualPoint_of_eval_zero c q v hv]
    exact smul_ne_zero (neg_ne_zero.mpr hmq) hv0
  · rw [tangentResidualPoint_of_eval_zero c p u hu,
      tangentResidualPoint_of_eval_zero c q v hv,
      secantResidualPoint_smul_pair, hsec, smul_smul]

end Field
end PfaffianDescent.Cubic
