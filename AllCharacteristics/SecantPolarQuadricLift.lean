import AllCharacteristics.TangentSecantInverseCoordinates
import AllCharacteristics.CubicMultiplicity
import PfaffianDescent.RectangularSubstitution
import PfaffianDescent.CorayPlaneHomogeneousCommonZero

/-! The actual cubic/quadric construction of a secant
preimage. No plane-curve Bezout multiplicity calculation is needed: the
three-variable height theorem constructs a common projective zero directly.
The generic-target avoidance hypotheses are explicit and are not asserted
here to follow from smoothness. -/

noncomputable section

namespace PfaffianDescent.Cubic

open MvPolynomial

section Ring
variable {R : Type*} [CommRing R] {n : ℕ}

/-- The polar quadric controlling a secant preimage in a fixed plane. -/
def secantPolarValue (c : Cubic R n) (U : Vec R n →ₗ[R] R)
    (z v : Vec R n) : R :=
  U v * c.mixed z v - U z * c.mixed v z

/-- Substituting the plane-intersection lift into the cubic gives its polar
quadric times two explicit linear factors. -/
theorem eval_projectionDirection_eq_secantPolarValue
    (c : Cubic R n) (U : Vec R n →ₗ[R] R) (z v : Vec R n)
    (hz : c.eval z = 0) (hv : c.eval v = 0) :
    c.eval (projectionDirection U z v) =
      U z * U v * secantPolarValue c U z v := by
  rw [projectionDirection,
    show U z • v - U v • z = U z • v + (-U v) • z by
      simp only [sub_eq_add_neg, neg_smul], eval_line, hz, hv]
  unfold secantPolarValue
  ring

/-- Exact residual coordinates of the constructed secant, including the
polar-error term before imposing the quadric equation. -/
theorem secantResidualPoint_projectionDirection
    (c : Cubic R n) (U : Vec R n →ₗ[R] R) (z v : Vec R n)
    (hv : c.eval v = 0) :
    secantResidualPoint c (projectionDirection U z v) v =
      (-(U v) * secantPolarValue c U z v) • v +
        ((U v) ^ 2 * c.mixed v z) • z := by
  have hd : projectionDirection U z v = U z • v + (-U v) • z := by
    simp only [projectionDirection, sub_eq_add_neg, neg_smul]
  have hself : c.mixed v v = 0 := by
    rw [mixed_self_eq_three_eval, hv, mul_zero]
  have hright : c.mixed v (projectionDirection U z v) =
      -(U v) * c.mixed v z := by
    rw [hd, mixed_add_right, mixed_smul_right, mixed_smul_right, hself]
    ring
  have hleft : c.mixed (projectionDirection U z v) v =
      -2 * U z * U v * c.mixed v z + (U v) ^ 2 * c.mixed z v := by
    rw [show projectionDirection U z v = (-U v) • z + U z • v by
      simp only [projectionDirection, sub_eq_add_neg, neg_smul, add_comm],
      mixed_linearCombination_point c v z (-U v) (U z), hself]
    ring
  change c.mixed v (projectionDirection U z v) • projectionDirection U z v -
    c.mixed (projectionDirection U z v) v • v = _
  rw [hright, hleft]
  funext i
  simp only [projectionDirection,
    secantPolarValue, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem secantResidualPoint_projectionDirection_of_polar_zero
    (c : Cubic R n) (U : Vec R n →ₗ[R] R) (z v : Vec R n)
    (hv : c.eval v = 0) (hQ : secantPolarValue c U z v = 0) :
    secantResidualPoint c (projectionDirection U z v) v =
      ((U v) ^ 2 * c.mixed v z) • z := by
  rw [secantResidualPoint_projectionDirection c U z v hv, hQ,
    mul_zero, zero_smul, zero_add]

end Ring

section Polynomials
variable {K : Type*} [Field K]

/-- A linear coordinate form, viewed as a linear map on vectors. -/
def coordinateLinearMap (a : Fin 4 → K) : Vec K 4 →ₗ[K] K where
  toFun x := ∑ i, a i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

def linearCoordinatePolynomial (a : Fin 4 → K) : MvPolynomial (Fin 4) K :=
  ∑ i, C (a i) * X i

theorem linearCoordinatePolynomial_homogeneous (a : Fin 4 → K) :
    (linearCoordinatePolynomial a).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

theorem eval_linearCoordinatePolynomial (a x : Fin 4 → K) :
    MvPolynomial.aeval x (linearCoordinatePolynomial a) = coordinateLinearMap a x := by
  simp [linearCoordinatePolynomial, coordinateLinearMap]

def mixedLinearPolynomial (c : Cubic K 4) (z : Vec K 4) :
    MvPolynomial (Fin 4) K :=
  linearCoordinatePolynomial (fun i ↦ (pderiv i c.toMvPolynomial).eval z)

theorem eval_mixedLinearPolynomial (c : Cubic K 4) (z x : Vec K 4) :
    MvPolynomial.aeval x (mixedLinearPolynomial c z) = c.mixed z x := by
  rw [mixedLinearPolynomial, eval_linearCoordinatePolynomial,
    AllCharacteristics.Cubic.mixed_eq_sum_pderiv_eval]
  change (∑ i, (pderiv i c.toMvPolynomial).eval z * x i) =
    ∑ i, x i * (pderiv i c.toMvPolynomial).eval z
  apply Finset.sum_congr rfl
  intro i _
  ring

def mixedQuadraticPolynomial (c : Cubic K 4) (z : Vec K 4) :
    MvPolynomial (Fin 4) K :=
  ∑ i, C (z i) * pderiv i c.toMvPolynomial

theorem mixedQuadraticPolynomial_homogeneous
    (c : Cubic K 4) (hc : c.toMvPolynomial.IsHomogeneous 3) (z : Vec K 4) :
    (mixedQuadraticPolynomial c z).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  exact (show (pderiv i c.toMvPolynomial).IsHomogeneous 2 by
    simpa using hc.pderiv).C_mul _

theorem eval_mixedQuadraticPolynomial (c : Cubic K 4) (z x : Vec K 4) :
    MvPolynomial.aeval x (mixedQuadraticPolynomial c z) = c.mixed x z := by
  rw [AllCharacteristics.Cubic.mixed_eq_sum_pderiv_eval]
  simp only [mixedQuadraticPolynomial, _root_.map_sum, _root_.map_mul, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply, aeval_def,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_id, MvPolynomial.eval_C]

def secantPolarPolynomial (c : Cubic K 4) (a : Fin 4 → K) (z : Vec K 4) :
    MvPolynomial (Fin 4) K :=
  linearCoordinatePolynomial a * mixedLinearPolynomial c z -
    C (coordinateLinearMap a z) * mixedQuadraticPolynomial c z

theorem secantPolarPolynomial_homogeneous
    (c : Cubic K 4) (hc : c.toMvPolynomial.IsHomogeneous 3)
    (a : Fin 4 → K) (z : Vec K 4) :
    (secantPolarPolynomial c a z).IsHomogeneous 2 := by
  apply IsHomogeneous.sub
  · exact (linearCoordinatePolynomial_homogeneous a).mul
      (linearCoordinatePolynomial_homogeneous _)
  · exact (mixedQuadraticPolynomial_homogeneous c hc z).C_mul _

theorem eval_secantPolarPolynomial (c : Cubic K 4) (a : Fin 4 → K)
    (z x : Vec K 4) :
    MvPolynomial.aeval x (secantPolarPolynomial c a z) =
      secantPolarValue c (coordinateLinearMap a) z x := by
  simp only [secantPolarPolynomial, _root_.map_sub, _root_.map_mul,
    eval_linearCoordinatePolynomial, eval_mixedLinearPolynomial,
    eval_mixedQuadraticPolynomial, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply, secantPolarValue]

theorem rectangularSubstitution_aeval_three
    (M : Matrix (Fin 4) (Fin 3) K) (x : Fin 3 → K)
    (f : MvPolynomial (Fin 4) K) :
    MvPolynomial.aeval x (rectangularSubstitution M f) =
      MvPolynomial.aeval (M.mulVec x) f := by
  have h : (MvPolynomial.aeval x).comp (rectangularSubstitution M) =
      MvPolynomial.aeval (M.mulVec x) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, rectangularSubstitution_X, aeval_X]
    have he := eval₂_rectangularLinearCoordinate M i (RingHom.id K) x
    have hMid : M.map (RingHom.id K) = M := by
      ext i j
      rfl
    rw [hMid] at he
    simpa only [aeval_def, Algebra.algebraMap_self] using he
  exact AlgHom.congr_fun h f

/-- Construct a cubic point of the second plane satisfying the secant polar
quadric. The three-variable height theorem provides the point; avoidance of
the fixed common line places it in the domain of the projection inverse. -/
theorem exists_plane_cubic_polar_zero_avoiding_common_line
    [IsAlgClosed K]
    (c : Cubic K 4) (hc : c.toMvPolynomial.IsHomogeneous 3)
    (a : Fin 4 → K) (z : Vec K 4)
    (M : Matrix (Fin 4) (Fin 3) K)
    (hM : Function.Injective M.mulVec)
    (hUz : coordinateLinearMap a z ≠ 0)
    (havoid : ∀ x : Fin 3 → K, x ≠ 0 → c.eval (M.mulVec x) = 0 →
      coordinateLinearMap a (M.mulVec x) = 0 → c.mixed (M.mulVec x) z ≠ 0) :
    ∃ x : Fin 3 → K, x ≠ 0 ∧ M.mulVec x ≠ 0 ∧
      c.eval (M.mulVec x) = 0 ∧
      secantPolarValue c (coordinateLinearMap a) z (M.mulVec x) = 0 ∧
      coordinateLinearMap a (M.mulVec x) ≠ 0 := by
  obtain ⟨x, hx, hcx, hQx⟩ :=
    Coray.plane_exists_nonzero_common_zero_of_homogeneous_pos
      (rectangularSubstitution M c.toMvPolynomial)
      (rectangularSubstitution M (secantPolarPolynomial c a z))
      (rectangularSubstitution_homogeneous M hc)
      (rectangularSubstitution_homogeneous M (secantPolarPolynomial_homogeneous c hc a z))
      (by norm_num) (by norm_num)
  rw [rectangularSubstitution_aeval_three] at hcx hQx
  have hcEval : c.eval (M.mulVec x) = 0 := by
    simpa only [aeval_def, Algebra.algebraMap_self, eval_toMvPolynomial,
      show c.map (RingHom.id K) = c by rfl] using hcx
  rw [eval_secantPolarPolynomial] at hQx
  have hv0 : M.mulVec x ≠ 0 := by
    intro hv
    apply hx
    apply hM
    simpa using hv
  refine ⟨x, hx, hv0, hcEval, hQx, ?_⟩
  intro hUv
  have hmix := havoid x hx hcEval hUv
  have hprod : coordinateLinearMap a z * c.mixed (M.mulVec x) z = 0 := by
    simpa only [secantPolarValue, hUv, zero_mul, zero_sub, neg_eq_zero] using hQx
  exact (mul_ne_zero hUz hmix) hprod

/-- A geometric point is free of contained lines when each independent
direction has a nonzero cubic restriction somewhere on its joining line. -/
def NoContainedLineThrough (c : Cubic K 4) (z : Vec K 4) : Prop :=
  ∀ v : Vec K 4, LinearIndependent K ![z, v] →
    ∃ s t : K, c.eval (s • z + t • v) ≠ 0

/-- The cubic/quadric intersection constructs an actual secant preimage of
`z`, with nonzero projective residual scalar. Here `M` parametrizes the
second plane and `a` defines the first. The only avoidance hypothesis is on
their fixed common line, rather than on the unknown preimage. -/
theorem exists_secant_preimage_of_plane_polar_intersection
    [IsAlgClosed K]
    (c : Cubic K 4) (hc : c.toMvPolynomial.IsHomogeneous 3)
    (a : Fin 4 → K) (V : Vec K 4 →ₗ[K] K) (z : Vec K 4)
    (hz : c.eval z = 0) (hVz : V z ≠ 0)
    (M : Matrix (Fin 4) (Fin 3) K)
    (hM : Function.Injective M.mulVec)
    (hVM : ∀ x : Fin 3 → K, V (M.mulVec x) = 0)
    (hUz : coordinateLinearMap a z ≠ 0)
    (havoid : ∀ x : Fin 3 → K, x ≠ 0 → c.eval (M.mulVec x) = 0 →
      coordinateLinearMap a (M.mulVec x) = 0 → c.mixed (M.mulVec x) z ≠ 0)
    (hnoLine : NoContainedLineThrough c z) :
    ∃ (u v : Vec K 4) (r : K),
      u ≠ 0 ∧ v ≠ 0 ∧ c.eval u = 0 ∧ c.eval v = 0 ∧
      coordinateLinearMap a u = 0 ∧ V v = 0 ∧
      coordinateLinearMap a v ≠ 0 ∧ V u ≠ 0 ∧ r ≠ 0 ∧
      secantResidualPoint c u v = r • z := by
  obtain ⟨x, hx, hv0, hv, hQ, hUv⟩ :=
    exists_plane_cubic_polar_zero_avoiding_common_line c hc a z M hM hUz havoid
  let U := coordinateLinearMap a
  let v : Vec K 4 := M.mulVec x
  let u : Vec K 4 := projectionDirection U z v
  change secantPolarValue c U z v = 0 at hQ
  change U v ≠ 0 at hUv
  change c.eval v = 0 at hv
  have hVv : V v = 0 := hVM x
  have hVu : V u = -(U v) * V z := by
    simp only [u, projectionDirection, V.map_sub, V.map_smul, hVv,
      smul_eq_mul, mul_zero, zero_sub, neg_mul]
  have hVu0 : V u ≠ 0 := by
    rw [hVu]
    exact mul_ne_zero (neg_ne_zero.mpr hUv) hVz
  have hu0 : u ≠ 0 := by
    intro hu
    exact hVu0 (by rw [hu, V.map_zero])
  have hu : c.eval u = 0 := by
    change c.eval (projectionDirection U z v) = 0
    rw [eval_projectionDirection_eq_secantPolarValue c U z v hz hv, hQ,
      mul_zero]
  have hind : LinearIndependent K ![z, v] := by
    rw [linearIndependent_fin2]
    refine ⟨hv0, ?_⟩
    intro b hb
    change b • v = z at hb
    apply hVz
    rw [← hb, V.map_smul, hVv, smul_zero]
  have hmix : c.mixed v z ≠ 0 := by
    intro hm
    have hm' : c.mixed z v = 0 := by
      have hprod : U v * c.mixed z v = 0 := by
        simpa only [secantPolarValue, hm, mul_zero, sub_zero] using hQ
      exact (mul_eq_zero.mp hprod).resolve_left hUv
    obtain ⟨s, t, hst⟩ := hnoLine v hind
    apply hst
    rw [eval_line, hz, hv, hm, hm']
    ring
  refine ⟨u, v, (U v) ^ 2 * c.mixed v z, hu0, hv0, hu, hv,
    ?_, hVv, hUv, hVu0, mul_ne_zero (pow_ne_zero 2 hUv) hmix, ?_⟩
  · exact projectionDirection_mem_ker U z v
  · exact secantResidualPoint_projectionDirection_of_polar_zero c U z v hv hQ

end Polynomials
end PfaffianDescent.Cubic
