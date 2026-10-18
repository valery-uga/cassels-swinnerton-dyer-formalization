import AllCharacteristics.TwoTangentSecantPreimage
import AllCharacteristics.TangentHyperplaneGeneric
import AllCharacteristics.CubicLineAlgebra

/-! Actual known-target polynomial exclusions for the
secant lift: mutual tangent separation makes the center polar quadrics
nonzero, and low-degree genericity excludes their zero sets. -/

noncomputable section
namespace PfaffianDescent.Cubic

open MvPolynomial
universe u

variable {K L : Type u} [Field K] [Field L]

theorem eval₂_mixedLinearPolynomial (f : K →+* L)
    (c : Cubic K 4) (p : Vec K 4) (z : Vec L 4) :
    MvPolynomial.eval₂ f z (mixedLinearPolynomial c p) =
      (c.map f).mixed (fun i ↦ f (p i)) z := by
  rw [AllCharacteristics.mixed_map_eq_gradient_dot]
  simp only [mixedLinearPolynomial, linearCoordinatePolynomial,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eval₂_mixedQuadraticPolynomial (f : K →+* L)
    (c : Cubic K 4) (p : Vec K 4) (z : Vec L 4) :
    MvPolynomial.eval₂ f z (mixedQuadraticPolynomial c p) =
      (c.map f).mixed z (fun i ↦ f (p i)) := by
  rw [AllCharacteristics.Cubic.mixed_eq_sum_pderiv_eval]
  simp only [mixedQuadraticPolynomial, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [toMvPolynomial_map, MvPolynomial.pderiv_map, MvPolynomial.eval_map]

/-- The polar at the fixed center `p`, for the plane tangent at `q`, written
as a quadratic polynomial in the target coordinates. -/
def centerPolarPolynomial (c : Cubic K 4) (q p : Vec K 4) :
    MvPolynomial (Fin 4) K :=
  C (c.mixed q p) * mixedQuadraticPolynomial c p -
    mixedLinearPolynomial c q * mixedLinearPolynomial c p

theorem centerPolarPolynomial_homogeneous
    (c : Cubic K 4) (hc : c.toMvPolynomial.IsHomogeneous 3) (q p : Vec K 4) :
    (centerPolarPolynomial c q p).IsHomogeneous 2 := by
  apply IsHomogeneous.sub
  · exact (mixedQuadraticPolynomial_homogeneous c hc p).C_mul _
  · exact (linearCoordinatePolynomial_homogeneous _).mul
      (linearCoordinatePolynomial_homogeneous _)

theorem eval₂_centerPolarPolynomial (f : K →+* L)
    (c : Cubic K 4) (q p : Vec K 4) (z : Vec L 4) :
    MvPolynomial.eval₂ f z (centerPolarPolynomial c q p) =
      secantPolarValue (c.map f)
        (tangentLinear (c.map f) (fun i ↦ f (q i))) z (fun i ↦ f (p i)) := by
  simp only [centerPolarPolynomial, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    eval₂_mixedQuadraticPolynomial, eval₂_mixedLinearPolynomial,
    secantPolarValue, tangentLinear_apply, mixed_map]

/-- The center polar is nonzero for mutually separated tangent centers:
its value at the other center is the square of their tangent coefficient. -/
theorem centerPolarPolynomial_ne_zero
    (c : Cubic K 4) (q p : Vec K 4)
    (hq : c.eval q = 0) (hsep : c.mixed q p ≠ 0) :
    centerPolarPolynomial c q p ≠ 0 := by
  have he : MvPolynomial.aeval q (centerPolarPolynomial c q p) =
      (c.mixed q p) ^ 2 := by
    simp only [centerPolarPolynomial, _root_.map_sub, _root_.map_mul, aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply, eval_mixedQuadraticPolynomial,
      eval_mixedLinearPolynomial, mixed_self_eq_three_eval, hq]
    ring
  intro hzero
  rw [hzero, _root_.map_zero] at he
  exact (pow_ne_zero 2 hsep) he.symm

/-- Exact cone genericity supplies the two center exclusions needed for the
constructed tangent-secants, with no genericity assumption on the unknown
secant preimage. -/
theorem centerPolar_ne_zero_of_lowDegree_genericity
    (f : K →+* L) (c : Cubic K 4) (hc : c.toMvPolynomial.IsHomogeneous 3)
    (q p : Vec K 4) (hq : c.eval q = 0) (hsep : c.mixed q p ≠ 0)
    (z : Vec L 4)
    (hgeneric : ∀ P : MvPolynomial (Fin 4) K,
      P ≠ 0 → P.totalDegree ≤ 2 → MvPolynomial.eval₂ f z P ≠ 0) :
    secantPolarValue (c.map f)
      (tangentLinear (c.map f) (fun i ↦ f (q i))) z (fun i ↦ f (p i)) ≠ 0 := by
  rw [← eval₂_centerPolarPolynomial]
  exact hgeneric _ (centerPolarPolynomial_ne_zero c q p hq hsep)
    (centerPolarPolynomial_homogeneous c hc q p).totalDegree_le

theorem mixedLinearPolynomial_ne_zero_of_mixed_ne_zero
    (c : Cubic K 4) (w d : Vec K 4) (hwd : c.mixed w d ≠ 0) :
    mixedLinearPolynomial c w ≠ 0 := by
  intro hzero
  apply hwd
  rw [← eval_mixedLinearPolynomial, hzero, _root_.map_zero]

/-- A generic target avoids every tangent hyperplane defined over the base
field. The polynomial's nonzero coefficient is constructed from the given
transverse direction. -/
theorem mixed_map_point_generic_ne_zero
    (f : K →+* L) (c : Cubic K 4) (w d : Vec K 4)
    (hwd : c.mixed w d ≠ 0) (z : Vec L 4)
    (hgeneric : ∀ P : MvPolynomial (Fin 4) K,
      P ≠ 0 → P.totalDegree ≤ 2 → MvPolynomial.eval₂ f z P ≠ 0) :
    (c.map f).mixed (fun i ↦ f (w i)) z ≠ 0 := by
  rw [← eval₂_mixedLinearPolynomial]
  exact hgeneric _ (mixedLinearPolynomial_ne_zero_of_mixed_ne_zero c w d hwd)
    ((linearCoordinatePolynomial_homogeneous _).totalDegree_le.trans (by norm_num))

/-- Over an algebraically closed base, every point of a noncontained base
line section after any field extension is a scalar multiple of a base
point. This explicitly descends the root of the cubic line polynomial. -/
theorem exists_base_point_of_mapped_cubic_line_zero
    [IsAlgClosed K]
    (f : K →+* L) (c : Cubic K 4) (a b : Vec K 4)
    (ha : c.eval a ≠ 0) (s t : L)
    (hy : s • (fun i ↦ f (a i)) + t • (fun i ↦ f (b i)) ≠ 0)
    (hcy : (c.map f).eval
      (s • (fun i ↦ f (a i)) + t • (fun i ↦ f (b i))) = 0) :
    ∃ (w : Vec K 4) (r : L),
      w ≠ 0 ∧ c.eval w = 0 ∧ r ≠ 0 ∧
      s • (fun i ↦ f (a i)) + t • (fun i ↦ f (b i)) =
        r • (fun i ↦ f (w i)) := by
  let aL : Vec L 4 := fun i ↦ f (a i)
  let bL : Vec L 4 := fun i ↦ f (b i)
  have haL : (c.map f).eval aL ≠ 0 := by
    rw [Cubic.eval_map]
    exact fun h ↦ ha (f.injective (h.trans (_root_.map_zero f).symm))
  have ht : t ≠ 0 := by
    intro ht0
    have hs : s = 0 := by
      have he : s ^ 3 * (c.map f).eval aL = 0 := by
        simpa only [ht0, zero_smul, add_zero, eval_smul] using hcy
      have hs3 : s ^ 3 = 0 := (mul_eq_zero.mp he).resolve_right haL
      exact eq_zero_of_pow_eq_zero hs3
    apply hy
    simp only [hs, ht0, zero_smul, zero_add]
  let τ : L := s / t
  have hrepr : s • aL + t • bL = t • (τ • aL + bL) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp [τ]
    field_simp [ht]
  have hτ : (c.map f).eval (τ • aL + bL) = 0 := by
    rw [show s • (fun i ↦ f (a i)) + t • (fun i ↦ f (b i)) =
      t • (τ • aL + bL) from hrepr, eval_smul] at hcy
    exact (mul_eq_zero.mp hcy).resolve_left (pow_ne_zero 3 ht)
  let P := AllCharacteristics.cubicLinePolynomial c a b
  have hP0 : P ≠ 0 := by
    intro hzero
    have hdeg := AllCharacteristics.cubicLinePolynomial_natDegree c a b ha
    rw [show AllCharacteristics.cubicLinePolynomial c a b = 0 from hzero] at hdeg
    simpa using hdeg
  have hroot : (P.map f).IsRoot τ := by
    change (P.map f).eval τ = 0
    rw [Polynomial.eval_map]
    exact (AllCharacteristics.cubicLinePolynomial_eval₂ f c a b τ).trans hτ
  obtain ⟨r, hr⟩ := (IsAlgClosed.splits P).mem_range_of_isRoot hP0 hroot
  let w : Vec K 4 := r • a + b
  have hwmap : (fun i ↦ f (w i)) = τ • aL + bL := by
    funext i
    simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      _root_.map_add, _root_.map_mul]
    rw [hr]
  have hcw : c.eval w = 0 := by
    apply f.injective
    rw [_root_.map_zero, ← Cubic.eval_map, hwmap]
    exact hτ
  have hw0 : w ≠ 0 := by
    intro hw
    apply hy
    rw [show s • (fun i ↦ f (a i)) + t • (fun i ↦ f (b i)) =
      t • (τ • aL + bL) from hrepr, ← hwmap, hw]
    funext i
    simp only [Pi.smul_apply, Pi.zero_apply, _root_.map_zero, smul_eq_mul, mul_zero]
  exact ⟨w, t, hw0, hcw, ht, hrepr.trans (congrArg (t • ·) hwmap.symm)⟩

/-- Generic target avoidance of the fixed common line is constructed from
base-field smoothness and the explicit descent of cubic-line roots. -/
theorem mixed_generic_ne_zero_on_mapped_cubic_line
    [IsAlgClosed K]
    (f : K →+* L) (c : Cubic K 4) (a b : Vec K 4)
    (ha : c.eval a ≠ 0)
    (hregular : ∀ w : Vec K 4, w ≠ 0 → c.eval w = 0 →
      ∃ d : Vec K 4, c.mixed w d ≠ 0)
    (z : Vec L 4)
    (hgeneric : ∀ P : MvPolynomial (Fin 4) K,
      P ≠ 0 → P.totalDegree ≤ 2 → MvPolynomial.eval₂ f z P ≠ 0)
    (s t : L)
    (hy : s • (fun i ↦ f (a i)) + t • (fun i ↦ f (b i)) ≠ 0)
    (hcy : (c.map f).eval
      (s • (fun i ↦ f (a i)) + t • (fun i ↦ f (b i))) = 0) :
    (c.map f).mixed
      (s • (fun i ↦ f (a i)) + t • (fun i ↦ f (b i))) z ≠ 0 := by
  obtain ⟨w, r, hw0, hcw, hr, hyw⟩ :=
    exists_base_point_of_mapped_cubic_line_zero f c a b ha s t hy hcy
  obtain ⟨d, hwd⟩ := hregular w hw0 hcw
  rw [hyw, mixed_smul_left]
  exact mul_ne_zero (pow_ne_zero 2 hr)
    (mixed_map_point_generic_ne_zero f c w d hwd z hgeneric)

/-- The complete explicit generic-target secant lift. The low-degree
genericity premise now internally supplies every polar/linear avoidance
condition used in the construction. The remaining geometric inputs are
absence of contained lines and a frame of the fixed common tangent line. -/
theorem exists_two_tangentResidual_secant_preimage_of_lowDegree_genericity
    [IsAlgClosed K] [IsAlgClosed L]
    (f : K →+* L) (c : Cubic K 4) (hc : c.toMvPolynomial.IsHomogeneous 3)
    (p q : Vec K 4) (hp : c.eval p = 0) (hq : c.eval q = 0)
    (hpq : c.mixed p q ≠ 0) (hqp : c.mixed q p ≠ 0)
    (z : Vec L 4) (hz : (c.map f).eval z = 0)
    (hgeneric : ∀ P : MvPolynomial (Fin 4) K,
      P ≠ 0 → P.totalDegree ≤ 2 → MvPolynomial.eval₂ f z P ≠ 0)
    (hnoP : NoContainedLineThrough (c.map f) (fun i ↦ f (p i)))
    (hnoQ : NoContainedLineThrough (c.map f) (fun i ↦ f (q i)))
    (hnoZ : NoContainedLineThrough (c.map f) z)
    (a b : Vec K 4) (ha : c.eval a ≠ 0)
    (hregular : ∀ w : Vec K 4, w ≠ 0 → c.eval w = 0 →
      ∃ d : Vec K 4, c.mixed w d ≠ 0)
    (M : Matrix (Fin 4) (Fin 3) L) (hM : Function.Injective M.mulVec)
    (hVM : ∀ x : Fin 3 → L, (c.map f).mixed (fun i ↦ f (q i)) (M.mulVec x) = 0)
    (hcommon : ∀ x : Fin 3 → L,
      (c.map f).mixed (fun i ↦ f (p i)) (M.mulVec x) = 0 →
      ∃ s t : L, M.mulVec x =
        s • (fun i ↦ f (a i)) + t • (fun i ↦ f (b i))) :
    ∃ (dp dq : Vec L 4) (r : L),
      (c.map f).mixed (fun i ↦ f (p i)) dp = 0 ∧
      (c.map f).mixed (fun i ↦ f (q i)) dq = 0 ∧ r ≠ 0 ∧
      tangentResidualPoint (c.map f) (fun i ↦ f (p i)) dp ≠ 0 ∧
      tangentResidualPoint (c.map f) (fun i ↦ f (q i)) dq ≠ 0 ∧
      secantResidualPoint (c.map f)
        (tangentResidualPoint (c.map f) (fun i ↦ f (p i)) dp)
        (tangentResidualPoint (c.map f) (fun i ↦ f (q i)) dq) = r • z := by
  have hcL : (c.map f).toMvPolynomial.IsHomogeneous 3 := by
    rw [toMvPolynomial_map]
    exact hc.map f
  have hpL : (c.map f).eval (fun i ↦ f (p i)) = 0 := by
    rw [Cubic.eval_map, hp, _root_.map_zero]
  have hqL : (c.map f).eval (fun i ↦ f (q i)) = 0 := by
    rw [Cubic.eval_map, hq, _root_.map_zero]
  apply exists_two_tangentResidual_secant_preimage (c.map f) hcL
    (fun i ↦ f (p i)) (fun i ↦ f (q i)) z hpL hqL hz
    (mixed_map_point_generic_ne_zero f c p q hpq z hgeneric)
    (mixed_map_point_generic_ne_zero f c q p hqp z hgeneric)
    (centerPolar_ne_zero_of_lowDegree_genericity f c hc q p hq hqp z hgeneric)
    (centerPolar_ne_zero_of_lowDegree_genericity f c hc p q hp hpq z hgeneric)
    hnoP hnoQ hnoZ M hM hVM
  intro x hx hcubic hplane
  obtain ⟨s, t, hst⟩ := hcommon x hplane
  have hv0 : M.mulVec x ≠ 0 := by
    intro hzero
    apply hx
    apply hM
    simpa using hzero
  rw [hst] at hv0 hcubic ⊢
  exact mixed_generic_ne_zero_on_mapped_cubic_line f c a b ha hregular
    z hgeneric s t hv0 hcubic

end PfaffianDescent.Cubic
