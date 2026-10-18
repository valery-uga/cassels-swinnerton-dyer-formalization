import AllCharacteristics.GenericSecantPolarAvoidance
import AllCharacteristics.TangentPlaneCommonLineNoncontainment
import AllCharacteristics.SmoothCubicGenericNoContainedLine

/-! The final frame-free geometric secant interface.
The common tangent line, its noncubic first point, all scalar-extension
spanning data, and the second tangent plane parametrization are constructed
internally from smoothness and tangent separation. -/

noncomputable section
namespace AllCharacteristics

open PfaffianDescent MvPolynomial AlgebraicGeometry HomogeneousProjective
universe u

/-- Geometric absence of contained lines, expressed over all coefficient
fields so it can be used both before and after the generic-target extension. -/
def GeometricallyNoContainedLineThrough
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K) : Prop :=
  ∀ (M : Type u) [Field M] (g : K →+* M),
    PfaffianDescent.Cubic.NoContainedLineThrough (c.map g) (fun i ↦ g (p i))

/-- Two separated centers on a smooth cubic, geometrically free of contained
lines, give an actual two-tangent secant preimage of every sufficiently
generic cubic target. No frame, tangent-section irreducibility, curve
intersection, or preimage-existence certificate is a hypothesis. -/
theorem exists_two_tangent_secant_preimage_of_smooth_generic_target
    {K L : Type u} [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]
    (f : K →+* L) (c : Cubic K 4) (hc : c.toMvPolynomial.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hc)]
    (p q : Fin 4 → K) (hp : c.eval p = 0) (hq : c.eval q = 0)
    (hpq : c.mixed p q ≠ 0) (hqp : c.mixed q p ≠ 0)
    (hnoP : GeometricallyNoContainedLineThrough c p)
    (hnoQ : GeometricallyNoContainedLineThrough c q)
    (z : Fin 4 → L) (hz : (c.map f).eval z = 0)
    (hgeneric : ∀ P : MvPolynomial (Fin 4) K,
      P ≠ 0 → P.totalDegree ≤ 2 → MvPolynomial.eval₂ f z P ≠ 0)
    (hnoZ : PfaffianDescent.Cubic.NoContainedLineThrough (c.map f) z) :
    ∃ (dp dq : Fin 4 → L) (r : L),
      (c.map f).mixed (fun i ↦ f (p i)) dp = 0 ∧
      (c.map f).mixed (fun i ↦ f (q i)) dq = 0 ∧ r ≠ 0 ∧
      PfaffianDescent.Cubic.tangentResidualPoint (c.map f) (fun i ↦ f (p i)) dp ≠ 0 ∧
      PfaffianDescent.Cubic.tangentResidualPoint (c.map f) (fun i ↦ f (q i)) dq ≠ 0 ∧
      PfaffianDescent.Cubic.secantResidualPoint (c.map f)
        (PfaffianDescent.Cubic.tangentResidualPoint (c.map f) (fun i ↦ f (p i)) dp)
        (PfaffianDescent.Cubic.tangentResidualPoint (c.map f) (fun i ↦ f (q i)) dq) =
          r • z := by
  classical
  let g : Fin 4 → K := fun i ↦ (MvPolynomial.pderiv i c.toMvPolynomial).eval p
  let h : Fin 4 → K := fun i ↦ (MvPolynomial.pderiv i c.toMvPolynomial).eval q
  have hU : PfaffianDescent.Cubic.coordinateLinearMap g =
      PfaffianDescent.Cubic.tangentLinear c p :=
    PfaffianDescent.Cubic.coordinateLinearMap_tangentCoordinateCoefficients c p
  have hV : PfaffianDescent.Cubic.coordinateLinearMap h =
      PfaffianDescent.Cubic.tangentLinear c q :=
    PfaffianDescent.Cubic.coordinateLinearMap_tangentCoordinateCoefficients c q
  obtain ⟨kp, hkp⟩ : ∃ k : Fin 4, g k ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hpq
    rw [AllCharacteristics.Cubic.mixed_eq_sum_pderiv_eval]
    simp only [show ∀ i, (MvPolynomial.pderiv i c.toMvPolynomial).eval p = 0 from hn,
      mul_zero, Finset.sum_const_zero]
  obtain ⟨kq, hkq⟩ : ∃ k : Fin 4, h k ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hqp
    rw [AllCharacteristics.Cubic.mixed_eq_sum_pderiv_eval]
    simp only [show ∀ i, (MvPolynomial.pderiv i c.toMvPolynomial).eval q = 0 from hn,
      mul_zero, Finset.sum_const_zero]
  have hId : c.map (RingHom.id K) = c := by funext i; rfl
  have hnoP0 : PfaffianDescent.Cubic.NoContainedLineThrough c p := by
    simpa only [hId, RingHom.id_apply] using hnoP K (RingHom.id K)
  let R := coordinatePairMatrix g h
  have hR : Function.Surjective R.mulVec := by
    apply coordinatePairMatrix_mulVec_surjective g h p q
    · rw [hU, PfaffianDescent.Cubic.tangentLinear_apply,
        PfaffianDescent.Cubic.mixed_self_eq_three_eval, hp, mul_zero]
    · rw [hV, PfaffianDescent.Cubic.tangentLinear_apply,
        PfaffianDescent.Cubic.mixed_self_eq_three_eval, hq, mul_zero]
    · simpa only [hU, PfaffianDescent.Cubic.tangentLinear_apply] using hpq
    · simpa only [hV, PfaffianDescent.Cubic.tangentLinear_apply] using hqp
  obtain ⟨A, B, S, hBA, hRA, hRS⟩ := exists_split_kernel_frame_of_surjective_pair R hR
  have hrest : rectangularSubstitution A c.toMvPolynomial ≠ 0 :=
    common_tangent_split_frame_cubic_restriction_ne_zero c hc p q hp kp hkp hqp hnoP0
      A B S hBA hRA hRS
  obtain ⟨A', B', hBA', hRA', hfirst⟩ :=
    exists_split_common_line_frame_with_noncubic_first_column R A B S hBA hRA hRS c hrest
  let a : Fin 4 → K := fun i ↦ A' i 0
  let b : Fin 4 → K := fun i ↦ A' i 1
  have hF0 : c.toMvPolynomial ≠ 0 := by
    intro hzero
    apply hkp
    dsimp only [g]
    rw [hzero]
    simp
  have hregular : ∀ w : Fin 4 → K, w ≠ 0 → c.eval w = 0 →
      ∃ d : Fin 4 → K, c.mixed w d ≠ 0 := by
    intro w hw0 hw
    have he : (c.map (RingHom.id K)).eval w = 0 := by rw [hId]; exact hw
    obtain ⟨d, hd⟩ := smoothCubic_geometrically_nonsingular_mixed
      c.toMvPolynomial hc hF0 c rfl K (RingHom.id K) w hw0 he
    exact ⟨d, by simpa only [hId] using hd⟩
  let M0 := hyperplaneInclusion h kq
  let N0 := coordinateOmission (K := K) kq
  let M := M0.map f
  have hNM : N0 * M0 = 1 := hyperplaneInclusion_leftInverse h kq
  have hNML : N0.map f * M = 1 := by
    change N0.map f * M0.map f = 1
    rw [← Matrix.map_mul, hNM]
    simp
  have hM : Function.Injective M.mulVec := by
    intro x y hxy
    have he := congrArg (N0.map f).mulVec hxy
    simpa only [Matrix.mulVec_mulVec, hNML, Matrix.one_mulVec] using he
  have hVM : ∀ x : Fin 3 → L,
      (c.map f).mixed (fun i ↦ f (q i)) (M.mulVec x) = 0 := by
    intro x
    exact mixed_hyperplaneInclusion_zero f c q h (fun _ ↦ rfl) kq hkq x
  have hpair (w : Fin 4 → L) : (R.map f).mulVec w =
      ![(c.map f).mixed (fun i ↦ f (p i)) w,
        (c.map f).mixed (fun i ↦ f (q i)) w] := by
    funext i
    by_cases hi : i = 0
    · subst i
      change (∑ j, f ((MvPolynomial.pderiv j c.toMvPolynomial).eval p) * w j) =
        (c.map f).mixed (fun i ↦ f (p i)) w
      rw [mixed_map_eq_gradient_dot]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · have hi1 : i = 1 := by omega
      subst i
      change (∑ j, f ((MvPolynomial.pderiv j c.toMvPolynomial).eval q) * w j) =
        (c.map f).mixed (fun i ↦ f (q i)) w
      rw [mixed_map_eq_gradient_dot]
      apply Finset.sum_congr rfl
      intro j _
      ring
  have hcommon : ∀ x : Fin 3 → L,
      (c.map f).mixed (fun i ↦ f (p i)) (M.mulVec x) = 0 →
      ∃ s t : L, M.mulVec x =
        s • (fun i ↦ f (a i)) + t • (fun i ↦ f (b i)) := by
    intro x hpx
    have hker : (R.map f).mulVec (M.mulVec x) = 0 := by
      rw [hpair]
      funext i
      fin_cases i
      · change (c.map f).mixed (fun i ↦ f (p i)) (M.mulVec x) = 0
        exact hpx
      · change (c.map f).mixed (fun i ↦ f (q i)) (M.mulVec x) = 0
        exact hVM x
    exact mapped_kernel_frame_spans f R A' B' S hBA' hRA' hRS (M.mulVec x) hker
  exact PfaffianDescent.Cubic.exists_two_tangentResidual_secant_preimage_of_lowDegree_genericity
    f c hc p q hp hq hpq hqp z hz hgeneric (hnoP L f) (hnoQ L f) hnoZ
    a b hfirst hregular M hM hVM hcommon

end AllCharacteristics
