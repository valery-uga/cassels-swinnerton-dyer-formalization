import AllCharacteristics.CubicLineGraphChart
import AllCharacteristics.TangentHyperplaneGeneric
import AllCharacteristics.KollarSmoothPartialNonzero

/-! The scheme-smoothness bridge for actual generic
line exclusion. All field-valued nonsingularity conditions used by the graph
rigidity proof are constructed from smoothness of the original nonzero cubic.
-/

noncomputable section
namespace AllCharacteristics

open AlgebraicGeometry PfaffianDescent MvPolynomial HomogeneousProjective
universe u

/-- Scheme smoothness of a nonzero cubic implies geometric nonsingularity
of its actual tensor evaluation over EVERY field homomorphism. -/
theorem smoothCubic_geometrically_nonsingular_mixed
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∀ (M : Type u) [Field M] (f : K →+* M) (x : Fin 4 → M),
      x ≠ 0 → (c.map f).eval x = 0 → ∃ d, (c.map f).mixed x d ≠ 0 := by
  intro M _ f x hx hcx
  have hFM : F.map f ≠ 0 := by
    intro hzero
    apply hF0
    exact MvPolynomial.map_injective f f.injective (by simpa using hzero)
  letI : Smooth (hypersurfaceToBase (F.map f) (hF.map f)) :=
    smooth_hypersurfaceToBase_map f F hF
  have hpoly : (F.map f).eval x = 0 := by
    rw [← hc, ← Cubic.toMvPolynomial_map]
    change MvPolynomial.eval₂ (RingHom.id M) x (c.map f).toMvPolynomial = 0
    rw [Cubic.eval_toMvPolynomial]
    have hid : (c.map f).map (RingHom.id M) = c.map f := by funext j; rfl
    rw [hid]
    exact hcx
  by_contra h
  push Not at h
  have hgrad : ∀ i : Fin 4, (MvPolynomial.pderiv i (F.map f)).eval x = 0 := by
    intro i
    have hi := h (Pi.single i 1)
    rw [Cubic.mixed_eq_sum_pderiv_eval] at hi
    have heq : (c.map f).toMvPolynomial = F.map f := by rw [Cubic.toMvPolynomial_map, hc]
    simpa [heq, Pi.single_apply] using hi
  obtain ⟨z⟩ := nonempty_cubicJacobianScheme_of_nonzero_singular_vector
    (F.map f) (hF.map f) x hx hpoly hgrad
  letI := smoothCubic_cubicJacobianScheme_isEmpty (F.map f) (hF.map f) hFM
  exact isEmptyElim z

/-- The genuine generic no-contained-line theorem for a smooth cubic surface
over an algebraically closed ground field. The generic coordinate condition
is algebraic linear independence, supplied by the actual principal-kernel
construction, rather than a desired geometric property of the tangent cut. -/
theorem smoothCubic_generic_no_contained_line_through
    {K L : Type u} [Field K] [Field L] [IsAlgClosed K] [Algebra K L]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)]
    (x : Fin 4 → L) (hx : LinearIndependent K x) :
    ∀ d : Fin 4 → L, LinearIndependent L ![x, d] →
      ∃ s t : L, (c.map (algebraMap K L)).eval (s • x + t • d) ≠ 0 := by
  exact cubicGeneric_no_contained_line_through c x hx
    (smoothCubic_geometrically_nonsingular_mixed F hF hF0 c hc)

end AllCharacteristics
