import AllCharacteristics.FiniteExtensionFieldDescent
import AllCharacteristics.SmoothEquationFieldDescent

/-!
# Descending a smooth hypersurface and a finite-field point together

The finite-extension model includes all point coordinates and all equation
coefficients. The same finitely generated subfield therefore supports a
nonzero smooth homogeneous equation and a point over an extension of exactly
the original degree, with compatible embeddings into the original fields.
-/

open AlgebraicGeometry
namespace AllCharacteristics
open HomogeneousProjective
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
variable {σ : Type} [Finite σ]

/-- A smooth homogeneous equation and its point over a finite extension
descend together to a finitely generated subfield, preserving the full
extension degree and the original coordinates under the specified embedding. -/
theorem exists_fg_subfield_smooth_point_model
    (p : MvPolynomial σ k) {d : ℕ} (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (x : σ → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0) :
    ∃ F : Subfield k, Field.FG F ∧
      ∃ q : MvPolynomial σ F, ∃ hq : q.IsHomogeneous d,
        q.map F.subtype = p ∧ q ≠ 0 ∧ Smooth (hypersurfaceToBase q hq) ∧
        ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : Module.Finite F E)
          (c : E →+* L),
          Module.finrank F E = Module.finrank k L ∧
          (∀ a : F, c (algebraMap F E a) = algebraMap k L a.1) ∧
          ∃ y : σ → E, y ≠ 0 ∧ q.eval₂ (algebraMap F E) y = 0 ∧
            ∀ i, c (y i) = x i := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨F, hF, hc, E, _, _, _, c, hdegree, hscalar, ht⟩ :=
    exists_fg_subfield_model_of_finite_extension p.coeffs (Finset.univ.image x)
  obtain ⟨q, hq, he⟩ := exists_homogeneous_polynomial_over_subfield F p hp hc
  have hqne : q ≠ 0 := by
    intro hz
    apply hne
    rw [← he, hz, map_zero]
  have hs : Smooth (hypersurfaceToBase q hq) :=
    smooth_hypersurfaceToBase_of_subfield_model F q hq p hp he
  have hyex : ∀ i, ∃ y : E, c y = x i := fun i ↦
    ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  choose y hy using hyex
  refine ⟨F, hF, q, hq, he, hqne, hs, E, inferInstance, inferInstance, inferInstance,
    c, hdegree, hscalar, y, ?_, ?_, hy⟩
  · intro hz
    apply hx
    funext i
    simpa only [hz, Pi.zero_apply, map_zero] using (hy i).symm
  · apply c.injective
    rw [map_zero, MvPolynomial.eval₂_comp_left]
    have hb : c.comp (algebraMap F E) = (algebraMap k L).comp F.subtype :=
      RingHom.ext hscalar
    rw [hb, show c ∘ y = x from funext hy,
      ← MvPolynomial.eval₂_map F.subtype x (algebraMap k L) q, he]
    exact heval

end AllCharacteristics
