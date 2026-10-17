import AllCharacteristics.FiniteCoefficientField
import AllCharacteristics.HomogeneousFieldDescent

/-!
# Smooth homogeneous equations over finitely generated subfields

After descending the coefficients, smoothness follows by faithfully flat
field descent. Nonzeroness and homogeneity are retained, and any additional
finite coefficient data can be included in the same finitely generated field.
-/

open AlgebraicGeometry
namespace AllCharacteristics
open HomogeneousProjective
universe u
variable {k : Type u} [Field k] {σ : Type}

/-- An exact homogeneous equation model over a subfield retains the original
hypersurface's smoothness. -/
theorem smooth_hypersurfaceToBase_of_subfield_model
    (F : Subfield k) (q : MvPolynomial σ F) {d : ℕ} (hq : q.IsHomogeneous d)
    (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) (he : q.map F.subtype = p)
    [Smooth (hypersurfaceToBase p hp)] : Smooth (hypersurfaceToBase q hq) := by
  have : Smooth (hypersurfaceToBase (q.map F.subtype) (hq.map F.subtype)) :=
    (smooth_hypersurfaceToBase_congr (q.map F.subtype) p (hq.map F.subtype) hp he).mpr
      inferInstance
  exact smooth_hypersurfaceToBase_of_smooth_field_map F.subtype q hq

/-- A nonzero smooth homogeneous equation, together with arbitrary finite
auxiliary coefficients, has a nonzero smooth model over a finitely generated
subfield of the original field. -/
theorem exists_fg_subfield_smooth_homogeneous_model
    (p : MvPolynomial σ k) {d : ℕ} (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (s : Finset k) :
    ∃ F : Subfield k, Field.FG F ∧ (s : Set k) ⊆ F ∧
      ∃ q : MvPolynomial σ F, ∃ hq : q.IsHomogeneous d,
        q.map F.subtype = p ∧ q ≠ 0 ∧ Smooth (hypersurfaceToBase q hq) := by
  obtain ⟨F, hF, hs, q, hq, he⟩ := exists_fg_subfield_homogeneous_model p hp s
  refine ⟨F, hF, hs, q, hq, he, ?_, smooth_hypersurfaceToBase_of_subfield_model F q hq p hp he⟩
  intro hzero
  apply hne
  rw [← he, hzero, map_zero]

end AllCharacteristics
