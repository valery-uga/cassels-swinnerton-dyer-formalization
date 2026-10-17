import AllCharacteristics.ProjectivePoints
import Mathlib.Algebra.MvPolynomial.Rename

/- SOURCE ONLY / UNVERIFIED. Elementary inverse coordinate permutation
transports a rational section back to the SAME original hypersurface.
No degree-four/five descent or Chapter3 point/Pfaffian theorem. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma independent_hypersurface_section_of_rename_section
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (e : Fin 4 ≃ Fin 4)
    (h : ∃ s : Spec (.of K) ⟶ hypersurface (rename e p) hp.rename_isHomogeneous,
      s ≫ hypersurfaceToBase (rename e p) hp.rename_isHomogeneous = 𝟙 _) :
    ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨x, hx, hpx⟩ := hypersurface_coordinates_of_point (RingHom.id K)
    (rename e p) hp.rename_isHomogeneous s (by simpa using hs)
  let y := x ∘ e
  have hy : y ≠ 0 := by
    intro hy
    apply hx
    funext a
    have h := congrFun hy (e.symm a)
    simpa only [y, Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using h
  have hpy : p.eval₂ (RingHom.id K) y = 0 := by
    simpa only [eval₂_rename] using hpx
  obtain ⟨q, hq⟩ := hypersurface_point_of_coordinates (RingHom.id K) p hp y hy hpy
  exact ⟨q, by simpa using hq⟩

end PfaffianDescent
