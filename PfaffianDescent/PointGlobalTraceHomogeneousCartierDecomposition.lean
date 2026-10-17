import PfaffianDescent.ThreeGeneratorKoszul
import PfaffianDescent.HomogeneousProjection

/-! # Homogeneous Cartier coefficients in a three-linear-form point ideal

Membership of a homogeneous cubic in the ideal of three linear forms
provides homogeneous quadratic coefficients. This is the degree constraint
needed to sheafify the explicit ambient Koszul Cartier homotopy.
-/

namespace PfaffianDescent
open MvPolynomial

/-- An actual cubic equation in a three-linear-form ideal has quadratic
coefficients, obtained by projecting any ideal-membership expression. -/
theorem pointGlobalTrace_exists_homogeneous_cartier_coefficients
    {K : Type*} [Field K] {p f g h : MvPolynomial (Fin 4) K}
    (hp : p.IsHomogeneous 3) (hf : f.IsHomogeneous 1)
    (hg : g.IsHomogeneous 1) (hh : h.IsHomogeneous 1)
    (hmem : p ∈ Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K))) :
    ∃ a b c : homogeneousSubmodule (Fin 4) K 2,
      p = f * (a : MvPolynomial (Fin 4) K) +
        g * (b : MvPolynomial (Fin 4) K) + h * (c : MvPolynomial (Fin 4) K) := by
  rw [← threeGeneratorLast_range] at hmem
  obtain ⟨⟨a, b, c⟩, habc⟩ := hmem
  change f * a + g * b + h * c = p at habc
  refine ⟨⟨homogeneousComponent 2 a, homogeneousComponent_isHomogeneous 2 a⟩,
    ⟨homogeneousComponent 2 b, homogeneousComponent_isHomogeneous 2 b⟩,
    ⟨homogeneousComponent 2 c, homogeneousComponent_isHomogeneous 2 c⟩, ?_⟩
  have heq := congrArg (homogeneousComponent 3) habc
  simp only [map_add, homogeneousComponent_eq_self hp] at heq
  rw [show (3 : ℕ) = 1 + 2 from rfl,
    homogeneousComponent_mul_left hf, homogeneousComponent_mul_left hg,
    homogeneousComponent_mul_left hh] at heq
  exact heq.symm

end PfaffianDescent
