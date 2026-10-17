import PfaffianDescent.CubicSurfaceSectionDimensions
import PfaffianDescent.VoisinSectionRestriction

/-!
# The first curve choice in Coray's descent

SOURCE DRAFT: not compiler checked.

For every degree, construct an actual homogeneous equation vanishing on
specified finite-algebra coordinates, whose restriction to the cubic is
nonzero. The cubic relations are removed by the actual coordinate-ring
projection. No hypothesis about existence of a curve or a reduced point is
used. Geometric irreducibility, the genus estimate, and divisor effectivity
are separate later obligations in Coray (1976), Theorem 7.1.
-/

namespace PfaffianDescent.Coray

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A]

/-- More actual sections on the cubic than finite evaluation conditions
produce an equation through those coordinates which does not contain the
whole cubic surface. This holds in every degree, including below three. -/
theorem exists_homogeneous_curve_equation_of_grade_finrank_lt
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (x : Fin 4 → A)
    (hsize : finrank K A < finrank K (grading (equationIdeal p hp) n)) :
    ∃ q : MvPolynomial (Fin 4) K,
      q.IsHomogeneous n ∧ q.eval₂ (algebraMap K A) x = 0 ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
  classical
  letI : FiniteDimensional K (homogeneousSubmodule (Fin 4) K n) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) K n)
  let E := homogeneousSectionRestriction (K := K) x n
  let P : homogeneousSubmodule (Fin 4) K n →ₗ[K]
      CoordinateRing (equationIdeal p hp) := cubicSurfaceProjection p hp n
  have hE : finrank K (LinearMap.range E) + finrank K (LinearMap.ker E) =
      finrank K (homogeneousSubmodule (Fin 4) K n) :=
    E.finrank_range_add_finrank_ker
  have hP : finrank K (LinearMap.range P) + finrank K (LinearMap.ker P) =
      finrank K (homogeneousSubmodule (Fin 4) K n) :=
    P.finrank_range_add_finrank_ker
  have hErange : finrank K (LinearMap.range E) ≤ finrank K A :=
    Submodule.finrank_le (LinearMap.range E)
  have hPrange : finrank K (LinearMap.range P) =
      finrank K (grading (equationIdeal p hp) n) := by
    rw [show LinearMap.range P = grading (equationIdeal p hp) n from
      cubicSurfaceProjection_range p hp n]
  have hnot : ¬ LinearMap.ker E ≤ LinearMap.ker P := by
    intro hle
    have hk : finrank K (LinearMap.ker E) ≤ finrank K (LinearMap.ker P) :=
      Submodule.finrank_mono hle
    omega
  have hex : ∃ q : homogeneousSubmodule (Fin 4) K n,
      q ∈ LinearMap.ker E ∧ q ∉ LinearMap.ker P := by
    by_contra h
    apply hnot
    intro q hq
    by_contra hqP
    exact h ⟨q, hq, hqP⟩
  obtain ⟨q, hqE, hqP⟩ := hex
  refine ⟨q.val, q.property, LinearMap.mem_ker.mp hqE, ?_⟩
  intro hmem
  apply hqP
  change Ideal.Quotient.mk (equationIdeal p hp).toIdeal q.val = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

/-- Coray's section choice using the proved Hilbert function rather than an
unproved section-space dimension certificate. -/
theorem exists_homogeneous_curve_equation
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (n : ℕ) (x : Fin 4 → A)
    (hsize : finrank K A < (n + 3).choose 3 - n.choose 3) :
    ∃ q : MvPolynomial (Fin 4) K,
      q.IsHomogeneous n ∧ q.eval₂ (algebraMap K A) x = 0 ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
  apply exists_homogeneous_curve_equation_of_grade_finrank_lt p hp n x
  rwa [cubicSurface_grade_finrank p hp hne n]

end
end PfaffianDescent.Coray
