import PfaffianDescent.VoisinSectionRestriction
import PfaffianDescent.HomogeneousIdealPieces

/-!
# Cubic ideal rank from a sixteen-point evaluation
-/

namespace PfaffianDescent

open MvPolynomial Module

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If the cubic vanishing system has dimension three modulo the surface
equation, every homogeneous ideal vanishing on the same coordinates has at
most four cubic equations, counting the surface equation. -/
theorem fixedCurveCubicIdealPiece_finrank_le_four_of_cubicRank_three
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0)
    (hC : ∀ q ∈ C.toIdeal, q.eval₂ (algebraMap K A) x = 0)
    (hrank : cubicVanishingSectionsModuloEquationFinrank p hp x hpx = 3) :
    finrank K (homogeneousIdealPiece C 3) ≤ 4 := by
  have hle : homogeneousIdealPiece C 3 ≤
      LinearMap.ker (homogeneousSectionRestriction (K := K) x 3) := by
    intro q hq
    apply LinearMap.mem_ker.mpr
    change q.val.eval₂ (algebraMap K A) x = 0
    exact hC q.val ((mem_homogeneousIdealPiece_iff C 3 q).mp hq)
  have hker : finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)) = 4 := by
    unfold cubicVanishingSectionsModuloEquationFinrank at hrank
    omega
  exact (Submodule.finrank_mono hle).trans_eq hker

/-- A curve contains every cubic vanishing on the finite scheme exactly when
its cubic ideal piece is the full evaluation kernel, provided its own
equations vanish on that scheme. -/
theorem fixedCurveCubicIdealPiece_eq_restrictionKernel_of_common_component
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A)
    (hC : ∀ q ∈ C.toIdeal, q.eval₂ (algebraMap K A) x = 0)
    (hcommon : ∀ q : homogeneousSubmodule (Fin 4) K 3,
      q.val.eval₂ (algebraMap K A) x = 0 → q.val ∈ C.toIdeal) :
    homogeneousIdealPiece C 3 =
      LinearMap.ker (homogeneousSectionRestriction (K := K) x 3) := by
  apply le_antisymm
  · intro q hq
    apply LinearMap.mem_ker.mpr
    change q.val.eval₂ (algebraMap K A) x = 0
    exact hC q.val ((mem_homogeneousIdealPiece_iff C 3 q).mp hq)
  · intro q hq
    apply (mem_homogeneousIdealPiece_iff C 3 q).mpr
    exact hcommon q (LinearMap.mem_ker.mp hq)

/-- If the curve also contains every cubic through the sixteen-point scheme,
its cubic ideal piece has the full four-dimensional kernel rank. -/
theorem fixedCurveCubicIdealPiece_finrank_eq_four_of_common_component
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0)
    (hC : ∀ q ∈ C.toIdeal, q.eval₂ (algebraMap K A) x = 0)
    (hcommon : ∀ q : homogeneousSubmodule (Fin 4) K 3,
      q.val.eval₂ (algebraMap K A) x = 0 → q.val ∈ C.toIdeal)
    (hrank : cubicVanishingSectionsModuloEquationFinrank p hp x hpx = 3) :
    finrank K (homogeneousIdealPiece C 3) = 4 := by
  rw [fixedCurveCubicIdealPiece_eq_restrictionKernel_of_common_component
    C x hC hcommon]
  unfold cubicVanishingSectionsModuloEquationFinrank at hrank
  omega

end PfaffianDescent
