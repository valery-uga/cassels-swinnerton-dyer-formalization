import PfaffianDescent.VoisinConicCubicSheafRestriction

/-!
# Cubic section restriction to a plane conic

The source of the restriction map is the literal global-section space
`H⁰(S, O_S(3))`, identified with the cubic graded coordinate piece by the
proved smooth-cubic equivalence. The target consists of actual global
sections on the possibly reducible or nonreduced plane conic.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory AlgebraicGeometry MvPolynomial
open AllCharacteristics HomogeneousProjective

universe u

variable (K : Type u) [Field K] [Infinite K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Restriction of literal cubic sections of a smooth cubic surface to a
plane conic contained in it. -/
noncomputable def cubicSurfaceToPlaneConicLiteralSectionRestriction
    [HasExt.{u} (Proj PS).Modules]
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hell : ell.IsHomogeneous 1) (hq : q.IsHomogeneous 2)
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K))) :=
  (cubicToPlaneConicPositiveGlobalSectionLinearMap
    p ell q hp hell hq hpc).comp
      (cubicPositiveThreeGlobalSectionsLinearEquiv K p hp hp0).symm.toLinearMap

/-- Every nonzero plane conic on a nonzero smooth cubic imposes at least
seven independent conditions on literal `H⁰(S, O_S(3))` sections. The conic
may be reducible or nonreduced. -/
theorem cubicSurfaceToPlaneConicLiteralSectionRestriction_range_finrank_ge_seven
    [HasExt.{u} (Proj PS).Modules]
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0)
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K))) :
    7 ≤ Module.finrank K
      (LinearMap.range (cubicSurfaceToPlaneConicLiteralSectionRestriction
        K p ell q hp hp0 hell hq hpc)) := by
  let e := cubicPositiveThreeGlobalSectionsLinearEquiv K p hp hp0
  let f := cubicToPlaneConicPositiveGlobalSectionLinearMap
    p ell q hp hell hq hpc
  have hrange : LinearMap.range
      (cubicSurfaceToPlaneConicLiteralSectionRestriction
        K p ell q hp hp0 hell hq hpc) = LinearMap.range f := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨e.symm s, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨e x, ?_⟩
      simp [cubicSurfaceToPlaneConicLiteralSectionRestriction, e, f]
  rw [hrange]
  exact cubicToPlaneConicPositiveGlobalSectionLinearMap_range_finrank_ge_seven
    p ell q hp hp0 hell hell0 hq hq0 hpc

end PfaffianDescent.ProjectiveNegativeTwist
