import PfaffianDescent.HomogeneousIdealPieces
import PfaffianDescent.VoisinVeryAmpleCubicSections

/-!
# Cubic sections vanishing along a fixed curve

Three projectively distinct points on a proposed fixed curve impose three
independent conditions on cubic sections of a cubic surface.  This module
applies that geometric bound to the intrinsic cubic ideal piece of the curve.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Cubic sections of the surface whose homogeneous representatives vanish
along the closed subscheme represented by `C`. -/
noncomputable def fixedCurveCubicSurfaceSystem
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    Submodule K (grading (equationIdeal p hp) 3) :=
  (homogeneousIdealPiece C 3).map
    (cubicSurfaceHomogeneousCoordinateProjection p hp 3)

/-- If a fixed curve contains three distinct projective points, its cubic
ideal piece has at most sixteen independent sections after restriction to
the cubic surface. -/
theorem fixedCurveCubicSurfaceSystem_finrank_le_sixteen
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 3 → cubicSurfaceAffinePoints p)
    (hdir : ∀ i j, i ≠ j → ∀ a : K, a • (x i).1 ≠ (x j).1)
    (hx : ∀ i, ∀ f ∈ C.toIdeal, MvPolynomial.aeval (x i).1 f = 0) :
    finrank K (fixedCurveCubicSurfaceSystem p hp C) ≤ 16 := by
  apply cubicSurfaceCubicSubmodule_finrank_le_sixteen_of_pointwise_vanishing
    p hp hne x hdir
  intro z i
  obtain ⟨q, hqC, hqz⟩ := z.property
  rw [← hqz]
  change MvPolynomial.aeval (x i).1 q.1 = 0
  exact hx i q.1 ((mem_homogeneousIdealPiece_iff C 3 q).mp hqC)

/-- Before quotienting by the surface equation, the cubic ideal piece of a
curve through three distinct projective points has dimension at most
seventeen. This bounds the rank of its cubic Grassmannian presentation. -/
theorem fixedCurveCubicIdealPiece_finrank_le_seventeen
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (v : Fin 3 → Fin 4 → K)
    (hv : ∀ i, v i ≠ 0)
    (hdir : ∀ i j, i ≠ j → ∀ a : K, a • v i ≠ v j)
    (hx : ∀ i, ∀ f ∈ C.toIdeal, MvPolynomial.aeval (v i) f = 0) :
    finrank K (homogeneousIdealPiece C 3) ≤ 17 := by
  let E := homogeneousCubicTripleEvaluation v
  have hsurj : Function.Surjective E :=
    homogeneousCubicTripleEvaluation_surjective v hv hdir
  have hrange : LinearMap.range E = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := E.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_pi_fintype,
    Module.finrank_self, four_variable_homogeneous_finrank] at hdim
  have hchoose : Nat.choose 6 3 = 20 := by decide
  rw [hchoose] at hdim
  norm_num at hdim
  have hC : homogeneousIdealPiece C 3 ≤ LinearMap.ker E := by
    intro q hq
    apply LinearMap.mem_ker.mpr
    funext i
    exact hx i q.1 ((mem_homogeneousIdealPiece_iff C 3 q).mp hq)
  have hle := Submodule.finrank_mono hC
  omega

end PfaffianDescent
