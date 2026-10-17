import PfaffianDescent.VoisinHypersurfaceTwist

/-! # Actual cubic and quadratic multiplication commute on ambient twists -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The left square of the cubic restriction diagram is actual commuting
multiplication by the cubic and the quadratic. -/
theorem cubicQuadraticMultiplication_left_square
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : homogeneousSubmodule (Fin 4) K 2) :
    mulHomogeneous PS ⟨p, hp⟩ 3 ≫ mulHomogeneous PS q 1 =
      mulHomogeneous PS q 4 ≫ mulHomogeneous PS ⟨p, hp⟩ 1 := by
  ext U z
  apply Subtype.ext
  funext x
  change algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) (q : MvPolynomial (Fin 4) K) *
      (algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) p * z.1 x) =
    algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) p *
      (algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) (q : MvPolynomial (Fin 4) K) * z.1 x)
  ring

end PfaffianDescent.ProjectiveNegativeTwist
