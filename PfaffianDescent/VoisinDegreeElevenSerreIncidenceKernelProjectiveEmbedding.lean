import PfaffianDescent.RectangularSubstitution
import PfaffianDescent.PolynomialProjectiveMap

/-! # An actual projective-plane embedding from a split kernel frame

The matrix columns are the three kernel members.  Their literal left inverse
constructs a closed projective-plane embedding into the nine-section space.
The evaluation equations vanish under that embedding by the literal matrix
identity.  Equality with the full evaluation incidence is a further step.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R]

abbrev serreKernelFrameProjectiveEmbedding
    (frame : Matrix (Fin 9) (Fin 3) R)
    (retraction : Matrix (Fin 3) (Fin 9) R)
    (hframe : retraction * frame = 1) :
    scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) ⟶
      scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R)) :=
  polynomialProjectiveMap _ _ (rectangularSubstitution frame) bot_le
    (fun _ _ hp => rectangularSubstitution_homogeneous frame hp)
    (rectangularSubstitution_surjective frame retraction hframe)

instance serreKernelFrameProjectiveEmbedding_isClosedImmersion
    (frame : Matrix (Fin 9) (Fin 3) R)
    (retraction : Matrix (Fin 3) (Fin 9) R)
    (hframe : retraction * frame = 1) :
    IsClosedImmersion (serreKernelFrameProjectiveEmbedding frame retraction hframe) := by
  exact polynomialProjectiveMap_isClosedImmersion _ _ _ _ _ _

theorem serreKernelFrameProjectiveEmbedding_toBase
    (frame : Matrix (Fin 9) (Fin 3) R)
    (retraction : Matrix (Fin 3) (Fin 9) R)
    (hframe : retraction * frame = 1) :
    serreKernelFrameProjectiveEmbedding frame retraction hframe ≫
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R)) =
    toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) :=
  polynomialProjectiveMap_toBase _ _ _ _ _ _

/-- The actual six evaluation equations restrict to zero on the actual
three-coordinate kernel parameter. -/
theorem serreKernelFrameProjectiveEmbedding_evaluationEquations
    (evaluation : Matrix (Fin 6) (Fin 9) R)
    (frame : Matrix (Fin 9) (Fin 3) R)
    (hkernel : evaluation * frame = 0) (i : Fin 6) :
    rectangularSubstitution frame (rectangularLinearCoordinate evaluation i) = 0 := by
  rw [rectangularSubstitution_coordinate, hkernel]
  simp [rectangularLinearCoordinate, Matrix.mulVec, dotProduct]

end PfaffianDescent
