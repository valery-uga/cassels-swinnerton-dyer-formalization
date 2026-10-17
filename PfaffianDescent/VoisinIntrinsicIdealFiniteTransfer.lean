import PfaffianDescent.VoisinSelectedIntrinsicFieldIdeal

/-! Finiteness transfers across equality with a relative triple ideal. -/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous ideal equal to a finite relative cubic--two-quadrics
ideal defines a finite scheme over its coefficient field. -/
theorem isFinite_toBase_of_eq_relativeTripleIdeal
    {F : Type u} [Field F]
    (p q r : MvPolynomial (Fin 4) F)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hI : I = relativeTripleIntersectionHomogeneousIdeal p q r hp hq hr)
    [IsFinite (relativeTripleIntersectionToBase p q r hp hq hr)] :
    IsFinite (toBase I) := by
  rw [hI]
  infer_instance

end PfaffianDescent
