import PfaffianDescent.FiniteEquationHilbertAllTestRepresentability
import PfaffianDescent.MonomialCoefficientGluedFinitePresentation307
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! The actual WHOLE finite-equation locus in the existing H300 is
locally of finite presentation over the ORIGINAL Noetherian base. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
set_option autoImplicit false

/-- Derive LFP for the actual finite-equation representing object's
original structure map. No LFP/FG/reducedness outcome is an input; its
literal whole ideal and existing original-H inclusion are retained. -/
theorem finiteEquationHilbertRepresentingObject_locallyOfFinitePresentation001
    (R : Type u) [CommRing R] [IsNoetherianRing R] (m n r : ℕ)
    (q : Fin r → MvPolynomial (Fin m) R) :
    LocallyOfFinitePresentation (finiteEquationHilbertRepresentingObject001 R m n r q).hom := by
  letI : LocallyOfFinitePresentation (monomialCoefficientGluedToBase300 R m n) :=
    monomialCoefficientGluedToBase_locallyOfFinitePresentation307 R m n
  letI : LocallyOfFiniteType (finiteEquationHilbertCoefficientIdeal001 R m n r q).subschemeι :=
    inferInstance
  letI : LocallyOfFiniteType (finiteEquationHilbertRepresentingObject001 R m n r q).hom := by
    change LocallyOfFiniteType
      ((finiteEquationHilbertCoefficientIdeal001 R m n r q).subschemeι ≫
        monomialCoefficientGluedToBase300 R m n)
    infer_instance
  exact (LocallyOfFinitePresentation.iff_locallyOfFiniteType
    (f := (finiteEquationHilbertRepresentingObject001 R m n r q).hom)).mpr inferInstance

end PfaffianDescent
end
