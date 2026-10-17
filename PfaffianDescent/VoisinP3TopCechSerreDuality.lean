import PfaffianDescent.VoisinP3TopCechCohomology
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Explicit Serre duality for the top Cech quotient of `O(-6)`

The ten residue coordinates are identified with the dual of the actual
degree-two homogeneous polynomial module via its standard monomial basis.
Composing this basis equivalence with the previously computed Cech quotient
gives a concrete additive Serre-duality equivalence.
-/

noncomputable section

open MvPolynomial

universe u

namespace PfaffianDescent.LaurentCechExact

variable (K : Type u) [Field K]

/-- The standard degree-two monomials form a basis of the homogeneous
quadratic module. -/
noncomputable def p3QuadraticMonomialBasis :
    Module.Basis P3QuadraticExponent K
      (homogeneousSubmodule (Fin 4) K 2) :=
  (MvPolynomial.basisRestrictSupport K
      {d : Fin 4 →₀ ℕ | d.degree = 2}).map
    (LinearEquiv.ofEq
      (MvPolynomial.restrictSupport K {d : Fin 4 →₀ ℕ | d.degree = 2})
      (homogeneousSubmodule (Fin 4) K 2)
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported
        (Fin 4) K 2).symm)

@[simp]
lemma p3QuadraticMonomialBasis_apply_coe
    (b : P3QuadraticExponent) :
    ((p3QuadraticMonomialBasis K b :
        homogeneousSubmodule (Fin 4) K 2) : MvPolynomial (Fin 4) K) =
      MvPolynomial.monomial b 1 := by
  change (((MvPolynomial.basisRestrictSupport K
      {d : Fin 4 →₀ ℕ | d.degree = 2}) b :
        MvPolynomial.restrictSupport K
          {d : Fin 4 →₀ ℕ | d.degree = 2}) :
      MvPolynomial (Fin 4) K) = _
  change ((AddMonoidAlgebra.supportedEquivFinsupp
      (R := K) (S := K) {d : Fin 4 →₀ ℕ | d.degree = 2}).symm
        (Finsupp.single b 1) : MvPolynomial (Fin 4) K) = _
  simp [AddMonoidAlgebra.supportedEquivFinsupp,
    MvPolynomial.single_eq_monomial]

/-- Evaluation of a quadratic functional on the standard monomial basis is
a linear equivalence with the ten coordinate functions. -/
noncomputable def p3QuadraticDualCoordinateEquiv :
    Module.Dual K (homogeneousSubmodule (Fin 4) K 2) ≃ₗ[K]
      (P3QuadraticExponent → K) :=
  (p3QuadraticMonomialBasis K).dualBasis.equivFun

@[simp]
lemma p3QuadraticDualCoordinateEquiv_apply
    (phi : Module.Dual K (homogeneousSubmodule (Fin 4) K 2))
    (b : P3QuadraticExponent) :
    p3QuadraticDualCoordinateEquiv K phi b =
      phi (p3QuadraticMonomialBasis K b) := by
  exact Module.Basis.dualBasis_equivFun (p3QuadraticMonomialBasis K) phi b

end PfaffianDescent.LaurentCechExact

namespace PfaffianDescent.ProjectiveNegativeTwist

open LaurentCechExact

variable (K : Type u) [Field K]

/-- Concrete top-Cech Serre duality for `O(-6)` on projective three-space:
the quotient of raw top cocycles by actual Cech boundaries is additively
equivalent to the dual of the homogeneous quadratic module. -/
noncomputable def p3NegativeSixTopCechCohomologyDualQuadraticEquiv :
    p3NegativeSixTopCocycles K ⧸
        (p3NegativeSixTopResidueCoordinates K).ker ≃+
      Module.Dual K (homogeneousSubmodule (Fin 4) K 2) :=
  (p3NegativeSixTopCechCohomologyResidueEquiv K).trans
    (p3QuadraticDualCoordinateEquiv K).toAddEquiv.symm

end PfaffianDescent.ProjectiveNegativeTwist
