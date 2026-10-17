import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! SOURCE ONLY / UNVERIFIED148. Explicit coefficients for the actual generic
hyperplane X_0 + t_0 X_1 + t_1 X_2 + t_2 X_3. Their independence is constructed
from the polynomial variables and retained in every coefficient-field
extension, including an algebraic closure of the parameter field. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open scoped BigOperators
universe u

/-- The rational parameter field of hyperplanes in the affine dual chart. -/
abbrev GenericHyperplaneField (K : Type u) [Field K] :=
  FractionRing (MvPolynomial (Fin 3) K)

/-- The three actual independent coefficients of the generic hyperplane. -/
def genericHyperplaneCoefficient {K : Type u} [Field K] :
    Fin 3 → GenericHyperplaneField K :=
  fun i => algebraMap (MvPolynomial (Fin 3) K) (GenericHyperplaneField K)
    (MvPolynomial.X i)

/-- Independence is a genuine consequence of polynomial-variable
independence and injectivity into the fraction field. -/
theorem genericHyperplaneCoefficient_algebraicIndependent
    {K : Type u} [Field K] :
    AlgebraicIndependent K (genericHyperplaneCoefficient (K := K)) := by
  let R := MvPolynomial (Fin 3) K
  let L := GenericHyperplaneField K
  exact (MvPolynomial.algebraicIndependent_X (Fin 3) K).map'
    (f := IsScalarTower.toAlgHom K R L) (IsFractionRing.injective R L)

/-- Extending the WHOLE coefficient field preserves the same three
independent coefficients. This is available for all fields, not only
algebraically closed or infinite original fields. -/
theorem genericHyperplaneCoefficient_algebraicIndependent_extension
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    [Algebra (GenericHyperplaneField K) M]
    [IsScalarTower K (GenericHyperplaneField K) M] :
    AlgebraicIndependent K (fun i =>
      algebraMap (GenericHyperplaneField K) M
        (genericHyperplaneCoefficient (K := K) i)) := by
  exact genericHyperplaneCoefficient_algebraicIndependent.map'
    (f := IsScalarTower.toAlgHom K (GenericHyperplaneField K) M)
    (algebraMap (GenericHyperplaneField K) M).injective

/-- The literal generic plane equation, with fixed nonzero zeroth coefficient. -/
def genericHyperplaneEquation {K : Type u} [Field K] :
    MvPolynomial (Fin 4) (GenericHyperplaneField K) :=
  MvPolynomial.X 0 + ∑ i : Fin 3,
    MvPolynomial.C (genericHyperplaneCoefficient (K := K) i) * MvPolynomial.X i.succ

/-- The generic equation is an actual homogeneous linear form. -/
theorem genericHyperplaneEquation_isHomogeneous {K : Type u} [Field K] :
    (genericHyperplaneEquation (K := K)).IsHomogeneous 1 := by
  unfold genericHyperplaneEquation
  apply (isHomogeneous_X _ _).add
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- The fixed normal coefficient is exactly one. -/
theorem genericHyperplaneEquation_pderiv_zero {K : Type u} [Field K] :
    MvPolynomial.pderiv (0 : Fin 4) (genericHyperplaneEquation (K := K)) = 1 := by
  classical
  simp [genericHyperplaneEquation, map_sum, MvPolynomial.pderiv_C_mul,
    MvPolynomial.pderiv_X, Pi.single_apply]

/-- Every other normal coefficient is the actual independent parameter. -/
theorem genericHyperplaneEquation_pderiv_succ {K : Type u} [Field K] (i : Fin 3) :
    MvPolynomial.pderiv i.succ (genericHyperplaneEquation (K := K)) =
      MvPolynomial.C (genericHyperplaneCoefficient (K := K) i) := by
  classical
  simp [genericHyperplaneEquation, map_sum, MvPolynomial.pderiv_C_mul,
    MvPolynomial.pderiv_X, Pi.single_apply, Fin.succ_inj]

/-- The actual generic plane equation is nonzero, derived by its derivative. -/
theorem genericHyperplaneEquation_ne_zero {K : Type u} [Field K] :
    genericHyperplaneEquation (K := K) ≠ 0 := by
  intro hz
  have hd := genericHyperplaneEquation_pderiv_zero (K := K)
  simpa [hz] using hd

end PfaffianDescent.Coray
