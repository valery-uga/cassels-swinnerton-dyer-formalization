import PfaffianDescent.CorayGenericRationalTensorDomain
import PfaffianDescent.CorayWholeCoefficientQuotientTensor
import PfaffianDescent.CorayOwnCoordinateCartierCut

/-! SOURCE ONLY / UNVERIFIED152. For the actual original prime C, the literal
whole extension to K(T0,T1,T2) remains prime and the SAME generic H is regular.
Both conclusions are constructed; no component is selected after extension. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial AlgebraicGeometry TensorProduct
open scoped TensorProduct BigOperators
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Literal WHOLE original ideal extended to the actual generic parameter field. -/
abbrev wholeGenericCurveIdeal
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :=
  PfaffianDescent.coefficientChangedHomogeneousIdeal
    (algebraMap K (GenericHyperplaneField K)) C

/-- The underlying extended ideal is exact, without saturation or a prime choice. -/
theorem wholeGenericCurveIdeal_toIdeal
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    (wholeGenericCurveIdeal C).toIdeal =
      C.toIdeal.map (MvPolynomial.map (algebraMap K (GenericHyperplaneField K))) :=
  (PfaffianDescent.coefficientChangedHomogeneousIdeal_toIdeal _ C).symm

/-- SAME whole coefficient ideal plus SAME literal generic hyperplane. -/
def wholeGenericCutIdeal
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :=
  wholeGenericCurveIdeal C ⊔ equationIdeal (genericHyperplaneEquation (K := K))
    genericHyperplaneEquation_isHomogeneous

/-- Exact whole cut ideal, including nilpotents; no saturation/component choice. -/
theorem wholeGenericCutIdeal_toIdeal
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    (wholeGenericCutIdeal C).toIdeal =
      C.toIdeal.map (MvPolynomial.map (algebraMap K (GenericHyperplaneField K))) ⊔
        Ideal.span {genericHyperplaneEquation (K := K)} := by
  rw [wholeGenericCutIdeal, HomogeneousIdeal.toIdeal_sup, wholeGenericCurveIdeal_toIdeal]
  rfl

/-- Primality of the literal WHOLE extension is derived specifically for the
purely transcendental parameter field. This does not assert primality after
arbitrary or algebraically closed coefficient extension. -/
theorem wholeGenericCurveIdeal_isPrime
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (hprime : C.toIdeal.IsPrime) :
    (wholeGenericCurveIdeal C).toIdeal.IsPrime := by
  letI : C.toIdeal.IsPrime := hprime
  let A := CoordinateRing C
  let L := GenericHyperplaneField K
  letI : IsDomain (A ⊗[K] L) :=
    (genericRationalTensor_isDomain_and_localization_injective (K := K) (A := A)).1
  letI : IsDomain (L ⊗[K] A) :=
    MulEquiv.isDomain (A ⊗[K] L) (Algebra.TensorProduct.comm K L A).toMulEquiv
  let e := wholeHomogeneousCoefficientQuotientTensorAlgEquiv (E := L) C
  have hdom : IsDomain (CoordinateRing (wholeGenericCurveIdeal C)) :=
    MulEquiv.isDomain (L ⊗[K] A) e.symm.toMulEquiv
  exact (Ideal.Quotient.isDomain_iff_prime _).mp hdom

/-- Literal tensor hyperplane in the reversed tensor order used by the actual
whole coordinate quotient equivalence. -/
def wholeGenericCurveTensorHyperplane
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    GenericHyperplaneField K ⊗[K] CoordinateRing C :=
  1 ⊗ₜ[K] coordinate C 0 + ∑ i : Fin 3,
    genericHyperplaneCoefficient (K := K) i ⊗ₜ[K] coordinate C i.succ

/-- Native tensor commutation recovers exactly the constructed domain's H. -/
theorem wholeGenericCurveTensorHyperplane_comm
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    Algebra.TensorProduct.comm K (GenericHyperplaneField K) (CoordinateRing C)
      (wholeGenericCurveTensorHyperplane C) =
        genericRationalTensorHyperplane (K := K) (coordinate C) := by
  simp [wholeGenericCurveTensorHyperplane, genericRationalTensorHyperplane]

/-- The actual quotient algebra equivalence sends this tensor to the literal
SAME generic equation class in the actual whole extended quotient. -/
theorem wholeGenericCurveTensorHyperplane_quotient
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    wholeHomogeneousCoefficientQuotientTensorAlgEquiv
      (E := GenericHyperplaneField K) C (wholeGenericCurveTensorHyperplane C) =
        Ideal.Quotient.mk (wholeGenericCurveIdeal C).toIdeal
          (genericHyperplaneEquation (K := K)) := by
  unfold wholeHomogeneousCoefficientQuotientTensorAlgEquiv
    wholeGenericCurveTensorHyperplane
  simp only [AlgEquiv.trans_apply, map_add, map_sum, coordinate,
    wholeCoefficientQuotientTensorAlgEquiv_tmul_mk, Ideal.quotientEquivAlgOfEq_mk,
    MvPolynomial.map_X, one_smul, MvPolynomial.smul_eq_C_mul]
  simp only [genericHyperplaneEquation, map_add, map_sum]

/-- Actual original relevance constructs a nonzero coordinate tuple. The point
belongs to original C; no point on a chosen extended component is supplied. -/
theorem originalWholeCurve_coordinate_exists_ne_zero
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (P : scheme C) :
    ∃ j, coordinate C j ≠ 0 := by
  obtain ⟨j, hj⟩ := projectivePoint_exists_coordinate_notMem C P
  exact ⟨j, (coordinate_notMem_at_point_ne_zero_and_notMem_component C P j hj).1⟩

/-- SAME generic H is nonzero on the literal whole extended C, constructed
from the ORIGINAL point and actual parameter localization. -/
theorem wholeGenericHyperplane_not_mem
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (hprime : C.toIdeal.IsPrime)
    (P : scheme C) : genericHyperplaneEquation (K := K) ∉ (wholeGenericCurveIdeal C).toIdeal := by
  letI : C.toIdeal.IsPrime := hprime
  have hnonzero := genericRationalTensorHyperplane_ne_zero (K := K)
    (coordinate C) (originalWholeCurve_coordinate_exists_ne_zero C P)
  intro hmem
  have hzero : Ideal.Quotient.mk (wholeGenericCurveIdeal C).toIdeal
      (genericHyperplaneEquation (K := K)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have htzero : wholeGenericCurveTensorHyperplane C = 0 := by
    apply (wholeHomogeneousCoefficientQuotientTensorAlgEquiv
      (E := GenericHyperplaneField K) C).injective
    rw [wholeGenericCurveTensorHyperplane_quotient, hzero, map_zero]
  have hc := congrArg
    (Algebra.TensorProduct.comm K (GenericHyperplaneField K) (CoordinateRing C)) htzero
  rw [wholeGenericCurveTensorHyperplane_comm, map_zero] at hc
  exact hnonzero hc

/-- Actual polynomial nonzerodivisor statement, not merely grade injectivity. -/
theorem wholeGenericHyperplane_regular
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (hprime : C.toIdeal.IsPrime)
    (P : scheme C) : ∀ q : MvPolynomial (Fin 4) (GenericHyperplaneField K),
      genericHyperplaneEquation (K := K) * q ∈ (wholeGenericCurveIdeal C).toIdeal →
        q ∈ (wholeGenericCurveIdeal C).toIdeal := by
  letI : (wholeGenericCurveIdeal C).toIdeal.IsPrime := wholeGenericCurveIdeal_isPrime C hprime
  intro q hq
  exact ((wholeGenericCurveIdeal_isPrime C hprime).mem_or_mem hq).resolve_left
    (wholeGenericHyperplane_not_mem C hprime P)

/-- Actual native regular-principal immersion of the SAME whole generic cut. -/
def wholeGenericHyperplane_regularPrincipalImmersion
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (hprime : C.toIdeal.IsPrime)
    (P : scheme C) : PfaffianDescent.RegularPrincipalImmersion
      (PfaffianDescent.schemeQuotientMap (wholeGenericCurveIdeal C)
        (wholeGenericCurveIdeal C ⊔ equationIdeal (genericHyperplaneEquation (K := K))
          genericHyperplaneEquation_isHomogeneous) le_sup_left) := by
  letI : (wholeGenericCurveIdeal C).toIdeal.IsPrime := wholeGenericCurveIdeal_isPrime C hprime
  exact primeComponent_linearSection_regularPrincipalImmersion
    (wholeGenericCurveIdeal C) _ _ (wholeGenericHyperplane_not_mem C hprime P)

end PfaffianDescent.Coray

