import PfaffianDescent.CorayGenericHyperplaneCoefficients
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Maps

/- SOURCE ONLY152; no compiler, options, or limit changes. -/

/- Source snapshot: /private/tmp/cassels-coray-whole-generic-cut-source152/new/PfaffianDescent/CorayGenericRationalTensorDomain.lean -/
/-! SOURCE ONLY / UNVERIFIED152. The actual purely transcendental extension
of a domain is a native localization of its polynomial tensor algebra.
No domain conclusion after coefficient extension is an input. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial TensorProduct
open scoped TensorProduct BigOperators nonZeroDivisors
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

/-- The polynomial tensor algebra before inverting parameter polynomials. -/
abbrev GenericPolynomialTensor := A ⊗[K] MvPolynomial (Fin 3) K
/-- The literal rational-parameter tensor algebra, retaining all of A. -/
abbrev GenericRationalTensor := A ⊗[K] GenericHyperplaneField K

/-- Actual parameter localization map; the first factor is unchanged. -/
def genericRationalTensorLocalizationHom :
    GenericPolynomialTensor (K := K) (A := A) →ₐ[A]
      GenericRationalTensor (K := K) (A := A) :=
  Algebra.TensorProduct.map (AlgHom.id A A)
    (IsScalarTower.toAlgHom K (MvPolynomial (Fin 3) K) (GenericHyperplaneField K))

/-- Explicit polynomial model of the tensor algebra. -/
def genericPolynomialTensorAlgEquiv :
    GenericPolynomialTensor (K := K) (A := A) ≃ₐ[A] MvPolynomial (Fin 3) A :=
  MvPolynomial.algebraTensorAlgEquiv K A

/-- The parameter-polynomial inclusion is injective, derived from the actual
polynomial model and injectivity of the original coefficient field map. -/
theorem genericPolynomialTensor_includeRight_injective [Nontrivial A] :
    Function.Injective (Algebra.TensorProduct.includeRight :
      MvPolynomial (Fin 3) K →ₐ[K] GenericPolynomialTensor (K := K) (A := A)) := by
  intro p q h
  have hh := congrArg (genericPolynomialTensorAlgEquiv (K := K) (A := A)) h
  have hmap : MvPolynomial.map (algebraMap K A) p =
      MvPolynomial.map (algebraMap K A) q := by
    simpa [genericPolynomialTensorAlgEquiv,
      MvPolynomial.algebraTensorAlgEquiv_tmul] using hh
  exact MvPolynomial.map_injective _ (algebraMap K A).injective hmap

/-- The native polynomial tensor is a domain when the original A is a domain. -/
theorem genericPolynomialTensor_isDomain [IsDomain A] :
    IsDomain (GenericPolynomialTensor (K := K) (A := A)) :=
  MulEquiv.isDomain (MvPolynomial (Fin 3) A)
    (genericPolynomialTensorAlgEquiv (K := K) (A := A)).toMulEquiv

/-- Both domain and injectivity of the actual rational-parameter map are
DERIVED from native tensor localization. No linear-disjointness certificate. -/
theorem genericRationalTensor_isDomain_and_localization_injective [IsDomain A] :
    IsDomain (GenericRationalTensor (K := K) (A := A)) ∧
      Function.Injective (genericRationalTensorLocalizationHom (K := K) (A := A)) := by
  let S := GenericPolynomialTensor (K := K) (A := A)
  let T := GenericRationalTensor (K := K) (A := A)
  let M := (MvPolynomial (Fin 3) K)⁰
  let f := genericRationalTensorLocalizationHom (K := K) (A := A)
  letI : IsDomain S := genericPolynomialTensor_isDomain (K := K) (A := A)
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower A S T := IsScalarTower.of_algebraMap_eq (by
    intro a
    exact (f.commutes a).symm)
  have hright : (algebraMap S T).comp
      (Algebra.TensorProduct.includeRight (R := K) (A := A)).toRingHom =
      (Algebra.TensorProduct.includeRight (R := K) (A := A)).toRingHom.comp
        (algebraMap (MvPolynomial (Fin 3) K) (GenericHyperplaneField K)) := by
    apply RingHom.ext
    intro p
    change Algebra.TensorProduct.map (AlgHom.id A A)
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin 3) K) (GenericHyperplaneField K))
      (1 ⊗ₜ[K] p) = 1 ⊗ₜ[K] (algebraMap (MvPolynomial (Fin 3) K) (GenericHyperplaneField K)) p
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  letI : IsLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := K) (A := A))) T :=
    IsLocalization.tensorProduct_tensorProduct_right K A M
      (GenericHyperplaneField K) hright
  have hM : M.map (Algebra.TensorProduct.includeRight (R := K) (A := A)) ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _
      (genericPolynomialTensor_includeRight_injective (K := K) (A := A)) le_rfl
  exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors T hM,
    IsLocalization.injective T hM⟩

/-- Universal hyperplane equation in the actual original coefficient algebra. -/
def genericUniversalEquation (x : Fin 4 → A) : MvPolynomial (Fin 3) A :=
  C (x 0) + ∑ i : Fin 3, C (x i.succ) * X i

/-- Its constant value is the zeroth original coordinate. -/
theorem genericUniversalEquation_eval_zero (x : Fin 4 → A) :
    MvPolynomial.eval (fun _ => 0) (genericUniversalEquation x) = x 0 := by
  simp [genericUniversalEquation]

/-- Its parameter derivatives recover EVERY retained original coordinate. -/
theorem genericUniversalEquation_pderiv (x : Fin 4 → A) (i : Fin 3) :
    MvPolynomial.pderiv i (genericUniversalEquation x) = C (x i.succ) := by
  classical
  simp [genericUniversalEquation, map_sum, MvPolynomial.pderiv_C_mul,
    MvPolynomial.pderiv_X, Pi.single_apply]

/-- Relevance of the original coordinate tuple forces the universal equation
nonzero. This uses no nonzero zeroth-coordinate assumption. -/
theorem genericUniversalEquation_ne_zero (x : Fin 4 → A)
    (hx : ∃ j, x j ≠ 0) : genericUniversalEquation x ≠ 0 := by
  intro h
  have hzero : x 0 = 0 := by
    have he := congrArg (MvPolynomial.eval (fun _ => (0 : A))) h
    simpa only [genericUniversalEquation_eval_zero, map_zero] using he
  have hsucc (i : Fin 3) : x i.succ = 0 := by
    have hd := congrArg (MvPolynomial.pderiv i) h
    rw [genericUniversalEquation_pderiv, map_zero] at hd
    exact MvPolynomial.C_injective (Fin 3) A (hd.trans (map_zero MvPolynomial.C).symm)
  obtain ⟨j, hj⟩ := hx
  exact hj (Fin.cases hzero hsucc j)

/-- The actual generic hyperplane before parameter localization. -/
def genericPolynomialTensorHyperplane (x : Fin 4 → A) :
    GenericPolynomialTensor (K := K) (A := A) :=
  x 0 ⊗ₜ[K] 1 + ∑ i : Fin 3, x i.succ ⊗ₜ[K] X i

/-- The actual generic hyperplane after parameter localization. -/
def genericRationalTensorHyperplane (x : Fin 4 → A) :
    GenericRationalTensor (K := K) (A := A) :=
  x 0 ⊗ₜ[K] 1 + ∑ i : Fin 3,
    x i.succ ⊗ₜ[K] genericHyperplaneCoefficient (K := K) i

/-- Literal polynomial tensor and universal equation agree in the native model. -/
theorem genericPolynomialTensorHyperplane_equiv (x : Fin 4 → A) :
    genericPolynomialTensorAlgEquiv (K := K) (A := A)
      (genericPolynomialTensorHyperplane (K := K) x) = genericUniversalEquation x := by
  simp [genericPolynomialTensorAlgEquiv, genericPolynomialTensorHyperplane,
    genericUniversalEquation, MvPolynomial.algebraTensorAlgEquiv_tmul,
    MvPolynomial.smul_eq_C_mul]

/-- The localization map sends the actual universal hyperplane to exactly the
literal rational-parameter hyperplane. No equation comparison premise. -/
theorem genericPolynomialTensorHyperplane_localization (x : Fin 4 → A) :
    genericRationalTensorLocalizationHom (K := K) (A := A)
      (genericPolynomialTensorHyperplane (K := K) x) =
        genericRationalTensorHyperplane (K := K) x := by
  simp [genericRationalTensorLocalizationHom, genericPolynomialTensorHyperplane,
    genericRationalTensorHyperplane, genericHyperplaneCoefficient]

/-- The actual generic equation is nonzero in the whole rational tensor. -/
theorem genericRationalTensorHyperplane_ne_zero [IsDomain A]
    (x : Fin 4 → A) (hx : ∃ j, x j ≠ 0) :
    genericRationalTensorHyperplane (K := K) x ≠ 0 := by
  have hinj := (genericRationalTensor_isDomain_and_localization_injective
    (K := K) (A := A)).2
  intro h
  have hpoly : genericPolynomialTensorHyperplane (K := K) x = 0 := by
    apply hinj
    rw [genericPolynomialTensorHyperplane_localization, h, map_zero]
  have he := congrArg (genericPolynomialTensorAlgEquiv (K := K) (A := A)) hpoly
  rw [genericPolynomialTensorHyperplane_equiv, map_zero] at he
  exact genericUniversalEquation_ne_zero x hx he

end PfaffianDescent.Coray

/- Exported types and recursive standard axioms roots for this bounded frontier. -/
