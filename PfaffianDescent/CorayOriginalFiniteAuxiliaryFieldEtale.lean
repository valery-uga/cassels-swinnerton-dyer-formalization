import PfaffianDescent.CorayOriginalFiniteEtaleKernelDescent
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Field.IsField

noncomputable section
namespace PfaffianDescent.Coray
open TensorProduct
universe u
set_option autoImplicit false

/-- The ACTUAL original auxiliary algebra that is a finite field over
characteristic-zero K is finite etale, using its EXISTING ring and K action.
The field structure reuses the original ring; separability is derived from
finite algebraicity and perfect original K, not supplied. -/
theorem originalFiniteAuxiliaryAlgebra_isField_finiteType_formallyEtale001
    {K A : Type u} [Field K] [CharZero K] [CommRing A]
    [Algebra K A] [Module.Finite K A] (hField : IsField A) :
    Algebra.FiniteType K A ∧ Algebra.FormallyEtale K A := by
  letI : Field A := hField.toField
  letI : Algebra.IsSeparable K A := inferInstance
  exact ⟨inferInstance, Algebra.FormallyEtale.of_isSeparable K A⟩

/-- The SAME actual rank3 original auxiliary algebra has exactly three
geometric points after scalar extension. Neither finite etaleness nor
cardinality/list of conjugates is supplied as an outcome premise. -/
theorem originalFiniteAuxiliaryAlgebra_isField_rankThree_geometricPoints_natCard_three001
    {K A M : Type u} [Field K] [CharZero K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Module.Finite K A] [IsSepClosed M]
    (hField : IsField A) (hRank : Module.finrank K A = 3) :
    Nat.card (PrimeSpectrum (M ⊗[K] A)) = 3 := by
  obtain ⟨hFT, hEtale⟩ := originalFiniteAuxiliaryAlgebra_isField_finiteType_formallyEtale001 (K := K) hField
  letI : Algebra.FiniteType K A := hFT
  letI : Algebra.FormallyEtale K A := hEtale
  exact (originalFiniteEtaleGeometricPoints_natCard_eq_originalFinrank001
    (K := K) (A := A) (M := M)).trans hRank

end PfaffianDescent.Coray
