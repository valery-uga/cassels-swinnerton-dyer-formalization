import PfaffianDescent.CorayOriginalFiniteAuxiliaryFieldEtale
import Mathlib.SetTheory.Cardinal.NatCard

noncomputable section
namespace PfaffianDescent.Coray
open TensorProduct
universe u
set_option autoImplicit false

/-- The literal original auxiliary finite algebra's field and rank3
outputs construct an enumeration of ALL geometric points. The actual
cardinality follows from derived separability/etaleness, and finiteness
follows from cardinal positivity. No point, enumeration or conjugate list
is supplied. -/
theorem originalFiniteAuxiliaryAlgebra_isField_rankThree_exists_actualGeometricEnumeration001
    {K A M : Type u} [Field K] [CharZero K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Module.Finite K A] [IsSepClosed M]
    (hField : IsField A) (hRank : Module.finrank K A = 3) :
    Nonempty (Fin 3 ≃ PrimeSpectrum (M ⊗[K] A)) := by
  have hCard : Nat.card (PrimeSpectrum (M ⊗[K] A)) = 3 :=
    originalFiniteAuxiliaryAlgebra_isField_rankThree_geometricPoints_natCard_three001 (K := K) hField hRank
  have hPositive : 0 < Nat.card (PrimeSpectrum (M ⊗[K] A)) := by rw [hCard]; decide
  letI : Finite (PrimeSpectrum (M ⊗[K] A)) := (Nat.card_pos_iff.mp hPositive).2
  exact ⟨(Finite.equivFinOfCardEq hCard).symm⟩

end PfaffianDescent.Coray
