import PfaffianDescent.ActualResidueDifferentialLeibnizBalance
import PfaffianDescent.ActualKaehlerLineDualAlgebra

/- SOURCE ONLY / UNVERIFIED. Literal original ring quotient retains the
residue and derivative. No desired kernel/jet comparison is an input. -/
noncomputable section
namespace PfaffianDescent
open TensorProduct
open scoped TensorProduct
universe u
variable {K R L : Type u} [Field K] [CommRing R] [Field L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]

theorem actualResidueDualJet_zero_iff
    (ell : L ⊗[R] KaehlerDifferential K R →ₗ[L] L) (r : R) :
    actualKaehlerLineDualAlgebraMap ell r = 0 ↔
      algebraMap R L r = 0 ∧
        ell (actualResidueDifferentialDerivation (K := K) (R := R) (L := L) r) = 0 := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg TrivSqZeroExt.fst h,
      by simpa using congrArg TrivSqZeroExt.snd h⟩
  · rintro ⟨hf, hs⟩
    apply TrivSqZeroExt.ext
    · simpa using hf
    · simpa using hs

theorem actualResidueDualJet_zero_iff_on_vanishing_section
    (ell : L ⊗[R] KaehlerDifferential K R →ₗ[L] L) (r : R)
    (hr : algebraMap R L r = 0) :
    actualKaehlerLineDualAlgebraMap ell r = 0 ↔
      ell (actualResidueDifferentialDerivation (K := K) (R := R) (L := L) r) = 0 := by
  rw [actualResidueDualJet_zero_iff]
  exact and_iff_right hr

end PfaffianDescent
