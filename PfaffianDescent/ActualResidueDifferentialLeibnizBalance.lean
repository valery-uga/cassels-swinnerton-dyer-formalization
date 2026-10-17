import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/- SOURCE ONLY / UNVERIFIED. Genuine universal differential at the actual
residue map. The extra derivative term vanishes on a section zero at P. -/
noncomputable section
namespace PfaffianDescent
open TensorProduct
open scoped TensorProduct
universe u
variable {K R L : Type u} [Field K] [CommRing R] [Field L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]

def actualResidueDifferentialDerivation :
    Derivation K R (L ⊗[R] KaehlerDifferential K R) :=
  (TensorProduct.mk R L (KaehlerDifferential K R) 1).compDer (KaehlerDifferential.D K R)

@[simp] lemma actualResidueDifferentialDerivation_apply (r : R) :
    actualResidueDifferentialDerivation (K := K) (R := R) (L := L) r =
      (1 : L) ⊗ₜ[R] KaehlerDifferential.D K R r := rfl

lemma actualResidueDifferential_zero_section_leibniz
    (a r : R) (hr : algebraMap R L r = 0) :
    actualResidueDifferentialDerivation (K := K) (R := R) (L := L) (a * r) =
      algebraMap R L a • actualResidueDifferentialDerivation (K := K) (R := R) (L := L) r := by
  change (1 : L) ⊗ₜ[R] KaehlerDifferential.D K R (a * r) = _
  rw [(KaehlerDifferential.D K R).leibniz, TensorProduct.tmul_add,
    ← TensorProduct.smul_tmul (R := R) a (1 : L),
    ← TensorProduct.smul_tmul (R := R) r (1 : L)]
  simp only [Algebra.smul_def, mul_one, hr, zero_tmul, add_zero]
  simp only [actualResidueDifferentialDerivation_apply, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

lemma actualResidueDifferential_zero_section_unit_compensation
    (a : Rˣ) (r : R) (hr : algebraMap R L r = 0) :
    (algebraMap R L (↑(a⁻¹) : R)) •
      actualResidueDifferentialDerivation (K := K) (R := R) (L := L) ((a : R) * r) =
        actualResidueDifferentialDerivation (K := K) (R := R) (L := L) r := by
  rw [actualResidueDifferential_zero_section_leibniz _ _ hr, smul_smul,
    ← map_mul]
  simp

end PfaffianDescent
