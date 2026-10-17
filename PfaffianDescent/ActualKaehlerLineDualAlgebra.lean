import PfaffianDescent.SeparableResidueCotangentKaehlerFiber
import Mathlib.Algebra.DualNumber

/- SOURCE ONLY / UNVERIFIED. Every actual Kaehler-fiber line defines an
algebra map over the original residue evaluator. No splitting is assumed. -/
noncomputable section
namespace PfaffianDescent
open TensorProduct KaehlerDifferential TrivSqZeroExt
open scoped TensorProduct
universe u
variable {k R L : Type u} [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L] [Algebra R L] [IsScalarTower k R L]

/-- Compose the genuine universal derivation with the given fiber line. -/
def actualKaehlerLineDerivation
    (q : L ⊗[R] KaehlerDifferential k R →ₗ[L] L) : Derivation k R L :=
  ((q.restrictScalars R).comp
    (TensorProduct.mk R L (KaehlerDifferential k R) 1)).compDer
      (KaehlerDifferential.D k R)

@[simp] lemma actualKaehlerLineDerivation_apply
    (q : L ⊗[R] KaehlerDifferential k R →ₗ[L] L) (r : R) :
    actualKaehlerLineDerivation q r = q (1 ⊗ₜ[R] KaehlerDifferential.D k R r) := rfl

/-- The actual residue-plus-derivative quotient of the SAME ambient ring. -/
def actualKaehlerLineDualAlgebraMap
    (q : L ⊗[R] KaehlerDifferential k R →ₗ[L] L) : R →ₐ[k] DualNumber L where
  toFun r := inl (algebraMap R L r) + inr (actualKaehlerLineDerivation q r)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp [Derivation.map_one_eq_zero]
  map_add' r s := by apply TrivSqZeroExt.ext <;> simp [map_add]
  map_mul' r s := by
    apply TrivSqZeroExt.ext
    · simp
    · have h := (actualKaehlerLineDerivation q).leibniz r s
      simpa [DualNumber.snd_mul, Algebra.smul_def,
        TrivSqZeroExt.algebraMap_eq_inl, mul_comm] using h
  commutes' c := by
    apply TrivSqZeroExt.ext
    · simp [IsScalarTower.algebraMap_apply k R L,
        TrivSqZeroExt.algebraMap_eq_inl']
    · simp [Derivation.map_algebraMap, TrivSqZeroExt.algebraMap_eq_inl']

@[simp] lemma actualKaehlerLineDualAlgebraMap_fst
    (q : L ⊗[R] KaehlerDifferential k R →ₗ[L] L) (r : R) :
    (actualKaehlerLineDualAlgebraMap q r).fst = algebraMap R L r := by
  simp [actualKaehlerLineDualAlgebraMap]

@[simp] lemma actualKaehlerLineDualAlgebraMap_snd
    (q : L ⊗[R] KaehlerDifferential k R →ₗ[L] L) (r : R) :
    (actualKaehlerLineDualAlgebraMap q r).snd =
      q (1 ⊗ₜ[R] KaehlerDifferential.D k R r) := by
  simp [actualKaehlerLineDualAlgebraMap]

lemma actualKaehlerLineDualAlgebraMap_residue
    (q : L ⊗[R] KaehlerDifferential k R →ₗ[L] L) :
    (TrivSqZeroExt.fstHom k L L).comp (actualKaehlerLineDualAlgebraMap q) =
      IsScalarTower.toAlgHom k R L := by
  ext r
  exact actualKaehlerLineDualAlgebraMap_fst q r

end PfaffianDescent
