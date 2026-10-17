import PfaffianDescent.ActualResidueDualJetDifferentialKernel

/- SOURCE ONLY / UNVERIFIED. AUXILIARY linear calculation for an actual
space of vanishing sections. The eventual H0 caller must derive its residue
vanishing internally; this is not a final geometric comparison premise. -/
noncomputable section
namespace PfaffianDescent
open TensorProduct
universe u v
variable {K R L : Type u} [Field K] [CommRing R] [Field L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]
  {V : Type v} [AddCommGroup V] [Module K V]

def actualQuadraticDifferentialRestriction (a : V →ₗ[K] R) :
    V →ₗ[K] (L ⊗[R] KaehlerDifferential K R) :=
  (actualResidueDifferentialDerivation (K := K) (R := R) (L := L)).toLinearMap.comp a

theorem actualQuadraticDifferentialRestriction_jet_kernel
    (a : V →ₗ[K] R) (ha : ∀ v, algebraMap R L (a v) = 0)
    (ell : L ⊗[R] KaehlerDifferential K R →ₗ[L] L) :
    LinearMap.ker ((actualKaehlerLineDualAlgebraMap ell).toLinearMap.comp a) =
      LinearMap.ker ((ell.restrictScalars K).comp (actualQuadraticDifferentialRestriction a)) := by
  ext v
  exact actualResidueDualJet_zero_iff_on_vanishing_section ell (a v) (ha v)

end PfaffianDescent
