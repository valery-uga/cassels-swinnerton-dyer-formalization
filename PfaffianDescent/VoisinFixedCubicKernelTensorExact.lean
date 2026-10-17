import PfaffianDescent.ProjectiveChartKernelTensorExact
import PfaffianDescent.VoisinFixedCubicCoordinateFlat
import PfaffianDescent.QuotientChartKernel

/-!
# Exact fibre ideals for the moving cubic on a fixed cubic surface

At a local parameter point where the moving cubic is regular on the
residue-field fixed cubic, the intersection charts are flat. Thus their
principal equation ideals remain embedded after any further parameter
change, including closed and residue-field fibres.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual moving-cubic chart ideal remains embedded after arbitrary
parameter tensor change. No flatness of the parameter change is needed. -/
theorem fixedCubicIntersectionChart_kernel_lTensor_injective_of_residue_regular
    {K T B : Type u} [Field K] [CommRing T] [Algebra K T] [IsLocalRing T]
    [AddCommGroup B] [Module T B]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) T) (hp : p.IsHomogeneous 3)
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal
      (p.map (algebraMap T (IsLocalRing.ResidueField T)))))
    (j : Fin 4) :
    let J := equationIdeal (a.map (algebraMap K T))
      (ha.map (algebraMap K T))
    let hIJ : J.toIdeal ≤ (J ⊔ equationIdeal p hp).toIdeal := by
      rw [HomogeneousIdeal.toIdeal_sup]
      exact le_sup_left
    let chartIdeal := RingHom.ker
      (chartQuotientMap J (J ⊔ equationIdeal p hp) hIJ j)
    letI : Algebra T (ChartRing J j) := (chartBaseMap J j).toAlgebra
    letI : SMul T (ChartRing J j) := Algebra.toSMul
    letI : Module T (ChartRing J j) := Algebra.toModule
    Function.Injective
      (((chartIdeal.restrictScalars T).subtype).lTensor B) := by
  let J := equationIdeal (a.map (algebraMap K T))
    (ha.map (algebraMap K T))
  let hIJ : J.toIdeal ≤ (J ⊔ equationIdeal p hp).toIdeal := by
    rw [HomogeneousIdeal.toIdeal_sup]
    exact le_sup_left
  exact chartQuotientMap_kernel_lTensor_injective_of_flat
    J (J ⊔ equationIdeal p hp) hIJ j
    (fixedCubicIntersectionChart_flat_of_residue_regular a ha p hp hreg j)

end PfaffianDescent
