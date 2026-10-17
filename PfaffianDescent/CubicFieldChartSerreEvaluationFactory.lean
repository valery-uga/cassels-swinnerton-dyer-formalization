import PfaffianDescent.CubicFieldChartSerreEvaluationData
import PfaffianDescent.CubicFieldChartSerreEvaluationConstructor
import PfaffianDescent.CubicFieldChartKernelData
import PfaffianDescent.CubicFieldChartSerreEvaluationKernel

/-! The actual chart kernel constructs the actual locally free Serre
extension, its exact nine-dimensional section space, and actual rank six.
There is no supplied bundle, cover, section rank, or evaluation certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldChartSerreEvaluationData_of_native_kernel
    {F L : Type u} [Field F] [CharZero F] [Field L] [Algebra F L]
    [FiniteDimensional F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    (i : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase P hP = Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (hL : finrank F L = 11)
    (hdata : CubicFieldChartKernelData P hP i) :
    CubicFieldChartSerreEvaluationData P hP i := by
  classical
  rcases hdata with ⟨E, hE, β, hdata⟩
  letI : Field E := hE
  letI : Algebra F E := β.toAlgebra
  rcases hdata with ⟨j, g, α, y, J, hbase, hgi, hnz, hcoords, _,
    hresidue, hzero, hfull, hmem, _, hker, _⟩
  have hChart := cubicFieldChartSerreEvaluationAtChart_of_native_kernel_witnesses
    P hP hP0 i hi hL j g hbase hgi α y J hnz hcoords hresidue hzero hfull hmem hker
  exact cubicFieldChartSerreEvaluationData_of_witnesses P hP i β j g hbase hgi hChart

end PfaffianDescent
