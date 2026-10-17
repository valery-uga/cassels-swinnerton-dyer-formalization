import PfaffianDescent.CubicFieldChartSerreRankData

/-! Actual Serre evaluation data constructs its actual principal
configuration rank chart without another rank or integrality input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldChartSerreRankData_of_actual_evaluation
    {F L : Type u} [Field F] [CharZero F] [Field L] [Algebra F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    (i : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i]
    (hdata : CubicFieldChartSerreEvaluationData P hP i) :
    CubicFieldChartSerreRankData P hP i := by
  obtain ⟨E, hE, β, hdata⟩ := hdata
  letI : Field E := hE
  letI : Algebra F E := β.toAlgebra
  obtain ⟨j, g, hbase, hgi, hEval⟩ := hdata
  let I := equationIdeal P hP
  let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let iG := cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
    cubicFieldPoint_selectedChart_isClosedImmersion P hP i j g hgi
  letI : IsClosedImmersion iG :=
    cubicFieldPoint_selectedChart_ambient_isClosedImmersion P hP i j g hgi
  have hRank := cubicFieldChartSerreRankAtChart_of_actual_evaluation P hP hP0 ell g hbase hEval
  exact cubicFieldChartSerreRankData_of_witnesses P hP i β j g hbase hgi hRank

end PfaffianDescent
