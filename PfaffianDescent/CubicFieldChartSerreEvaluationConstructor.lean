import PfaffianDescent.CubicFieldChartSerreEvaluationData

/-! An opaque packaging theorem for literal Serre evaluation witnesses.
This only packages witnesses; the native factory constructs them. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldChartSerreEvaluationData_of_witnesses
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i]
    (β : F →+* E) (j : Fin 4) (g : ChartRing (equationIdeal P hP) j →+* L)
    (hbase : g.comp (chartBaseMap (equationIdeal P hP) j) = algebraMap F L)
    (hgi : Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal P hP) j = i) :
    letI : Algebra F E := β.toAlgebra
    let I := equationIdeal P hP
    let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
    let iG := cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
      cubicFieldPoint_selectedChart_isClosedImmersion P hP i j g hgi
    letI : IsClosedImmersion iG :=
      cubicFieldPoint_selectedChart_ambient_isClosedImmersion P hP i j g hgi
    CubicFieldChartSerreEvaluationAtChart (E := E) P hP ell g hbase →
      CubicFieldChartSerreEvaluationData P hP i := by
  dsimp only
  intro hChart
  exact ⟨E, inferInstance, β, j, g, hbase, hgi, hChart⟩

end PfaffianDescent
