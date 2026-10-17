import PfaffianDescent.CubicFieldChartSerreEvaluationAtChart

/-! Output data for an actual closed degree-eleven point: the actual Serre
bundle has nine sections and its actual three-component evaluation is onto.
The separate constructor builds this data from the native chart kernel. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def CubicFieldChartSerreEvaluationData
    {F L : Type u} [Field F] [Field L] [Algebra F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i] : Prop :=
    ∃ (E : Type u) (_ : Field E) (β : F →+* E),
    letI : Algebra F E := β.toAlgebra
    ∃ (j : Fin 4) (g : ChartRing (equationIdeal P hP) j →+* L)
      (hbase : g.comp (chartBaseMap (equationIdeal P hP) j) = algebraMap F L)
      (hgi : Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal P hP) j = i),
    let I := equationIdeal P hP
    let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
    let iG := cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
      cubicFieldPoint_selectedChart_isClosedImmersion P hP i j g hgi
    letI : IsClosedImmersion iG :=
      cubicFieldPoint_selectedChart_ambient_isClosedImmersion P hP i j g hgi
    CubicFieldChartSerreEvaluationAtChart (E := E) P hP ell g hbase

end PfaffianDescent
