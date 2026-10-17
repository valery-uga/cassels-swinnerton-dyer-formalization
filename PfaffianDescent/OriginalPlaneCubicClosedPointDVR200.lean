import PfaffianDescent.PlaneCubicSectionCokernelZeroCycle172
import PfaffianDescent.CorayNormalizationClosedPointNongeneric
import PfaffianDescent.CorayPlaneCubicJacobianSmooth
import PfaffianDescent.CorayActualGenericPlaneCubicIntegral

/-! SOURCE ONLY200. Original smooth integral plane-cubic closed points
are nongeneric and DVR. No Kaehler basis or normalization is constructed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ORIGINAL integral plane cubic has more than one point. A singleton
would make an original normalized chart a field, contradicted by its literal
three-variable/two-equation presentation. -/
lemma integralPlaneCubic_not_subsingleton200
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 3)
    [IsIntegral (hypersurface q hq)] : ¬ Subsingleton (hypersurface q hq) := by
  let C := hypersurface q hq
  let I := equationIdeal q hq
  letI : IsIntegral (scheme I) := by
    change IsIntegral (hypersurface q hq)
    infer_instance
  intro hsingle
  letI : Subsingleton C := hsingle
  letI : Subsingleton (scheme I) := by
    change Subsingleton C
    exact hsingle
  obtain ⟨j, z, _⟩ := exists_coordinate_chart I (genericPoint C)
  let A := ChartRing I j
  letI : Algebra K A := (chartBaseMap I j).toAlgebra
  let Y := Spec (.of A)
  letI : Nonempty Y := ⟨z⟩
  letI : IsIntegral Y := isIntegral_of_isOpenImmersion (chartι I j)
  letI : Subsingleton Y := ⟨fun s t =>
    (chartι I j).isOpenEmbedding.injective (Subsingleton.elim _ _)⟩
  have hsections : IsField Γ(Y, ⊤) := isField_of_isIntegral_of_subsingleton Y
  have hchart : IsField A := MulEquiv.isField hsections
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.toMulEquiv
  have hrange : Ideal.span (Set.range (plane_hypersurfaceChartRelations q j)) =
      Ideal.span ({q, X j - 1} : Set (MvPolynomial (Fin 3) K)) :=
    congrArg Ideal.span (plane_range_hypersurfaceChartRelations q j)
  let e : A ≃+* (MvPolynomial (Fin 3) K ⧸ Ideal.span ({q, X j - 1} : Set _)) :=
    (plane_hypersurfaceChartRelationsEquiv q hq j).toRingEquiv.symm.trans
      (Ideal.quotEquivOfEq hrange)
  exact affineThreeSpace_pairQuotient_not_isField q (X j - 1)
    (MulEquiv.isField hchart e.symm.toMulEquiv)

/-- Closed-point nongenericity on the SAME original curve is derived,
without passing to a normalization or assuming a positive-dimensional stalk. -/
lemma integralPlaneCubic_closedPoint_ne_generic200
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 3)
    [IsIntegral (hypersurface q hq)] (P : closedPoints (hypersurface q hq)) :
    P.1 ≠ genericPoint (hypersurface q hq) := by
  let C := hypersurface q hq
  intro hP
  have hclosedP : IsClosed ({P.1} : Set C) := P.2
  have hclosed : IsClosed ({genericPoint C} : Set C) := by
    simpa only [hP] using hclosedP
  have hall : (Set.univ : Set C) = {genericPoint C} :=
    (genericPoint_spec C).symm.trans hclosed.closure_eq
  have hsingle : Subsingleton C := ⟨fun s t => by
    have hs : s = genericPoint C := Set.mem_singleton_iff.mp (hall ▸ Set.mem_univ s)
    have ht : t = genericPoint C := Set.mem_singleton_iff.mp (hall ▸ Set.mem_univ t)
    exact hs.trans ht.symm⟩
  exact integralPlaneCubic_not_subsingleton200 q hq hsingle

/-- Existing172 derives the ORIGINAL DVR from native regularity and
Krull dimension. This caller derives its missing nongenericity hypothesis. -/
theorem smoothIntegralPlaneCubic_closedPoint_stalk_isDVR200
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 3) (hq0 : q ≠ 0)
    [Smooth (hypersurfaceToBase q hq)] [IsIntegral (hypersurface q hq)]
    (P : closedPoints (hypersurface q hq)) :
    IsDiscreteValuationRing ((hypersurface q hq).presheaf.stalk P.1) := by
  letI : IsIntegral (scheme (equationIdeal q hq)) := by
    change IsIntegral (hypersurface q hq)
    infer_instance
  exact planeCubic_original_nongeneric_stalk_isDVR172 q hq hq0 P.1
    (integralPlaneCubic_closedPoint_ne_generic200 q hq P)

/-- Every closed point of the SAME generic-plane cubic has an actual DVR
stalk, solely from the original nonzero smooth cubic over ANY field. -/
theorem smoothCubic_actualGenericPlaneCubic_closedPoint_stalk_isDVR200
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints
      (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp))) :
    letI : IsIntegral
      (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
        smoothCubic_actualGenericPlaneCubic_isIntegral p hp hp0
    IsDiscreteValuationRing
      ((hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)).presheaf.stalk P.1) := by
  letI : Smooth (hypersurfaceToBase (genericPlaneCubic p)
      (genericPlaneCubic_isHomogeneous p hp)) :=
    smoothCubic_actualGenericPlaneCubic_smooth p hp hp0
  letI : IsIntegral
      (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
    smoothCubic_actualGenericPlaneCubic_isIntegral p hp hp0
  exact smoothIntegralPlaneCubic_closedPoint_stalk_isDVR200 _ _
    (genericPlaneCubic_ne_zero p hp hp0) P

end PfaffianDescent.Coray
