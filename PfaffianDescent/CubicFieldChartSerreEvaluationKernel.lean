import PfaffianDescent.CubicFieldChartSerreEvaluationConstructor
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodNativeBundle
import PfaffianDescent.SerreSectionSequenceDimension

/-! Actual Serre evaluation from fixed native chart-kernel witnesses.
The outer factory obtains these witnesses from the actual kernel data. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldChartSerreEvaluationAtChart_of_native_kernel_witnesses
    {F L E : Type u} [Field F] [CharZero F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] [FiniteDimensional F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    (i : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase P hP = Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (hL : finrank F L = 11)
    (j : Fin 4) (g : ChartRing (equationIdeal P hP) j →+* L)
    (hbase : g.comp (chartBaseMap (equationIdeal P hP) j) = algebraMap F L)
    (hgi : Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal P hP) j = i)
    (α : Fin 11 → (L →ₐ[F] E)) (y : Fin 11 → Fin 4 → E)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet E)
    (hnz : ∀ k, y k j ≠ 0)
    (hcoords : ∀ k r, α k (g (linearChartCoordinate (equationIdeal P hP)
        (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) r)) =
      (y k j)⁻¹ * y k r)
    (hresidue : ∀ k r, (J k r).fst = y (k.castAdd 8) r)
    (hzero : ∀ k, aeval (J k) (P.map (algebraMap F E)) = 0)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction y J))
    (hmem : ∀ q, cubicHomogeneousChartRestriction (equationIdeal P hP)
        (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g q = 0 →
      cubicElevenPointValueRestriction y
        (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) q) = 0)
    (hker : finrank F (cubicHomogeneousChartRestriction (equationIdeal P hP)
      (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g).ker = 9) :
    let I := equationIdeal P hP
    let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
    let iG := cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
      cubicFieldPoint_selectedChart_isClosedImmersion P hP i j g hgi
    letI : IsClosedImmersion iG :=
      cubicFieldPoint_selectedChart_ambient_isClosedImmersion P hP i j g hgi
    CubicFieldChartSerreEvaluationAtChart (E := E) P hP ell g hbase := by
  let I := equationIdeal P hP
  let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let iG := cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
    cubicFieldPoint_selectedChart_isClosedImmersion P hP i j g hgi
  letI : IsClosedImmersion iG :=
    cubicFieldPoint_selectedChart_ambient_isClosedImmersion P hP i j g hgi
  letI : HasExt.{u} (hypersurface P hP).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (Proj (grading I)).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) F)).Modules := schemeModules_hasExt _
  letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits I 3
  letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits I 3
  obtain ⟨e₀, hne, h9⟩ := cubicFieldPointChartSerre_exists_sequence_nine
    P hP hP0 i hi j g hbase hgi hL hker
  obtain ⟨e, C, heq⟩ :=
    cubicClosedPointSerreFreeNeighborhood_native_exists_bundle_cover F P hP hP0 iG e₀ hne
  have hne' : SerreConnectingProductNonzero iG (positiveSheafOfModules (grading I) 3)
      e.toSequenceData := by
    rw [heq]
    exact hne
  obtain ⟨φ, hres, honto, hbij⟩ :=
    cubicElevenPoint_groundChart_exists_actualSerreEvaluation_surjective
      P hP hP0 j g hbase e C α y hnz hcoords J hresidue hzero hfull
      (le_of_eq hL) hmem hker
  have hEval := cubicFieldChartSerreBundleEvaluation_of_witnesses I ell g hbase e.E
    e.projection φ (fun k => α (k.castAdd 8)) hres honto hbij
  have h9' := serreSection_finrank_of_sequence_eq (hypersurfaceToBase P hP) e e₀ heq h9
  exact cubicFieldChartSerreEvaluationAtChart_of_witnesses P hP ell g hbase e C hne' h9' hEval

end PfaffianDescent
