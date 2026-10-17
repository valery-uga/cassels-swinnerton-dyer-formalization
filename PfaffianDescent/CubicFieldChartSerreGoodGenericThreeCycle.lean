import PfaffianDescent.CubicFieldChartSerreGoodData
import PfaffianDescent.SerreActualCubicGroundFamilyNativeSelectedResidualCycle
import PfaffianDescent.CubicFieldPointChartClosedImmersion
import PfaffianDescent.CubicGenericThreeEffectiveEightType

/-! Actual closed-eleven good Serre data produce the inner generic-three
cycle. The original generic-eleven caller constructs every premise internally. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldChartSerreGoodData_genericThree_effectiveEight
    {F L : Type u} [Field F] [CharZero F] [Field L] [Algebra F L]
    [FiniteDimensional F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (P0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    (i₁₁ : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i₁₁]
    (hi₁₁ : i₁₁ ≫ hypersurfaceToBase P hP = Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (hL : finrank F L = 11)
    (hGood : CubicFieldChartSerreGoodData P hP i₁₁) :
    CubicGenericThreeEffectiveEightType P hP := by
  letI : Infinite F := CharZero.infinite F
  let base := hypersurfaceToBase P hP
  -- Unpack the SAME actual generic11 good datum. The witnesses now are
  -- opaque local variables instead of recursively reduced choose_spec terms.
  change CubicFieldChartSerreGoodData (F := F) (L := L) P hP i₁₁ at hGood
  obtain ⟨E₀, hE₀, β₀, hChartData⟩ := hGood
  letI : Field E₀ := hE₀
  letI : Algebra F E₀ := β₀.toAlgebra
  obtain ⟨j, g, hbase, hgi, hChart⟩ := hChartData
  let I := equationIdeal P hP
  let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let iG := cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g
  let hSame := cubicFieldPoint_selectedChart_ambient_eq P hP i₁₁ j g hgi
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
    cubicFieldPoint_selectedChart_isClosedImmersion P hP i₁₁ j g hgi
  letI : IsClosedImmersion iG :=
    cubicFieldPoint_selectedChart_ambient_isClosedImmersion P hP i₁₁ j g hgi
  let hiG := (congrArg (fun i => i ≫ base) hSame).trans hi₁₁
  letI : HasExt.{u} (hypersurface P hP).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (Proj (grading I)).Modules := schemeModules_hasExt _
  letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits I 3
  letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits I 3
  obtain ⟨e, C, h9, hConnecting, hEvaluation, hGenericGood⟩ := hChart
  letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver base e.E) :=
    Module.finite_of_finrank_pos (by rw [h9]; decide)
  obtain ⟨Rk, aRank, chart, markedU, hm, hAffine, hIntegral,
    hOpen, hmarked, minor, hminor, hPlane, hInitial⟩ := hGenericGood
  letI : IsAffine Rk := hAffine
  letI : IsIntegral Rk := hIntegral
  letI : IsOpenImmersion aRank := hOpen
  letI : Nonempty (orderedFamilyConfigurationOver base 3).left :=
    ⟨aRank (genericPoint Rk)⟩
  letI : IsSeparated base := isSeparated_homogeneousToBase (equationIdeal P hP)
  letI : Flat base := inferInstance
  letI : UniversallyOpen base := inferInstance
  letI : LocallyOfFiniteType base := inferInstance
  letI : GeometricallyIntegral base :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_infinite P hP P0
  letI : IsIntegral (orderedFamilyConfigurationOver base 3).left :=
    isIntegral_orderedFamilyConfigurationOver_of_geometricallyIntegral base 3
  letI : GeometricallyIntegral (toBase I) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_infinite P hP P0
  letI : Flat (toBase I) := inferInstance
  letI : UniversallyOpen (toBase I) := inferInstance
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  letI : Nonempty (orderedFamilyConfigurationOver (toBase I) 3).left := by
    change Nonempty (orderedFamilyConfigurationOver base 3).left
    infer_instance
  let hB₃ : IsIntegral (cubicConfigurationBase P hP 3) :=
    isIntegral_cubicConfigurationBase_of_geometricallyIntegral P hP 3
  letI := hB₃
  let a₃ : CommRingCat.of F ⟶ CommRingCat.of (cubicConfigurationBase P hP 3).functionField :=
    Spec.preimage (cubicConfigurationGenericBaseMap P hP 3 ≫ cubicConfigurationToBase P hP 3)
  let ha₃ : Spec.map a₃ = cubicConfigurationGenericBaseMap P hP 3 ≫
      cubicConfigurationToBase P hP 3 := Spec.map_preimage _
  obtain ⟨z₈, hDegree⟩ :=
    serreActualCubicGroundFamily_retainedGenericGood_nativeSelectedEffectiveEight
      (K := F) (L := L)
      P hP P0 a₃ ha₃ iG hiG hL e C h9 aRank chart markedU hmarked minor hminor hInitial
  unfold CubicGenericThreeEffectiveEightType
  exact Exists.intro hB₃ (Exists.intro a₃ (Exists.intro ha₃ (Exists.intro z₈ hDegree)))

end PfaffianDescent
