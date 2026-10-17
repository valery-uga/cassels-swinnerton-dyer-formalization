import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionUniversalReindex
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceParameterRankChartMap
import PfaffianDescent.SchemeAffineFunctions

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The inverse actual rank-chart equivalence retains the literal reindexed coordinate. -/
theorem pointSplittingCubicSerreGroundChosenSection_rankChart_coordinate_symm
    (K : Type u) [CommRing K] {r n : ℕ} (hn : r = n) (j : Fin r) (i : Fin n) :
    (serreIncidenceParameterRankChartEquiv K hn j).symm
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
        ((finCongr hn) j) i) =
    chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin r) K))
      j ((finCongr hn).symm i) := by
  apply (serreIncidenceParameterRankChartEquiv K hn j).injective
  rw [RingEquiv.apply_symm_apply, serreIncidenceParameterRankChart_coordinate,
    Equiv.apply_symm_apply]

/-- Actual rank-n parameter-chart map of an arbitrary genuine product-chart map. -/
def pointSplittingCubicSerreGroundChosenSection_parameterRankChartMap
    {K : Type u} [Field K] {X T : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    {n : ℕ} (hn : Module.finrank K (SchemeModuleGlobalSectionsOver base M) = n)
    (f : T ⟶ (C.projectiveSectionOpenCover base M).X ij) :
    T ⟶ Spec (.of (ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      ((finCongr hn) ij.2))) :=
  f ≫ C.projectiveSectionOpenCoverToParameterChart base M ij ≫
    Spec.map (CommRingCat.ofHom
      (serreIncidenceParameterRankChartEquiv K hn ij.2).symm.toRingHom)

/-- The actual local coefficient pulled to an arbitrary source is its literal affine coordinate function. -/
theorem pointSplittingCubicSerreGroundChosenSection_localCoefficient_affine
    {K : Type u} [Field K] {X T : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (f : T ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    f.appTop (C.projectiveSectionLocalCoefficient base M ij i) =
    affineFunctionHom (f ≫ C.projectiveSectionOpenCoverToParameterChart base M ij)
      (chartCoordinate (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) ij.2 i) := by
  rw [affineFunctionHom_comp]
  rfl

/-- Actual reindexed old local coefficients equal the natural rank-n chart coordinates,
with no supplied point, section or coordinate comparison. -/
theorem pointSplittingCubicSerreGroundChosenSection_parameterRankChart_coefficient
    {K : Type u} [Field K] {X T : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    {n : ℕ} (hn : Module.finrank K (SchemeModuleGlobalSectionsOver base M) = n)
    (f : T ⟶ (C.projectiveSectionOpenCover base M).X ij) (i : Fin n) :
    f.appTop (C.projectiveSectionLocalCoefficient base M ij ((finCongr hn).symm i)) =
    affineFunctionHom
      (pointSplittingCubicSerreGroundChosenSection_parameterRankChartMap base M C ij hn f)
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
        ((finCongr hn) ij.2) i) := by
  rw [pointSplittingCubicSerreGroundChosenSection_localCoefficient_affine]
  symm
  unfold pointSplittingCubicSerreGroundChosenSection_parameterRankChartMap
  rw [← Category.assoc, affineFunctionHom_comp_Spec]
  change affineFunctionHom (f ≫ C.projectiveSectionOpenCoverToParameterChart base M ij)
    ((serreIncidenceParameterRankChartEquiv K hn ij.2).symm
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
        ((finCongr hn) ij.2) i)) = _
  rw [pointSplittingCubicSerreGroundChosenSection_rankChart_coordinate_symm]

/-- The actual rank-chart map recovers the actual original parameter projection,
followed by its true rank parameter isomorphism. -/
theorem pointSplittingCubicSerreGroundChosenSection_parameterRankChartMap_chartι
    {K : Type u} [Field K] {X T : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    {n : ℕ} (hn : Module.finrank K (SchemeModuleGlobalSectionsOver base M) = n)
    (f : T ⟶ (C.projectiveSectionOpenCover base M).X ij) :
    pointSplittingCubicSerreGroundChosenSection_parameterRankChartMap base M C ij hn f ≫
      chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) ((finCongr hn) ij.2) =
    f ≫ (C.projectiveSectionOpenCover base M).f ij ≫
      pullback.snd base (schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫
      (serreIncidenceParameterRankIso K hn).hom := by
  unfold pointSplittingCubicSerreGroundChosenSection_parameterRankChartMap
  simp only [Category.assoc]
  rw [← serreIncidenceParameterRankChart_map]
  have h := C.projectiveSectionOpenCover_f_comp_ambientSnd base M ij
  have hh := congrArg (fun g => f ≫ g ≫ (serreIncidenceParameterRankIso K hn).hom) h
  simpa only [Category.assoc, finiteDimensionalProjectiveChartι,
    finiteDimensionalProjectiveIdeal] using hh.symm

end PfaffianDescent
