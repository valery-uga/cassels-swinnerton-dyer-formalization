import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeProductCoefficients
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceThreeChartEquations

/-! # Actual triple incidence equations from the actual configuration matrix -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual incidence ideal on each affine configuration--parameter chart
is the literal evaluation matrix applied to the common normalized projective
coefficient vector. All marked factor maps are constructed internally. -/
theorem serreThreePointSectionIncidenceIdeal_native_product_equations
    {K : Type u} [Field K] {X B : Scheme.{u}} [IsAffine B]
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (C : SchemeModuleFiniteFreeAffineCover M (ULift.{u} (Fin 2)))
    (b : B ⟶ Spec (.of K)) (chart : Fin 3 → C.ι)
    (markedU : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u}))
    (hmarked : ∀ i, (markedU i ≫ (C.U (chart i)).ι) ≫ base = b)
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    (serreThreePointSectionIncidenceIdeal b base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      (fun i => markedU i ≫ (C.U (chart i)).ι) hmarked
      (C.projectiveSectionLocalZeroGluedToAmbient base M)).comap
        (serreIncidenceProductChartToProduct b
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
          (finiteDimensionalProjectiveChartι K (SchemeModuleGlobalSectionsOver base M) j)) =
    Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range fun r : Fin 3 × ULift.{u} (Fin 2) =>
      ∑ k, serreIncidenceNativeParameterProductCoefficient base M b j k *
        (pullback.fst b (finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) j ≫
          schemeModuleGlobalSectionsProjectiveParametersToBase base M)).appTop
            (serreIncidenceGlobalBasisEvaluationMatrix base M C chart markedU r k))) := by
  letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  have h := serreThreePointSectionIncidenceIdeal_comap_threeCharts base M C b
    (fun i => markedU i ≫ (C.U (chart i)).ι) hmarked
    (serreIncidenceProductChartToProduct b
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      (finiteDimensionalProjectiveChartι K (SchemeModuleGlobalSectionsOver base M) j))
    (fun i => (chart i,j))
    (fun i => serreIncidenceNativeParameterProductMarked base M C b chart markedU hmarked j i)
    (fun i => serreIncidenceNativeParameterProductMarked_incidence base M C b chart markedU hmarked j i)
  refine h.trans ?_
  congr 2
  apply congrArg Set.range
  funext r
  apply Finset.sum_congr rfl
  intro k hk
  rw [serreIncidenceNativeParameterProductMarked_coefficient,
    serreIncidenceNativeParameterProductMarked_evaluation]

end PfaffianDescent
