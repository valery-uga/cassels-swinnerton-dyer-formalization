import PfaffianDescent.IncidenceSectionCoefficients
import PfaffianDescent.IncidenceChartSectionFormula
import PfaffianDescent.IncidenceFiberChartPoints
import PfaffianDescent.IncidenceKernelSheafCoordinatesInverse

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
section
variable (K : Type u) [CommRing K] (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (U : (grassmannianScheme K 3 3).Opens) (hU : U ≤ (grassmannianChartι K σ).opensRange)
    (s : IncidenceSchemeSections K U)

noncomputable def incidenceOpenSectionChartLift : U.toScheme ⟶ incidenceGraphScheme K :=
  incidenceSectionChartLift K σ (grassmannianOpenChartLift K σ U hU) s.1
    (s.2.trans (grassmannianOpenChartLift_fac K σ U hU).symm)

noncomputable def incidenceOpenSectionChartPoint : IncidenceGraphPoints Γ(U.toScheme, ⊤) :=
  incidenceChartPoint K (incidenceOpenSectionChartLift K σ U hU s)

lemma incidenceSchemeSectionFunctions_chartPoint :
    incidenceSchemeSectionFunctions K σ U hU s =
      U.topIso.hom.hom ∘ (fun i : IncidenceFiberIndex => incidenceGraphPointCoordinates Γ(U.toScheme, ⊤)
        (incidenceOpenSectionChartPoint K σ U hU s) (Sum.inr i)) := by
  funext i
  change U.topIso.hom (incidenceChartSectionCoordinates K σ (grassmannianOpenChartLift K σ U hU)
    ⟨s.1, s.2.trans (grassmannianOpenChartLift_fac K σ U hU).symm⟩ i) = _
  exact congrArg U.topIso.hom (incidenceChartSectionCoordinates_apply K σ
    (grassmannianOpenChartLift K σ U hU) _ i)

lemma incidenceOpenChartMatrix_sectionPoint :
    incidenceOpenChartMatrix K σ U hU =
      (LinearMap.toMatrix' (incidenceOpenSectionChartPoint K σ U hU s).1).map U.topIso.hom.hom := by
  have ha : incidenceOpenSectionChartLift K σ U hU s ≫ incidenceGraphToGrassmannianChart K =
      grassmannianOpenChartLift K σ U hU := incidenceSectionChartLift_toGraph K σ _ _ _
  have h : grassmannianChartFunctions K (grassmannianOpenChartLift K σ U hU) =
      LinearMap.toMatrix' (incidenceOpenSectionChartPoint K σ U hU s).1 :=
    (congrArg (grassmannianChartMatrix K) ha.symm).trans
      (incidenceGraphToGrassmannianChart_matrix K (incidenceOpenSectionChartLift K σ U hU s))
  exact congrArg (fun T => T.map U.topIso.hom.hom) h

lemma incidenceSchemeSectionCoefficients_chartPoint :
    incidenceSchemeSectionCoefficients K U s =
      U.topIso.hom.hom ∘ incidenceOriginalCoefficients σ (incidenceOpenSectionChartPoint K σ U hU s) := by
  let a := incidenceOpenSectionChartLift K σ U hU s
  have ha : a ≫ incidenceChartι K σ = s.1 := incidenceSectionChartLift_toIncidence K σ _ _ _
  have hb : a ≫ incidenceChartToTriples K σ = s.1 ≫ incidenceToTriples K :=
    (congrArg (fun f => a ≫ f) (incidenceChartι_toTriples K σ).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ incidenceToTriples K) ha))
  funext i
  change U.topIso.hom (affineFunctionHom (s.1 ≫ incidenceToTriples K) (MvPolynomial.X i)) = _
  exact congrArg U.topIso.hom
    ((congrArg (fun f => affineFunctionHom f (MvPolynomial.X i)) hb.symm).trans
      (incidenceChartToTriples_coordinates K σ a i))

/-- The local total-space correspondence preserves the actual ambient alternating forms. -/
theorem incidenceSchemeKernelSectionsOnChart_coefficients :
    (incidenceKernelSheafι K).val.app (op U) (incidenceSchemeKernelSectionsOnChart K σ U hU s) =
      incidenceSchemeSectionCoefficients K U s := by
  change (incidenceKernelSheafι K).val.app (op U)
    ((incidenceKernelSheafOpenSectionsEquiv K σ U hU).symm (incidenceSchemeSectionFunctions K σ U hU s)) = _
  rw [incidenceKernelSheafOpenSectionsEquiv_symm_val,
    incidenceOpenChartMatrix_sectionPoint K σ U hU s, incidenceSchemeSectionFunctions_chartPoint,
    incidenceFiberInclusion_map, incidenceFiberInclusion_original]
  exact (incidenceSchemeSectionCoefficients_chartPoint K σ U hU s).symm

end
end PfaffianDescent
