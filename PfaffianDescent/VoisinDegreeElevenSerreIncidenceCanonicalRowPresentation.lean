import PfaffianDescent.VoisinDegreeElevenSerreIncidenceRankChartEquationTransport
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeProductEquations

/-! # The actual bundle incidence supplies its literal normalized evaluation rows -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreThreePointSectionIncidenceIdeal_rank_rows
    {K : Type u} [Field K] {X B : Scheme.{u}} [IsAffine B]
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (C : SchemeModuleFiniteFreeAffineCover M (ULift.{u} (Fin 2)))
    (b : B ⟶ Spec (.of K)) (chart : Fin 3 → C.ι)
    (markedU : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u}))
    (hmarked : ∀ i, (markedU i ≫ (C.U (chart i)).ι) ≫ base = b)
    (ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2)))
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    (serreThreePointSectionIncidenceIdeal b base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      (fun i => markedU i ≫ (C.U (chart i)).ι) hmarked
      (C.projectiveSectionLocalZeroGluedToAmbient base M)).comap
        (serreIncidenceRankProductChart b j) =
    Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range
      (serreIncidenceRankProductRow b j (fun r k =>
        serreIncidenceGlobalBasisEvaluationMatrix base M C chart markedU (ρ r) k)))) := by
  letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  have h := serreThreePointSectionIncidenceIdeal_native_product_equations
    base M C b chart markedU hmarked j
  apply serreIncidenceRankProductEquations_spec
  let f : (Fin 3 × ULift.{u} (Fin 2)) →
      Γ(serreIncidenceNativeParameterProductChart base M b j, ⊤) := fun r =>
    ∑ k, serreIncidenceNativeParameterProductCoefficient base M b j k *
      (pullback.fst b (finiteDimensionalProjectiveChartι K
        (SchemeModuleGlobalSectionsOver base M) j ≫
        schemeModuleGlobalSectionsProjectiveParametersToBase base M)).appTop
          (serreIncidenceGlobalBasisEvaluationMatrix base M C chart markedU r k)
  change _ = Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range (fun r => f (ρ r))))
  have hr : Set.range (fun r => f (ρ r)) = Set.range f := ρ.surjective.range_comp f
  rw [hr]
  exact h

end PfaffianDescent
