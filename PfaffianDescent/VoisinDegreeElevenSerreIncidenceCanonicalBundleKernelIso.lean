import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalKernelIso

/-! # Literal section incidence and its actual bundle-evaluation kernel Proj -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] {X B : Scheme.{u}} [IsAffine B]
variable (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
variable (C : SchemeModuleFiniteFreeAffineCover M (ULift.{u} (Fin 2)))
variable (b : B ⟶ Spec (.of K)) (chart : Fin 3 → C.ι)
variable (markedU : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u}))
variable (hmarked : ∀ i, (markedU i ≫ (C.U (chart i)).ι) ≫ base = b)
variable (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
variable (ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2)))

def serreThreePointSectionIncidence_nativeKernelIso :
    letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    let I := serreThreePointSectionIncidenceIdeal b base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      (fun i => markedU i ≫ (C.U (chart i)).ι) hmarked
      (C.projectiveSectionLocalZeroGluedToAmbient base M)
    scheme (serreEvaluationHomogeneousIdeal (fun r k =>
      serreIncidenceGlobalBasisEvaluationMatrix base M C chart markedU
        (ρ r) ((finCongr h9).symm k))) ≅ I.subscheme := by
  letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  exact serreIncidenceCanonicalKernelIso b h9 _
    (fun r k => serreIncidenceGlobalBasisEvaluationMatrix base M C chart markedU (ρ r) k)
    (fun j => serreThreePointSectionIncidenceIdeal_rank_rows
      base M C b chart markedU hmarked ρ j)

@[reassoc]
theorem serreThreePointSectionIncidence_nativeKernelIso_toConfiguration :
    letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    let I := serreThreePointSectionIncidenceIdeal b base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      (fun i => markedU i ≫ (C.U (chart i)).ι) hmarked
      (C.projectiveSectionLocalZeroGluedToAmbient base M)
    (serreThreePointSectionIncidence_nativeKernelIso base M C b chart markedU hmarked h9 ρ).hom ≫
      I.subschemeι ≫ pullback.fst b
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M) =
      toBase (serreEvaluationHomogeneousIdeal (fun r k =>
        serreIncidenceGlobalBasisEvaluationMatrix base M C chart markedU
          (ρ r) ((finCongr h9).symm k))) ≫ B.isoSpec.inv := by
  letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  exact serreIncidenceCanonicalKernelIso_toConfiguration b h9 _
    (fun r k => serreIncidenceGlobalBasisEvaluationMatrix base M C chart markedU (ρ r) k)
    (fun j => serreThreePointSectionIncidenceIdeal_rank_rows
      base M C b chart markedU hmarked ρ j)

end PfaffianDescent
