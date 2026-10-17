import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalBundleKernelData
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalKernelParameters

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

def serreIncidenceBundleKernelParameters :
    (serreIncidenceBundleKernelIdeal base M C b chart markedU hmarked).subscheme ⟶
      schemeModuleGlobalSectionsProjectiveParameters base M :=
  (serreIncidenceBundleKernelIdeal base M C b chart markedU hmarked).subschemeι ≫
    pullback.snd b (schemeModuleGlobalSectionsProjectiveParametersToBase base M)

@[reassoc]
theorem serreIncidenceBundleKernelIso_toParameters :
    (serreIncidenceBundleKernelIso base M C b chart markedU hmarked h9 ρ).hom ≫
      serreIncidenceBundleKernelParameters base M C b chart markedU hmarked =
    schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤)))
      (serreEvaluationHomogeneousIdeal
        (serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ)) bot_le ≫
      projectiveCoefficientMap (affineFunctionHom b)
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (by simp) ≫
      (serreIncidenceNineParameterIso base M h9).inv := by
  letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  exact serreIncidenceCanonicalKernelIso_toParameters b h9 _
    (fun r k => serreIncidenceGlobalBasisEvaluationMatrix base M C chart markedU (ρ r) k)
    (fun j => serreThreePointSectionIncidenceIdeal_rank_rows
      base M C b chart markedU hmarked ρ j)

end PfaffianDescent
