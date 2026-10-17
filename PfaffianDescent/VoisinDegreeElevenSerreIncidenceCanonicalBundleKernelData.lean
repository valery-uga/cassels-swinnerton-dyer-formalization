import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalBundleKernelIso

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

def serreIncidenceBundleKernelMatrix : Matrix (Fin 6) (Fin 9) Γ(B, ⊤) :=
  fun r k => serreIncidenceGlobalBasisEvaluationMatrix base M C chart markedU
    (ρ r) ((finCongr h9).symm k)

def serreIncidenceBundleKernelIdeal :
    (pullback b (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).IdealSheafData := by
  letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  exact serreThreePointSectionIncidenceIdeal b base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    (fun i => markedU i ≫ (C.U (chart i)).ι) hmarked
    (C.projectiveSectionLocalZeroGluedToAmbient base M)

def serreIncidenceBundleKernelConfiguration :
    (serreIncidenceBundleKernelIdeal base M C b chart markedU hmarked).subscheme ⟶ B :=
  (serreIncidenceBundleKernelIdeal base M C b chart markedU hmarked).subschemeι ≫
    pullback.fst b (schemeModuleGlobalSectionsProjectiveParametersToBase base M)

def serreIncidenceBundleKernelIso :
    scheme (serreEvaluationHomogeneousIdeal
      (serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ)) ≅
    (serreIncidenceBundleKernelIdeal base M C b chart markedU hmarked).subscheme := by
  exact serreThreePointSectionIncidence_nativeKernelIso base M C b chart markedU hmarked h9 ρ

@[reassoc]
theorem serreIncidenceBundleKernelIso_toConfiguration :
    (serreIncidenceBundleKernelIso base M C b chart markedU hmarked h9 ρ).hom ≫
      serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked =
    toBase (serreEvaluationHomogeneousIdeal
      (serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ)) ≫ B.isoSpec.inv := by
  exact serreThreePointSectionIncidence_nativeKernelIso_toConfiguration
    base M C b chart markedU hmarked h9 ρ

end PfaffianDescent
