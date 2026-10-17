import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalBundleKernelData
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelBaseChange

/-! # Actual bundle section-incidence fibre and its native specialized kernel Proj -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K E : Type u} [Field K] [Field E] {X B : Scheme.{u}} [IsAffine B]
variable (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
variable (C : SchemeModuleFiniteFreeAffineCover M (ULift.{u} (Fin 2)))
variable (b : B ⟶ Spec (.of K)) (chart : Fin 3 → C.ι)
variable (markedU : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u}))
variable (hmarked : ∀ i, (markedU i ≫ (C.U (chart i)).ι) ≫ base = b)
variable (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
variable (ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2)))

variable (β : Γ(B, ⊤) →+* E) (c : Spec (.of E) ⟶ B)
variable (hc : Spec.map (CommRingCat.ofHom β) ≫ B.isoSpec.inv = c)

def serreThreePointSectionIncidence_nativeKernelFieldIso :
    scheme (serreEvaluationHomogeneousIdeal
      ((serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ).map β)) ≅
    pullback (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked) c :=
  serreIncidenceKernelBaseChangeIso B.isoSpec.symm
    (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked)
    (serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ)
    (serreIncidenceBundleKernelIso base M C b chart markedU hmarked h9 ρ)
    (serreIncidenceBundleKernelIso_toConfiguration base M C b chart markedU hmarked h9 ρ)
    β c hc

@[reassoc]
theorem serreThreePointSectionIncidence_nativeKernelFieldIso_toBase :
    (serreThreePointSectionIncidence_nativeKernelFieldIso
      base M C b chart markedU hmarked h9 ρ β c hc).hom ≫
      pullback.snd (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked) c =
    toBase (serreEvaluationHomogeneousIdeal
      ((serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ).map β)) :=
  serreIncidenceKernelBaseChangeIso_toBase B.isoSpec.symm
    (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked)
    (serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ)
    (serreIncidenceBundleKernelIso base M C b chart markedU hmarked h9 ρ)
    (serreIncidenceBundleKernelIso_toConfiguration base M C b chart markedU hmarked h9 ρ)
    β c hc

end PfaffianDescent
