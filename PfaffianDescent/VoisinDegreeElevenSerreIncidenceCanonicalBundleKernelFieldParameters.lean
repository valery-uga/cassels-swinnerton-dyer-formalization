import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalBundleKernelFieldIso
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalBundleKernelParameters
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelCoefficientSquare
import AllCharacteristics.ProjectiveCoefficientComposition
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

@[reassoc]
theorem serreThreePointSectionIncidence_nativeKernelFieldIso_toOriginal :
    (serreThreePointSectionIncidence_nativeKernelFieldIso
      base M C b chart markedU hmarked h9 ρ β c hc).hom ≫
      pullback.fst (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked) c =
    projectiveCoefficientMap β
      (serreEvaluationHomogeneousIdeal (serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ))
      (serreEvaluationHomogeneousIdeal ((serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ).map β))
      (serreIncidenceKernelIdeal_coefficient β (serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ)) ≫
    (serreIncidenceBundleKernelIso base M C b chart markedU hmarked h9 ρ).hom :=
  serreIncidenceKernelBaseChangeIso_toOriginal B.isoSpec.symm
    (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked)
    (serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ)
    (serreIncidenceBundleKernelIso base M C b chart markedU hmarked h9 ρ)
    (serreIncidenceBundleKernelIso_toConfiguration base M C b chart markedU hmarked h9 ρ)
    β c hc

@[reassoc]
theorem serreThreePointSectionIncidence_nativeKernelFieldIso_toParameters :
    (serreThreePointSectionIncidence_nativeKernelFieldIso
      base M C b chart markedU hmarked h9 ρ β c hc).hom ≫
      pullback.fst (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked) c ≫
      serreIncidenceBundleKernelParameters base M C b chart markedU hmarked =
    schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E))
      (serreEvaluationHomogeneousIdeal
        ((serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ).map β)) bot_le ≫
      projectiveCoefficientMap (β.comp (affineFunctionHom b))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp) ≫
      (serreIncidenceNineParameterIso base M h9).inv := by
  have hf := congrArg (fun z => z ≫ serreIncidenceBundleKernelParameters base M C b chart markedU hmarked)
    (serreThreePointSectionIncidence_nativeKernelFieldIso_toOriginal
      base M C b chart markedU hmarked h9 ρ β c hc)
  simp only [Category.assoc] at hf
  rw [serreIncidenceBundleKernelIso_toParameters] at hf
  have hcoeff := congrArg (fun z => z ≫ projectiveCoefficientMap (affineFunctionHom b)
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (by simp) ≫
      (serreIncidenceNineParameterIso base M h9).inv)
    (serreIncidenceKernelImmersion_coefficient_square β
      (serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ))
  simp only [Category.assoc] at hcoeff
  rw [← hcoeff] at hf
  have hcomp := congrArg (fun z => z ≫ (serreIncidenceNineParameterIso base M h9).inv)
    (projectiveCoefficientMap_comp (affineFunctionHom b) β
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤)))
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp) (by simp))
  simp only [Category.assoc] at hcomp
  rw [hcomp] at hf
  exact hf

end PfaffianDescent
