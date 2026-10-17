import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalBundleKernelFieldParameters
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundFrameCoefficientSquare

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

variable {F : Type u} [Field F] [Algebra K F] [Algebra F E]
variable [Algebra K E] [IsScalarTower K F E]

theorem serreIncidenceBundleGroundFrame_toOriginalParameters
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1)
    (qF : Spec (.of F) ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    (q : Spec (.of E) ⟶ scheme (serreEvaluationHomogeneousIdeal
      ((serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ).map β)))
    (hcoeff : β.comp (affineFunctionHom b) = algebraMap K E)
    (hframe : q ≫ schemeQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E))
        (serreEvaluationHomogeneousIdeal
          ((serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ).map β)) bot_le ≫
        projectiveCoefficientMap (algebraMap F E)
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F))
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp) =
      Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ qF ≫
        serreKernelFrameProjectiveEmbedding G H hHG) :
    q ≫ (serreThreePointSectionIncidence_nativeKernelFieldIso
      base M C b chart markedU hmarked h9 ρ β c hc).hom ≫
      pullback.fst (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked) c ≫
      serreIncidenceBundleKernelParameters base M C b chart markedU hmarked =
    Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ qF ≫
      serreKernelFrameProjectiveEmbedding G H hHG ≫
      projectiveCoefficientMap (algebraMap K F)
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F)) (by simp) ≫
      (serreIncidenceNineParameterIso base M h9).inv := by
  rw [serreThreePointSectionIncidence_nativeKernelFieldIso_toParameters, hcoeff]
  have hcomp := projectiveCoefficientMap_comp (algebraMap K F) (algebraMap F E)
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F))
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp) (by simp)
  have hmap := congrArg (fun g : K →+* E => projectiveCoefficientMap g
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp))
    (IsScalarTower.algebraMap_eq K F E).symm
  have hcomp' := hcomp.trans hmap
  have h := congrArg (fun z => z ≫ projectiveCoefficientMap (algebraMap K F)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F)) (by simp) ≫
      (serreIncidenceNineParameterIso base M h9).inv) hframe
  have hccomp := congrArg (fun z => z ≫ (serreIncidenceNineParameterIso base M h9).inv) hcomp'
  simp only [Category.assoc] at hccomp h
  rw [hccomp] at h
  exact h

end PfaffianDescent
