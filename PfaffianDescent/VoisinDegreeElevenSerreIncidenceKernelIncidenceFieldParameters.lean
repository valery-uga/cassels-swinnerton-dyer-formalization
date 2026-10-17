import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelIncidenceFieldIso
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelCoefficientSquare
import AllCharacteristics.ProjectiveCoefficientComposition

/-! # Literal specialized incidence and the original section parameters -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[reassoc]
theorem serreIncidenceKernelIncidenceFieldIso_toParameters
    {K E : Type u} [CommRing K] [CommRing E] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K))
    (I : (pullback b (toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 9) K)))).IdealSheafData)
    (A : Matrix (Fin 6) (Fin 9) Γ(B, ⊤))
    (h : I.comap (serreIncidenceNativeAmbientProjectiveIso b).hom =
      (schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤)))
        (serreEvaluationHomogeneousIdeal A) bot_le).ker)
    (β : Γ(B, ⊤) →+* E) (c : Spec (.of E) ⟶ B)
    (hc : Spec.map (CommRingCat.ofHom β) ≫ B.isoSpec.inv = c) :
    (serreIncidenceKernelIncidenceFieldIso b I A h β c hc).hom ≫ pullback.fst
      (I.subschemeι ≫ pullback.fst b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)))) c ≫
      I.subschemeι ≫ pullback.snd b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))) =
    schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E))
        (serreEvaluationHomogeneousIdeal (A.map β)) bot_le ≫
      projectiveCoefficientMap (β.comp (affineFunctionHom b))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp) := by
  have hp := congrArg (fun z => z ≫ pullback.snd b
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))))
      (serreIncidenceKernelProjIso_toProduct b I A h)
  simp only [Category.assoc, serreIncidenceNativeAmbientProjectiveIso_hom_snd] at hp
  have hf := congrArg (fun z => z ≫ I.subschemeι ≫ pullback.snd b
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))))
      (serreIncidenceKernelIncidenceFieldIso_toOriginal b I A h β c hc)
  simp only [Category.assoc] at hf
  rw [hp] at hf
  have hcoeff := congrArg (fun z => z ≫ projectiveCoefficientMap (affineFunctionHom b)
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (by simp))
      (serreIncidenceKernelImmersion_coefficient_square β A)
  simp only [Category.assoc] at hcoeff
  rw [← hcoeff] at hf
  rw [projectiveCoefficientMap_comp] at hf
  exact hf

end PfaffianDescent
