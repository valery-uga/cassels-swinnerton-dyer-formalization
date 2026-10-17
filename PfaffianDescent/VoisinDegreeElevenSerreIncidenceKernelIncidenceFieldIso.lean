import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelBaseChange
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelIncidenceProjection

/-! # Literal field fibre of the actual incidence is its specialized kernel Proj -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K E : Type u} [CommRing K] [CommRing E]
variable {B : Scheme.{u}} [IsAffine B]
variable (b : B ⟶ Spec (.of K))
variable (I : (pullback b (toBase (⊥ : HomogeneousIdeal
  (homogeneousSubmodule (Fin 9) K)))).IdealSheafData)
variable (A : Matrix (Fin 6) (Fin 9) Γ(B, ⊤))
variable (h : I.comap (serreIncidenceNativeAmbientProjectiveIso b).hom =
  (schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤)))
    (serreEvaluationHomogeneousIdeal A) bot_le).ker)
variable (β : Γ(B, ⊤) →+* E) (c : Spec (.of E) ⟶ B)
variable (hc : Spec.map (CommRingCat.ofHom β) ≫ B.isoSpec.inv = c)

def serreIncidenceKernelIncidenceFieldIso :
    scheme (serreEvaluationHomogeneousIdeal (A.map β)) ≅
      pullback (I.subschemeι ≫ pullback.fst b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)))) c :=
  serreIncidenceKernelBaseChangeIso B.isoSpec.symm _ A
    (serreIncidenceKernelProjIso_of_ideal_eq b I A h)
    (serreIncidenceKernelProjIso_toConfiguration b I A h) β c hc

@[reassoc]
theorem serreIncidenceKernelIncidenceFieldIso_toBase :
    (serreIncidenceKernelIncidenceFieldIso b I A h β c hc).hom ≫ pullback.snd
      (I.subschemeι ≫ pullback.fst b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)))) c =
      toBase (serreEvaluationHomogeneousIdeal (A.map β)) :=
  serreIncidenceKernelBaseChangeIso_toBase B.isoSpec.symm _ A _ _ β c hc

@[reassoc]
theorem serreIncidenceKernelIncidenceFieldIso_toOriginal :
    (serreIncidenceKernelIncidenceFieldIso b I A h β c hc).hom ≫ pullback.fst
      (I.subschemeι ≫ pullback.fst b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)))) c =
      projectiveCoefficientMap β (serreEvaluationHomogeneousIdeal A)
        (serreEvaluationHomogeneousIdeal (A.map β)) (serreIncidenceKernelIdeal_coefficient β A) ≫
      (serreIncidenceKernelProjIso_of_ideal_eq b I A h).hom :=
  serreIncidenceKernelBaseChangeIso_toOriginal B.isoSpec.symm _ A _ _ β c hc

end PfaffianDescent
