import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelIncidenceGluing

/-! # The actual kernel-incidence identification preserves the actual configuration map -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[reassoc]
theorem serreIncidenceKernelProjIso_toProduct
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K))
    (I : (pullback b (toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 9) K)))).IdealSheafData)
    (A : Matrix (Fin 6) (Fin 9) Γ(B, ⊤))
    (h : I.comap (serreIncidenceNativeAmbientProjectiveIso b).hom =
      (schemeQuotientMap (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (serreEvaluationHomogeneousIdeal A) bot_le).ker) :
    (serreIncidenceKernelProjIso_of_ideal_eq b I A h).hom ≫ I.subschemeι =
      schemeQuotientMap (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (serreEvaluationHomogeneousIdeal A) bot_le ≫
      (serreIncidenceNativeAmbientProjectiveIso b).hom := by
  simp only [serreIncidenceKernelProjIso_of_ideal_eq, Iso.trans_hom, asIso_hom,
    Category.assoc, pullback.condition]
  rw [← Category.assoc, IsClosedImmersion.lift_fac]

@[reassoc]
theorem serreIncidenceKernelProjIso_toConfiguration
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K))
    (I : (pullback b (toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 9) K)))).IdealSheafData)
    (A : Matrix (Fin 6) (Fin 9) Γ(B, ⊤))
    (h : I.comap (serreIncidenceNativeAmbientProjectiveIso b).hom =
      (schemeQuotientMap (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (serreEvaluationHomogeneousIdeal A) bot_le).ker) :
    (serreIncidenceKernelProjIso_of_ideal_eq b I A h).hom ≫ I.subschemeι ≫
      pullback.fst b (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))) =
    toBase (serreEvaluationHomogeneousIdeal A) ≫ B.isoSpec.inv := by
  rw [← Category.assoc, serreIncidenceKernelProjIso_toProduct, Category.assoc,
    serreIncidenceNativeAmbientProjectiveIso_hom_fst, ← Category.assoc,
    schemeQuotientMap_toBase]

end PfaffianDescent
