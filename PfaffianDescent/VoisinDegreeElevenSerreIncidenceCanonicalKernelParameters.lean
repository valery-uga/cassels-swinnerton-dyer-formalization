import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalKernelIso

/-! # Canonical kernel Proj retains the literal original section-parameter map -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[reassoc]
theorem serreIncidenceKernelProjIso_toParameters
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K))
    (I : (pullback b (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)))).IdealSheafData)
    (A : Matrix (Fin 6) (Fin 9) Γ(B, ⊤))
    (h : I.comap (serreIncidenceNativeAmbientProjectiveIso b).hom =
      (schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤)))
        (serreEvaluationHomogeneousIdeal A) bot_le).ker) :
    (serreIncidenceKernelProjIso_of_ideal_eq b I A h).hom ≫ I.subschemeι ≫ pullback.snd b
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))) =
    schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤)))
      (serreEvaluationHomogeneousIdeal A) bot_le ≫
      projectiveCoefficientMap (affineFunctionHom b)
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (by simp) := by
  rw [← Category.assoc, serreIncidenceKernelProjIso_toProduct, Category.assoc,
    serreIncidenceNativeAmbientProjectiveIso_hom_snd]

@[reassoc]
theorem serreIncidenceCanonicalKernelIso_toParameters
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) {n : ℕ} (h9 : n = 9)
    (I : (pullback b (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))).IdealSheafData)
    (A : Matrix (Fin 6) (Fin n) Γ(B, ⊤))
    (h : ∀ j : Fin n, I.comap (serreIncidenceRankProductChart b j) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range (serreIncidenceRankProductRow b j A)))) :
    (serreIncidenceCanonicalKernelIso b h9 I A h).hom ≫ I.subschemeι ≫ pullback.snd b
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) =
    schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤)))
      (serreEvaluationHomogeneousIdeal (fun r k => A r ((finCongr h9).symm k))) bot_le ≫
      projectiveCoefficientMap (affineFunctionHom b)
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (by simp) ≫
      (serreIncidenceParameterRankIso K h9).inv := by
  subst n
  have hr : ∀ j : Fin 9, I.comap (serreIncidenceNativeAmbientChartToProduct b j) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range (serreIncidenceNativeProductEvaluationRow b j A))) := h
  have ht := serreIncidenceKernelProjIso_toParameters b I A
    (serreIncidenceIdeal_eq_kernelProj_of_native_rows b I A hr)
  simp only [serreIncidenceParameterRankIso, eqToIso_refl, Iso.refl_inv, Category.comp_id]
  exact ht

end PfaffianDescent
