import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalPlane

/-! # The actual rank-nine incidence is its literal kernel Proj, before choosing a pivot -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
variable (b : B ⟶ Spec (.of K)) {n : ℕ} (h9 : n = 9)
variable (I : (pullback b (toBase (⊥ : HomogeneousIdeal
  (homogeneousSubmodule (Fin n) K)))).IdealSheafData)
variable (A : Matrix (Fin 6) (Fin n) Γ(B, ⊤))
variable (h : ∀ j : Fin n, I.comap (serreIncidenceRankProductChart b j) =
  Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range (serreIncidenceRankProductRow b j A))))

def serreIncidenceCanonicalKernelIso :
    scheme (serreEvaluationHomogeneousIdeal (fun r k => A r ((finCongr h9).symm k))) ≅
      I.subscheme := by
  subst n
  have hr : ∀ j : Fin 9, I.comap (serreIncidenceNativeAmbientChartToProduct b j) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range (serreIncidenceNativeProductEvaluationRow b j A))) := h
  exact serreIncidenceKernelProjIso_of_ideal_eq b I A
      (serreIncidenceIdeal_eq_kernelProj_of_native_rows b I A hr)

@[reassoc]
theorem serreIncidenceCanonicalKernelIso_toConfiguration :
    (serreIncidenceCanonicalKernelIso b h9 I A h).hom ≫ I.subschemeι ≫ pullback.fst b
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) =
      toBase (serreEvaluationHomogeneousIdeal (fun r k => A r ((finCongr h9).symm k))) ≫
        B.isoSpec.inv := by
  subst n
  have hr : ∀ j : Fin 9, I.comap (serreIncidenceNativeAmbientChartToProduct b j) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range (serreIncidenceNativeProductEvaluationRow b j A))) := h
  exact serreIncidenceKernelProjIso_toConfiguration b I A
      (serreIncidenceIdeal_eq_kernelProj_of_native_rows b I A hr)

end PfaffianDescent
