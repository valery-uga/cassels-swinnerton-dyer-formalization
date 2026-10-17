import PfaffianDescent.VoisinDegreeElevenSerreIncidenceIdealAffineCover
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeAmbientChartMap
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelChartIdeal

/-! # Actual affine equations identify the actual incidence with the kernel Proj -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceIdeal_eq_kernelProj_of_chart_equations
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K))
    (I : (pullback b (toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 9) K)))).IdealSheafData)
    (A : Matrix (Fin 6) (Fin 9) Γ(B, ⊤))
    (h : ∀ j : Fin 9,
      (I.comap (serreIncidenceNativeAmbientChartToProduct b j)).comap
        (serreIncidenceNativeAmbientChartIso b j).hom =
      (schemeQuotientMap (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (serreEvaluationHomogeneousIdeal A) bot_le).ker.comap
        (chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) j)) :
    I.comap (serreIncidenceNativeAmbientProjectiveIso b).hom =
      (schemeQuotientMap (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (serreEvaluationHomogeneousIdeal A) bot_le).ker := by
  apply serreIncidenceIdeal_eq_of_affineCover _ _
    (coordinateOpenCover (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))))
  intro j
  change (I.comap (serreIncidenceNativeAmbientProjectiveIso b).hom).comap
      (chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) j) = _
  rw [← Scheme.IdealSheafData.comap_comp, serreIncidenceNativeAmbientChart_commutes,
    Scheme.IdealSheafData.comap_comp]
  exact h j

def serreIncidenceKernelProjIso_of_ideal_eq
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K))
    (I : (pullback b (toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 9) K)))).IdealSheafData)
    (A : Matrix (Fin 6) (Fin 9) Γ(B, ⊤))
    (h : I.comap (serreIncidenceNativeAmbientProjectiveIso b).hom =
      (schemeQuotientMap (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (serreEvaluationHomogeneousIdeal A) bot_le).ker) :
    scheme (serreEvaluationHomogeneousIdeal A) ≅ I.subscheme := by
  let e := serreIncidenceNativeAmbientProjectiveIso b
  let c := schemeQuotientMap (⊥ : HomogeneousIdeal
    (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (serreEvaluationHomogeneousIdeal A) bot_le
  letI : IsClosedImmersion c := schemeQuotientMap_closedImmersion _ _ _
  let j := pullback.snd I.subschemeι e.hom
  have hj : j.ker = c.ker := by
    rw [cubicClosedPointSerreFiniteZeroResidual_pullback_snd_kernel,
      Scheme.IdealSheafData.ker_subschemeι]
    exact h
  let w := IsClosedImmersion.lift j c hj.le
  letI : IsIso w := IsClosedImmersion.isIso_lift j c hj
  exact asIso w ≪≫ asIso (pullback.fst I.subschemeι e.hom)

end PfaffianDescent
