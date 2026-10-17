import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeRowIdealGluing
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelIncidenceProjection
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceMinorKernelScheme

/-! # Literal incidence equations and a unit minor give the actual projective plane family -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidence_exists_native_plane_of_rows_minor
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K))
    (I : (pullback b (toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 9) K)))).IdealSheafData)
    (A : Matrix (Fin 6) (Fin 9) Γ(B, ⊤))
    (h : ∀ j : Fin 9,
      I.comap (serreIncidenceNativeAmbientChartToProduct b j) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range (serreIncidenceNativeProductEvaluationRow b j A))))
    (m : Fin 6 ↪ Fin 9) (hm : IsUnit (A.submatrix id m).det) :
    ∃ e : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≅
        I.subscheme,
      e.hom ≫ I.subschemeι ≫ pullback.fst b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))) =
        toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≫
          B.isoSpec.inv ∧
      IsOpenMap (I.subschemeι ≫ pullback.fst b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)))) := by
  have hi := serreIncidenceIdeal_eq_kernelProj_of_native_rows b I A h
  let eK := serreIncidenceKernelProjIso_of_ideal_eq b I A hi
  obtain ⟨eP, hp, hopen⟩ := serreEvaluationKernel_exists_planeIso_of_unit_minor A m hm
  have hk : eK.hom ≫ I.subschemeι ≫ pullback.fst b
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))) =
      toBase (serreEvaluationHomogeneousIdeal A) ≫ B.isoSpec.inv :=
    serreIncidenceKernelProjIso_toConfiguration b I A hi
  refine ⟨eP ≪≫ eK, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc]
    rw [hk, ← Category.assoc, hp]
  · have hf : I.subschemeι ≫ pullback.fst b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))) =
        eK.inv ≫ toBase (serreEvaluationHomogeneousIdeal A) ≫ B.isoSpec.inv := by
      rw [← hk]
      simp
    rw [hf]
    exact B.isoSpec.inv.isOpenMap.comp (hopen.comp eK.inv.isOpenMap)

end PfaffianDescent
