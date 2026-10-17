import PfaffianDescent.ProjectiveLinearCoordinateSchemeIso
import AllCharacteristics.HomogeneousProjectiveAmbient

/-! The actual ambient morphism square for linear coordinate changes of
homogeneous projective schemes. This retains their projective embeddings,
not merely the abstract isomorphism of the source and target schemes. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal polynomial substitution with its actual degree grading. -/
def linearCoordinateChangeAmbientGradedHom (M : Matrix (Fin 4) (Fin 4) K) :
    homogeneousSubmodule (Fin 4) K →+*ᵍ homogeneousSubmodule (Fin 4) K where
  __ := (linearSubstitution M).toRingHom
  map_mem hx := linearSubstitution_homogeneous M hx

/-- The actual ambient projective automorphism, in the SAME orientation
as linearCoordinateChangeSchemeIso.hom. Its coordinate-ring map is inverse. -/
def linearCoordinateChangeAmbientIso
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    Proj (homogeneousSubmodule (Fin 4) K) ≅ Proj (homogeneousSubmodule (Fin 4) K) := by
  let e := linearSubstitutionEquiv M hM
  let F := linearCoordinateChangeAmbientGradedHom M
  let G := linearCoordinateChangeAmbientGradedHom M⁻¹
  have hF : Function.Surjective F := e.surjective
  have hG : Function.Surjective G := e.symm.surjective
  let hf := gradedSurjective_irrelevant_le F hF
  let hg := gradedSurjective_irrelevant_le G hG
  have hGF : G.comp F = GradedRingHom.id (homogeneousSubmodule (Fin 4) K) := by
    apply GradedRingHom.ext
    intro p
    exact e.symm_apply_apply p
  have hFG : F.comp G = GradedRingHom.id (homogeneousSubmodule (Fin 4) K) := by
    apply GradedRingHom.ext
    intro p
    exact e.apply_symm_apply p
  refine { hom := Proj.map G hg
           inv := Proj.map F hf
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · rw [← Proj.map_comp F G hf hg]
    simpa only [hGF] using (Proj.map_id (𝒜 := homogeneousSubmodule (Fin 4) K))
  · rw [← Proj.map_comp G F hg hf]
    simpa only [hFG] using (Proj.map_id (𝒜 := homogeneousSubmodule (Fin 4) K))

/-- The induced projective scheme isomorphism has the expected actual
ambient square. The relation is derived from literal quotient maps. -/
theorem linearCoordinateChangeSchemeIso_hom_toAmbient
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom) :
    (linearCoordinateChangeSchemeIso M hM I J hIJ).hom ≫ quotientProjMap J =
      quotientProjMap I ≫ (linearCoordinateChangeAmbientIso M hM).hom := by
  let G := linearCoordinateChangeGradedHomSymm M hM I J hIJ
  let H := linearCoordinateChangeAmbientGradedHom M⁻¹
  have hG : Function.Surjective G :=
    (Ideal.quotientEquivAlg J.toIdeal I.toIdeal
      (linearSubstitutionEquiv M hM).symm
      (linearCoordinateChange_ideal_symm M hM I J hIJ)).surjective
  have hH : Function.Surjective H := (linearSubstitutionEquiv M hM).symm.surjective
  let hg := gradedSurjective_irrelevant_le G hG
  let hh := gradedSurjective_irrelevant_le H hH
  have hcomp : G.comp (quotientGradedRingHom J) =
      (quotientGradedRingHom I).comp H := by
    apply GradedRingHom.ext
    intro p
    change Ideal.quotientEquivAlg J.toIdeal I.toIdeal
      (linearSubstitutionEquiv M hM).symm
      (linearCoordinateChange_ideal_symm M hM I J hIJ)
      (Ideal.Quotient.mk J.toIdeal p) =
      Ideal.Quotient.mk I.toIdeal ((linearSubstitutionEquiv M hM).symm p)
    rw [Ideal.quotientEquivAlg_mk]
  change Proj.map G hg ≫ Proj.map (quotientGradedRingHom J)
      (irrelevant_le_map_quotientGradedRingHom J) =
    Proj.map (quotientGradedRingHom I) (irrelevant_le_map_quotientGradedRingHom I) ≫
      Proj.map H hh
  rw [← Proj.map_comp (quotientGradedRingHom J) G
      (irrelevant_le_map_quotientGradedRingHom J) hg,
    ← Proj.map_comp H (quotientGradedRingHom I) hh
      (irrelevant_le_map_quotientGradedRingHom I)]
  congr 1

end PfaffianDescent
