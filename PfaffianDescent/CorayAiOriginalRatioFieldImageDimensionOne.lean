import PfaffianDescent.CorayAiOriginalRatioFieldPointSameImage
import PfaffianDescent.CorayAiDominantFieldPointAffineSections
import PfaffianDescent.CorayAiFiniteTypeFieldEmbeddingDimensionOne

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- An honest transcendence-degree≤1 branch of the SAME existing ratio
field forces dimension≤1 at EVERY stalk of the SAME full original image.
The actual field point, affine maps, original scalar action, finite-type
property, normalization and stalk localization are all derived internally. -/
theorem cubicThroughPointOriginalBasisRatioField_trdeg_le_one_sameImage_stalk_dimensionLEOne001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let E := cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a
    Algebra.trdeg K E ≤ 1 →
      ∀ z : cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a,
        Ring.DimensionLEOne
          ((cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a).presheaf.stalk z) := by
  classical
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let E := cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a
  let C := cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a
  let pi := cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a
  change Algebra.trdeg K E ≤ 1 → ∀ z : C, Ring.DimensionLEOne (C.presheaf.stalk z)
  intro hTrdeg z
  letI : IsIntegral C := cubicThroughPointBasisEvaluationImage_isIntegral p hp hp0 n y hpy j b a
  letI : IsProper pi := cubicThroughPointBasisEvaluationImageToBase_isProper p hp hp0 n y hpy j b a
  let i := cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a
  letI : IsClosedImmersion i :=
    cubicThroughPointBasisEvaluationImageInclusion_isClosedImmersion p hp hp0 n y hpy j b a
  letI : IsLocallyNoetherian
      (scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))) :=
    projectiveEvaluationAmbient_isLocallyNoetherian m
  letI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian i
  obtain ⟨eta, hEta, _, _, hBase⟩ :=
    cubicThroughPointOriginalBasisRatioField_exists_dominant_sameImagePoint001 p hp hp0 n y hpy j b a
  letI : IsDominant eta := hEta
  letI : QuasiCompact eta := inferInstance
  obtain ⟨U, hU, hz, _⟩ := exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : C.Opens) by trivial)
  letI : Nonempty U := ⟨⟨z, hz⟩⟩
  let beta : K →+* Γ(C, U) :=
    (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨g, hg, hCoeff, hFinite⟩ :=
    integralScheme_dominantFieldPoint_affineSection_embedding001 C pi eta hBase U hU
  letI : Algebra K Γ(C, U) := beta.toAlgebra
  letI : Algebra.FiniteType K Γ(C, U) := hFinite
  let gAlg : Γ(C, U) →ₐ[K] E :=
    { g with commutes' := fun c => RingHom.congr_fun hCoeff c }
  letI : Ring.DimensionLEOne Γ(C, U) :=
    finiteTypeRing_injective_field_trdeg_le_one_dimensionLEOne001 gAlg hg hTrdeg
  exact integralScheme_affineOpen_dimensionLEOne_stalk001 C U hU ⟨z, hz⟩

end PfaffianDescent.Coray
