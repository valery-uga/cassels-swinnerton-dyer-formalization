import AllCharacteristics.AmbientProjectiveBaseChange
import AllCharacteristics.UniversalProjectiveAmbient
import AllCharacteristics.UniversalProjectiveFamilyCharts
import PfaffianDescent.CartesianClosedProduct

/-!
# Closedness of the global universal projective hypersurface incidence

Each normalized coefficient chart defines a closed subscheme of ambient
projective space times that coefficient chart. The chartwise result is the
input for the global closed-immersion descent.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective

universe u
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The normalized universal hypersurface as a morphism to ambient projective
space times its affine coefficient chart. -/
noncomputable def normalizedFamilyToAmbientProduct (i : Monomials σ d) :
    hypersurface (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i) ⟶
      Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
        Spec (.of (ParameterChartRing R σ d i)) :=
  prod.lift (normalizedFamilyToAmbient R σ d i) (normalizedFamilyToBase R σ d i)

/-- On every coefficient chart, the normalized universal hypersurface is a
closed subscheme of ambient projective space times that chart. -/
theorem normalizedFamilyToAmbientProduct_isClosedImmersion (i : Monomials σ d) :
    IsClosedImmersion (normalizedFamilyToAmbientProduct R σ d i) := by
  let p := normalizedForm R σ d i
  let hp := normalizedForm_isHomogeneous R σ d i
  let f := chartBaseMap (ParameterIdeal R σ d) i
  let j := hypersurfaceToAmbient p hp
  have hjBase : j ≫ ambientToBase (R := ParameterChartRing R σ d i) (σ := σ) =
      normalizedFamilyToBase R σ d i := by
    exact quotientProjMap_toBase (equationIdeal p hp)
  have hcart := isPullback_ambientCoefficientMap (σ := σ) f
  have hclosed := PfaffianDescent.isClosedImmersion_prodLift_of_isPullback
    (ambientCoefficientMap (σ := σ) f)
    (ambientToBase (R := ParameterChartRing R σ d i) (σ := σ))
    (ambientToBase (R := R) (σ := σ))
    (Spec.map (CommRingCat.ofHom f)) hcart j
  change IsClosedImmersion
    (prod.lift (j ≫ ambientCoefficientMap (σ := σ) f)
      (normalizedFamilyToBase R σ d i))
  rw [← hjBase]
  exact hclosed

/-- The normalized universal hypersurface chart is the full preimage of the
coefficient chart under the global incidence map. -/
theorem isPullback_projectiveUniversalIncidence_chart (i : Monomials σ d) :
    IsPullback (normalizedFamilyToAmbientProduct R σ d i)
      (projectiveUniversalChartι R σ d i)
      (prod.map (𝟙 (Proj (MvPolynomial.homogeneousSubmodule σ R)))
        (parameterChartι R σ d i))
      (projectiveUniversalIncidence R σ d) := by
  apply IsPullback.of_right
    (h₁₂ := (prod.snd :
      Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
        Spec (.of (ParameterChartRing R σ d i)) ⟶
        Spec (.of (ParameterChartRing R σ d i))))
    (h₂₂ := (prod.snd :
      Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
        projectiveParameters R σ d ⟶ projectiveParameters R σ d))
  · simpa only [normalizedFamilyToAmbientProduct, prod.lift_snd,
      projectiveUniversalIncidence_snd] using
      (isPullback_projectiveUniversalChart R σ d i).flip
  · change prod.lift (normalizedFamilyToAmbient R σ d i)
      (normalizedFamilyToBase R σ d i) ≫
        prod.map (𝟙 _) (parameterChartι R σ d i) =
      projectiveUniversalChartι R σ d i ≫ projectiveUniversalIncidence R σ d
    rw [projectiveUniversalChartι_toIncidence, prod.lift_map]
    simp only [Category.comp_id]
  · exact (PfaffianDescent.isPullback_prodMap_id_snd (Z :=
      Proj (MvPolynomial.homogeneousSubmodule σ R))
      (parameterChartι R σ d i)).flip

/-- Ambient projective space times the normalized equation charts covers
ambient projective space times the global equation-parameter space. -/
noncomputable def projectiveUniversalIncidenceAmbientOpenCover :
    (Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d).OpenCover := by
  classical
  refine {
    I₀ := Monomials σ d
    X := fun i => Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      Spec (.of (ParameterChartRing R σ d i))
    f := fun i => prod.map (𝟙 _) (parameterChartι R σ d i)
    mem₀ := ?_ }
  rw [Scheme.presieve₀_mem_precoverage_iff]
  constructor
  · intro y
    obtain ⟨i, z, hz⟩ := exists_coordinate_chart (ParameterIdeal R σ d)
      ((prod.snd : Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
        projectiveParameters R σ d ⟶ projectiveParameters R σ d) y)
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
      (PfaffianDescent.isPullback_prodMap_id_snd (Z :=
        Proj (MvPolynomial.homogeneousSubmodule σ R))
        (parameterChartι R σ d i)) y z hz.symm
    exact ⟨i, w, hw⟩
  · intro i
    exact PfaffianDescent.isOpenImmersion_prodMap_id_snd (Z :=
      Proj (MvPolynomial.homogeneousSubmodule σ R))
      (parameterChartι R σ d i)

/-- The global universal projective hypersurface is a closed subscheme of
ambient projective space times the projective equation-parameter space. -/
theorem projectiveUniversalIncidence_isClosedImmersion :
    IsClosedImmersion (projectiveUniversalIncidence R σ d) := by
  apply IsZariskiLocalAtTarget.of_openCover
    (projectiveUniversalIncidenceAmbientOpenCover R σ d)
  intro i
  change IsClosedImmersion
    (pullback.snd (projectiveUniversalIncidence R σ d)
      (prod.map (𝟙 (Proj (MvPolynomial.homogeneousSubmodule σ R)))
        (parameterChartι R σ d i)))
  rw [← (isPullback_projectiveUniversalIncidence_chart R σ d i).flip.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp (@IsClosedImmersion.{u})
    (isPullback_projectiveUniversalIncidence_chart R σ d i).flip.isoPullback.inv
    (normalizedFamilyToAmbientProduct R σ d i)
    (normalizedFamilyToAmbientProduct_isClosedImmersion R σ d i)

end UniversalHomogeneous
end AllCharacteristics
