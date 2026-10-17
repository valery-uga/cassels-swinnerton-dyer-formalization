import AllCharacteristics.UniversalProjectiveFamily
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Cartesian charts of the global universal family

The glued normalized family over a coefficient chart is the entire inverse
image of that chart. Thus the global structure morphism is proper and flat.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The global structure map's inverse image of a coefficient chart is exactly
the corresponding normalized universal chart family. -/
theorem projectiveUniversalToBase_preimage_chart (i : Monomials σ d) :
    projectiveUniversalToBase R σ d ⁻¹ᵁ (parameterChartι R σ d i).opensRange =
      (projectiveUniversalChartι R σ d i).opensRange := by
  ext x
  change (∃ b, parameterChartι R σ d i b = projectiveUniversalToBase R σ d x) ↔
    ∃ y, projectiveUniversalChartι R σ d i y = x
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨j, y, rfl⟩ := projectiveUniversalChartι_jointly_surjective R σ d x
    have hbase : parameterChartι R σ d j (normalizedFamilyToBase R σ d j y) =
        parameterChartι R σ d i b := by
      calc
        _ = projectiveUniversalToBase R σ d (projectiveUniversalChartι R σ d j y) :=
          (congrArg (fun f ↦ f y) (projectiveUniversalChartι_toBase R σ d j)).symm
        _ = _ := hb.symm
    obtain ⟨q, hq, _⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_chartOverlap (ParameterIdeal R σ d) j i)
      (normalizedFamilyToBase R σ d j y) b hbase
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_normalizedOverlapToLeft R σ d j i) y q hq.symm
    refine ⟨normalizedOverlapToRight R σ d j i z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← projectiveUniversalChartι_overlap, Scheme.Hom.comp_apply, hz]
  · rintro ⟨y, rfl⟩
    refine ⟨normalizedFamilyToBase R σ d i y, ?_⟩
    exact (congrArg (fun f ↦ f y) (projectiveUniversalChartι_toBase R σ d i)).symm

/-- Each normalized chart is the actual base change of the global family. -/
theorem isPullback_projectiveUniversalChart (i : Monomials σ d) :
    IsPullback (projectiveUniversalChartι R σ d i) (normalizedFamilyToBase R σ d i)
      (projectiveUniversalToBase R σ d) (parameterChartι R σ d i) :=
  (IsOpenImmersion.isPullback _ _ _ _ (projectiveUniversalChartι_toBase R σ d i)
    (projectiveUniversalToBase_preimage_chart R σ d i)).flip

/-- The normalized universal family is the entire categorical fiber over a coefficient chart. -/
noncomputable def projectiveUniversalChartFiberIso (i : Monomials σ d) :
    hypersurface (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i) ≅
      pullback (projectiveUniversalToBase R σ d) (parameterChartι R σ d i) :=
  (isPullback_projectiveUniversalChart R σ d i).isoPullback

/-- The chart-fiber identification has the given global chart inclusion. -/
theorem projectiveUniversalChartFiberIso_hom_fst (i : Monomials σ d) :
    (projectiveUniversalChartFiberIso R σ d i).hom ≫
      pullback.fst (projectiveUniversalToBase R σ d) (parameterChartι R σ d i) =
        projectiveUniversalChartι R σ d i :=
  (isPullback_projectiveUniversalChart R σ d i).isoPullback_hom_fst

/-- The chart-fiber identification preserves the normalized coefficient base. -/
theorem projectiveUniversalChartFiberIso_hom_snd (i : Monomials σ d) :
    (projectiveUniversalChartFiberIso R σ d i).hom ≫
      pullback.snd (projectiveUniversalToBase R σ d) (parameterChartι R σ d i) =
        normalizedFamilyToBase R σ d i :=
  (isPullback_projectiveUniversalChart R σ d i).isoPullback_hom_snd

/-- The global universal family is proper over projective coefficient space. -/
instance isProper_projectiveUniversalToBase : IsProper (projectiveUniversalToBase R σ d) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper.{u})
    (parameterChartCover R σ d).openCover
  intro i
  change IsProper (pullback.snd (projectiveUniversalToBase R σ d) (parameterChartι R σ d i))
  rw [← (isPullback_projectiveUniversalChart R σ d i).isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp (@IsProper.{u})
    (isPullback_projectiveUniversalChart R σ d i).isoPullback.inv
    (normalizedFamilyToBase R σ d i) (isProper_normalizedFamilyToBase R σ d i)

/-- The global universal family is flat over projective coefficient space. -/
instance flat_projectiveUniversalToBase : Flat (projectiveUniversalToBase R σ d) := by
  have : IsZariskiLocalAtTarget (@AlgebraicGeometry.Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @AlgebraicGeometry.Flat.{u}) (Q := RingHom.Flat)
  have : MorphismProperty.RespectsIso (@AlgebraicGeometry.Flat.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ _ (_ : IsIso _) ↦ by infer_instance)
  apply IsZariskiLocalAtTarget.of_openCover (P := @AlgebraicGeometry.Flat.{u})
    (parameterChartCover R σ d).openCover
  intro i
  change Flat (pullback.snd (projectiveUniversalToBase R σ d) (parameterChartι R σ d i))
  rw [← (isPullback_projectiveUniversalChart R σ d i).isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp (@Flat.{u})
    (isPullback_projectiveUniversalChart R σ d i).isoPullback.inv
    (normalizedFamilyToBase R σ d i) (flat_normalizedFamilyToBase R σ d i)

end UniversalHomogeneous
end AllCharacteristics
