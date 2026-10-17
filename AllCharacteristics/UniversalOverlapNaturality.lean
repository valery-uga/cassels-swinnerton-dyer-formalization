import AllCharacteristics.UniversalCoefficientOverlap
import AllCharacteristics.ScaledHypersurfaceComposition

/-!
# Canonical hypersurface maps on universal coefficient overlaps

One actual hypersurface over the overlap spectrum represents both restricted
universal families. Its maps into the two chart families are canonical
projective coefficient maps, are open immersions, and form Cartesian squares.
The previous overlap-family isomorphism is exactly their comparison.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)
variable (j l : Monomials σ d)
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => ParameterIdeal R σ d

/-- A single actual hypersurface representing both restricted universal chart families. -/
noncomputable def normalizedOverlapHypersurface : Scheme.{u} :=
  hypersurface ((normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
    ((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l))

/-- The common overlap hypersurface over its actual coefficient intersection. -/
noncomputable def normalizedOverlapToBase :
    normalizedOverlapHypersurface R σ d j l ⟶ Spec (.of (ChartOverlapRing I₀ j l)) :=
  hypersurfaceToBase ((normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
    ((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l))

/-- The canonical scaled coefficient map into the left universal chart family. -/
noncomputable def normalizedOverlapToLeft :
    normalizedOverlapHypersurface R σ d j l ⟶
      hypersurface (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j) :=
  scaledHypersurfaceMap (chartOverlapLeftMap I₀ j l)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    ((normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
    ((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l))
    (↑((chartOverlapUnit I₀ j l)⁻¹) : ChartOverlapRing I₀ j l)
    ((chartOverlapUnit I₀ j l)⁻¹).isUnit (normalizedForm_overlap_relation R σ d j l)

/-- The canonical coefficient map into the right universal chart family. -/
noncomputable def normalizedOverlapToRight :
    normalizedOverlapHypersurface R σ d j l ⟶
      hypersurface (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l) :=
  projectiveCoefficientMap (chartOverlapRightMap I₀ j l)
    (equationIdeal (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l))
    (equationIdeal ((normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
      ((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l)))
    (equationIdeal_map (chartOverlapRightMap I₀ j l)
      (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l))

/-- The common overlap hypersurface identifies with the left family's actual restriction. -/
noncomputable def normalizedOverlapLeftFiberIso :
    normalizedOverlapHypersurface R σ d j l ≅ pullback (normalizedFamilyToBase R σ d j)
      (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I₀ j l))) :=
  scaledHypersurfaceFiberIso (chartOverlapLeftMap I₀ j l)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    ((normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
    ((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l))
    (↑((chartOverlapUnit I₀ j l)⁻¹) : ChartOverlapRing I₀ j l)
    ((chartOverlapUnit I₀ j l)⁻¹).isUnit (normalizedForm_overlap_relation R σ d j l)

/-- The same hypersurface identifies with the right family's actual restriction. -/
noncomputable def normalizedOverlapRightFiberIso :
    normalizedOverlapHypersurface R σ d j l ≅ pullback (normalizedFamilyToBase R σ d l)
      (Spec.map (CommRingCat.ofHom (chartOverlapRightMap I₀ j l))) :=
  hypersurfaceBaseChangeIso (chartOverlapRightMap I₀ j l)
    (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)

/-- The left overlap-family square is Cartesian. -/
theorem isPullback_normalizedOverlapToLeft :
    IsPullback (normalizedOverlapToLeft R σ d j l) (normalizedOverlapToBase R σ d j l)
      (normalizedFamilyToBase R σ d j) (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I₀ j l))) :=
  isPullback_scaledHypersurfaceMap (chartOverlapLeftMap I₀ j l)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    ((normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
    ((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l))
    (↑((chartOverlapUnit I₀ j l)⁻¹) : ChartOverlapRing I₀ j l)
    ((chartOverlapUnit I₀ j l)⁻¹).isUnit (normalizedForm_overlap_relation R σ d j l)

/-- The right overlap-family square is Cartesian. -/
theorem isPullback_normalizedOverlapToRight :
    IsPullback (normalizedOverlapToRight R σ d j l) (normalizedOverlapToBase R σ d j l)
      (normalizedFamilyToBase R σ d l) (Spec.map (CommRingCat.ofHom (chartOverlapRightMap I₀ j l))) :=
  isPullback_projectiveCoefficientMap _ _ _ _

/-- The overlap embeds openly in the left universal chart family. -/
instance isOpenImmersion_normalizedOverlapToLeft :
    IsOpenImmersion (normalizedOverlapToLeft R σ d j l) :=
  MorphismProperty.of_isPullback (isPullback_normalizedOverlapToLeft R σ d j l).flip inferInstance

/-- The overlap embeds openly in the right universal chart family. -/
instance isOpenImmersion_normalizedOverlapToRight :
    IsOpenImmersion (normalizedOverlapToRight R σ d j l) :=
  MorphismProperty.of_isPullback (isPullback_normalizedOverlapToRight R σ d j l).flip inferInstance

/-- The left restriction identification has the canonical first projection. -/
theorem normalizedOverlapLeftFiberIso_hom_fst :
    (normalizedOverlapLeftFiberIso R σ d j l).hom ≫
      pullback.fst (normalizedFamilyToBase R σ d j)
        (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I₀ j l))) =
      normalizedOverlapToLeft R σ d j l :=
  scaledHypersurfaceFiberIso_hom_fst _ _ _ _ _ _ _ _

/-- The right restriction identification has the canonical first projection. -/
theorem normalizedOverlapRightFiberIso_hom_fst :
    (normalizedOverlapRightFiberIso R σ d j l).hom ≫
      pullback.fst (normalizedFamilyToBase R σ d l)
        (Spec.map (CommRingCat.ofHom (chartOverlapRightMap I₀ j l))) =
      normalizedOverlapToRight R σ d j l :=
  hypersurfaceBaseChangeIso_hom_fst _ _ _

/-- The left restriction identification preserves the actual overlap base map. -/
theorem normalizedOverlapLeftFiberIso_hom_snd :
    (normalizedOverlapLeftFiberIso R σ d j l).hom ≫
      pullback.snd (normalizedFamilyToBase R σ d j)
        (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I₀ j l))) =
      normalizedOverlapToBase R σ d j l :=
  scaledHypersurfaceFiberIso_hom_snd _ _ _ _ _ _ _ _

/-- The right restriction identification preserves that same overlap base map. -/
theorem normalizedOverlapRightFiberIso_hom_snd :
    (normalizedOverlapRightFiberIso R σ d j l).hom ≫
      pullback.snd (normalizedFamilyToBase R σ d l)
        (Spec.map (CommRingCat.ofHom (chartOverlapRightMap I₀ j l))) =
      normalizedOverlapToBase R σ d j l :=
  hypersurfaceBaseChangeIso_hom_snd _ _ _

/-- The previously constructed family-overlap isomorphism is exactly the
comparison of the two canonical hypersurface restriction identifications. -/
theorem normalizedOverlapLeftFiberIso_hom_familyIso :
    (normalizedOverlapLeftFiberIso R σ d j l).hom ≫
      (normalizedOverlapFamilyIso R σ d j l).hom =
    (normalizedOverlapRightFiberIso R σ d j l).hom := by
  let s := hypersurfaceScalingIso _ ((chartOverlapUnit I₀ j l)⁻¹).isUnit
    ((normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
    ((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l))
  let e := hypersurfaceReductionIso (chartOverlapLeftMap I₀ j l)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (C (↑((chartOverlapUnit I₀ j l)⁻¹) : ChartOverlapRing I₀ j l) *
      (normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
    (((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l)).C_mul _)
    (normalizedForm_overlap_relation R σ d j l)
  let t := hypersurfaceBaseChangeIso (chartOverlapRightMap I₀ j l)
    (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)
  exact (Category.assoc s.inv e.hom _).trans
    ((congrArg (fun f ↦ s.inv ≫ f) (e.hom_inv_id_assoc (s.hom ≫ t.hom))).trans
      (s.inv_hom_id_assoc t.hom))

end UniversalHomogeneous
end AllCharacteristics
