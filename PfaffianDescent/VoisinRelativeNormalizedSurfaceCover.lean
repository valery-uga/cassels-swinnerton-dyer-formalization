import PfaffianDescent.VoisinRelativeRingTwoCubicIntersection
import AllCharacteristics.ProjectiveCoefficientParameters

/-!
# Normalized parameter-chart cover of the fixed cubic surface family

The projective coefficient charts pull back along the surface family's
parameter map. Each member of the resulting open cover has its canonical
map to a normalized coefficient chart.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {K : Type u} [Field K]
  (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
  {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
  (h : E ⟶ projectiveParameters K (Fin 4) 3)

/-- Pull the normalized parameter charts back to an arbitrary parameter
scheme. -/
noncomputable def fixedCubicParameterChartOpenCover : E.OpenCover :=
  (parameterChartCover K (Fin 4) 3).openCover.pullback₁ h

/-- An affine refinement provides coefficient rings for the local
two-cubic descriptions of the universal family. -/
noncomputable def fixedCubicParameterChartAffineCover : E.AffineOpenCover :=
  (fixedCubicParameterChartOpenCover h).affineRefinement

/-- The map on coefficient rings induced by an affine refinement member's
canonical morphism to its normalized parameter chart. -/
noncomputable def fixedCubicParameterChartAffineCover_coefficientMap
    (j : (fixedCubicParameterChartAffineCover h).I₀) :
    ParameterChartRing K (Fin 4) 3 j.1 →+*
      (fixedCubicParameterChartAffineCover h).X j :=
  (Spec.preimage
    (((fixedCubicParameterChartOpenCover h).X j.1).affineCover.f j.2 ≫
      (parameterChartCover K (Fin 4) 3).openCover.pullbackHom h j.1)).hom

/-- The ground-field algebra structure on an affine cover member, induced
by its actual map to the ground-field spectrum. -/
noncomputable def fixedCubicParameterChartAffineCover_groundAlgebra
    (j : (fixedCubicParameterChartAffineCover h).I₀) :
    Algebra K ((fixedCubicParameterChartAffineCover h).X j) :=
  ((Spec.preimage
    ((fixedCubicParameterChartAffineCover h).f j ≫ k)).hom).toAlgebra

theorem fixedCubicParameterChartAffineCover_toBase
    (j : (fixedCubicParameterChartAffineCover h).I₀) :
    letI : Algebra K ((fixedCubicParameterChartAffineCover h).X j) :=
      fixedCubicParameterChartAffineCover_groundAlgebra k h j
    (fixedCubicParameterChartAffineCover h).f j ≫ k =
      Spec.map (CommRingCat.ofHom
        (algebraMap K ((fixedCubicParameterChartAffineCover h).X j))) := by
  exact (Spec.map_preimage _).symm

/-- Every affine member of the refined parameter cover factors through the
normalized projective coefficient chart specified by its first index. -/
theorem fixedCubicParameterChartAffineCover_factor
    (j : (fixedCubicParameterChartAffineCover h).I₀) :
    ∃ f : ParameterChartRing K (Fin 4) 3 j.1 →+*
        (fixedCubicParameterChartAffineCover h).X j,
      (fixedCubicParameterChartAffineCover h).f j ≫ h =
        Spec.map (CommRingCat.ofHom f) ≫
          parameterChartι K (Fin 4) 3 j.1 := by
  let 𝒰 := (parameterChartCover K (Fin 4) 3).openCover
  let 𝒱 := fixedCubicParameterChartOpenCover h
  let 𝒜 := fixedCubicParameterChartAffineCover h
  let t : Spec (𝒜.X j) ⟶ Spec (.of (ParameterChartRing K (Fin 4) 3 j.1)) :=
    (𝒱.X j.1).affineCover.f j.2 ≫ 𝒰.pullbackHom h j.1
  refine ⟨(Spec.preimage t).hom, ?_⟩
  change 𝒜.f j ≫ h = Spec.map (Spec.preimage t) ≫ 𝒰.f j.1
  rw [Spec.map_preimage]
  change ((𝒱.X j.1).affineCover.f j.2 ≫ 𝒱.f j.1) ≫ h =
    ((𝒱.X j.1).affineCover.f j.2 ≫ 𝒰.pullbackHom h j.1) ≫ 𝒰.f j.1
  have hpb : 𝒱.f j.1 ≫ h =
      𝒰.pullbackHom h j.1 ≫ 𝒰.f j.1 :=
    (Scheme.Cover.pullbackHom_map 𝒰 h j.1).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun w => (𝒱.X j.1).affineCover.f j.2 ≫ w) hpb).trans
      (Category.assoc _ _ _).symm)

theorem fixedCubicParameterChartAffineCover_coefficientMap_factor
    (j : (fixedCubicParameterChartAffineCover h).I₀) :
    (fixedCubicParameterChartAffineCover h).f j ≫ h =
      Spec.map (CommRingCat.ofHom
        (fixedCubicParameterChartAffineCover_coefficientMap h j)) ≫
        parameterChartι K (Fin 4) 3 j.1 := by
  let 𝒰 := (parameterChartCover K (Fin 4) 3).openCover
  let 𝒱 := fixedCubicParameterChartOpenCover h
  let 𝒜 := fixedCubicParameterChartAffineCover h
  let t : Spec (𝒜.X j) ⟶ Spec (.of (ParameterChartRing K (Fin 4) 3 j.1)) :=
    (𝒱.X j.1).affineCover.f j.2 ≫ 𝒰.pullbackHom h j.1
  change 𝒜.f j ≫ h = Spec.map (Spec.preimage t) ≫ 𝒰.f j.1
  rw [Spec.map_preimage]
  change ((𝒱.X j.1).affineCover.f j.2 ≫ 𝒱.f j.1) ≫ h =
    ((𝒱.X j.1).affineCover.f j.2 ≫ 𝒰.pullbackHom h j.1) ≫ 𝒰.f j.1
  have hpb : 𝒱.f j.1 ≫ h =
      𝒰.pullbackHom h j.1 ≫ 𝒰.f j.1 :=
    (Scheme.Cover.pullbackHom_map 𝒰 h j.1).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun w => (𝒱.X j.1).affineCover.f j.2 ≫ w) hpb).trans
      (Category.assoc _ _ _).symm)

/-- The coefficient map on each affine cover member is automatically
compatible with its ground-field map. -/
theorem fixedCubicParameterChartAffineCover_factor_overBase
    (hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k)
    (j : (fixedCubicParameterChartAffineCover h).I₀) :
    ∃ f : ParameterChartRing K (Fin 4) 3 j.1 →+*
        (fixedCubicParameterChartAffineCover h).X j,
      (fixedCubicParameterChartAffineCover h).f j ≫ h =
          Spec.map (CommRingCat.ofHom f) ≫
            parameterChartι K (Fin 4) 3 j.1 ∧
      f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j.1) =
        (Spec.preimage
          ((fixedCubicParameterChartAffineCover h).f j ≫ k)).hom := by
  obtain ⟨f, hf⟩ := fixedCubicParameterChartAffineCover_factor h j
  refine ⟨f, hf, ?_⟩
  exact normalizedParameterChart_baseMap h k hk
    (Spec.preimage
      ((fixedCubicParameterChartAffineCover h).f j ≫ k)).hom
    ((fixedCubicParameterChartAffineCover h).f j)
    (Spec.map_preimage _).symm j.1 f hf

theorem fixedCubicParameterChartAffineCover_coefficientMap_base
    (hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k)
    (j : (fixedCubicParameterChartAffineCover h).I₀) :
    (fixedCubicParameterChartAffineCover_coefficientMap h j).comp
        (chartBaseMap (ParameterIdeal K (Fin 4) 3) j.1) =
      (Spec.preimage
        ((fixedCubicParameterChartAffineCover h).f j ≫ k)).hom := by
  exact normalizedParameterChart_baseMap h k hk
    (Spec.preimage
      ((fixedCubicParameterChartAffineCover h).f j ≫ k)).hom
    ((fixedCubicParameterChartAffineCover h).f j)
    (Spec.map_preimage _).symm j.1
    (fixedCubicParameterChartAffineCover_coefficientMap h j)
    (fixedCubicParameterChartAffineCover_coefficientMap_factor h j)

/-- The open cover of the constant cubic surface family obtained from
normalized equation-parameter charts. -/
noncomputable def fixedCubicSurfaceParameterChartOpenCover :
    (fixedCubicSurfaceFamily a ha k).OpenCover :=
  (parameterChartCover K (Fin 4) 3).openCover.pullback₁
    (pullback.snd (hypersurfaceToBase a ha) k ≫ h)

/-- The canonical map from a surface-family cover member to its normalized
equation-parameter chart. -/
noncomputable def fixedCubicSurfaceParameterChartMap
    (j : (fixedCubicSurfaceParameterChartOpenCover a ha k h).I₀) :
    (fixedCubicSurfaceParameterChartOpenCover a ha k h).X j ⟶
      Spec (.of (ParameterChartRing K (Fin 4) 3 j)) :=
  (parameterChartCover K (Fin 4) 3).openCover.pullbackHom
    (pullback.snd (hypersurfaceToBase a ha) k ≫ h) j

/-- On a normalized cover member, the chart inclusion recovers the actual
parameter map of the fixed cubic surface family. -/
theorem fixedCubicSurfaceParameterChartMap_comp
    (j : (fixedCubicSurfaceParameterChartOpenCover a ha k h).I₀) :
    fixedCubicSurfaceParameterChartMap a ha k h j ≫
        parameterChartι K (Fin 4) 3 j =
      (fixedCubicSurfaceParameterChartOpenCover a ha k h).f j ≫
        (pullback.snd (hypersurfaceToBase a ha) k ≫ h) := by
  exact Scheme.Cover.pullbackHom_map
    (parameterChartCover K (Fin 4) 3).openCover
    (pullback.snd (hypersurfaceToBase a ha) k ≫ h) j

end PfaffianDescent
