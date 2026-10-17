import AllCharacteristics.ProjectiveChartOverlap
import AllCharacteristics.NormalizedCoefficientTransitions

/-!
# Universal coefficient families on actual projective chart intersections

The actual restriction homomorphisms from the two projective coefficient
charts are the normalized transition maps already constructed. Their universal
equations differ by the explicit overlap unit, and their actual base-changed
hypersurface families are isomorphic over the intersection spectrum.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable (R : Type u) [CommRing R] (σ : Type) (d : ℕ)
variable (j l : Monomials σ d)
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => ParameterIdeal R σ d

/-- The normalized transition map is the actual left restriction to the chart overlap. -/
theorem normalizedChartTransition_eq_overlapLeftMap :
    normalizedChartTransition j l (chartOverlapRightMap I₀ j l) (chartOverlapUnit I₀ j l)
      (chartOverlapUnit_val I₀ j l) = chartOverlapLeftMap I₀ j l := by
  apply projectiveChartMap_ext j
  · apply RingHom.ext
    intro r
    change normalizedChartTransition j l (chartOverlapRightMap I₀ j l) (chartOverlapUnit I₀ j l)
      (chartOverlapUnit_val I₀ j l) (chartBaseMap I₀ j r) =
        chartOverlapLeftMap I₀ j l (chartBaseMap I₀ j r)
    rw [normalizedChartTransition_baseMap, chartOverlapRightMap_baseMap, chartOverlapLeftMap_baseMap]
  · intro m
    exact (normalizedChartTransition_coordinate j l (chartOverlapRightMap I₀ j l)
      (chartOverlapUnit I₀ j l) (chartOverlapUnit_val I₀ j l) m).trans
        (chartOverlap_coordinate_relation I₀ j l m).symm

variable [Finite σ]

/-- The actual restrictions of the universal equations differ by the overlap unit. -/
theorem normalizedForm_overlap_relation :
    (normalizedForm R σ d j).map (chartOverlapLeftMap I₀ j l) =
      C (↑((chartOverlapUnit I₀ j l)⁻¹) : ChartOverlapRing I₀ j l) *
        (normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l) := by
  have h := map_normalizedForm_transition j l (chartOverlapRightMap I₀ j l)
    (chartOverlapUnit I₀ j l) (chartOverlapUnit_val I₀ j l)
  rw [normalizedChartTransition_eq_overlapLeftMap R σ d j l] at h
  exact h

/-- The two actual universal coefficient-chart families agree over their intersection. -/
noncomputable def normalizedOverlapFamilyIso :
    pullback (normalizedFamilyToBase R σ d j)
      (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I₀ j l))) ≅
    pullback (normalizedFamilyToBase R σ d l)
      (Spec.map (CommRingCat.ofHom (chartOverlapRightMap I₀ j l))) :=
  (hypersurfaceReductionIso (chartOverlapLeftMap I₀ j l)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (C (↑((chartOverlapUnit I₀ j l)⁻¹) : ChartOverlapRing I₀ j l) *
      (normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
    (((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l)).C_mul _)
    (normalizedForm_overlap_relation R σ d j l)).symm ≪≫
      (hypersurfaceScalingIso _ ((chartOverlapUnit I₀ j l)⁻¹).isUnit
        ((normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
        ((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l)) ≪≫
        hypersurfaceBaseChangeIso (chartOverlapRightMap I₀ j l)
          (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l))

/-- The overlap-family isomorphism is over the actual intersection spectrum. -/
theorem normalizedOverlapFamilyIso_hom_snd :
    (normalizedOverlapFamilyIso R σ d j l).hom ≫
      pullback.snd (normalizedFamilyToBase R σ d l)
        (Spec.map (CommRingCat.ofHom (chartOverlapRightMap I₀ j l))) =
    pullback.snd (normalizedFamilyToBase R σ d j)
      (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I₀ j l))) := by
  let e := hypersurfaceReductionIso (chartOverlapLeftMap I₀ j l)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (C (↑((chartOverlapUnit I₀ j l)⁻¹) : ChartOverlapRing I₀ j l) *
      (normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
    (((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l)).C_mul _)
    (normalizedForm_overlap_relation R σ d j l)
  let s := hypersurfaceScalingIso _ ((chartOverlapUnit I₀ j l)⁻¹).isUnit
    ((normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
    ((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l))
  let t := hypersurfaceBaseChangeIso (chartOverlapRightMap I₀ j l)
    (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)
  have he := e.inv_comp_eq.mpr (hypersurfaceReductionIso_hom_snd (chartOverlapLeftMap I₀ j l)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j) _ _
    (normalizedForm_overlap_relation R σ d j l)).symm
  have hs := hypersurfaceScalingIso_hom_toBase _ ((chartOverlapUnit I₀ j l)⁻¹).isUnit
    ((normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
    ((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l))
  have ht := hypersurfaceBaseChangeIso_hom_snd (chartOverlapRightMap I₀ j l)
    (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)
  exact (Category.assoc e.inv (s.hom ≫ t.hom) _).trans
    ((congrArg (fun f ↦ e.inv ≫ f)
      ((Category.assoc s.hom t.hom _).trans ((congrArg (fun f ↦ s.hom ≫ f) ht).trans hs))).trans he)

end UniversalHomogeneous
end AllCharacteristics
