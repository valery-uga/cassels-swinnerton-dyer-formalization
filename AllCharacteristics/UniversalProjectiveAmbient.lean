import AllCharacteristics.HypersurfaceAmbientNaturality
import AllCharacteristics.UniversalProjectiveFamily

/-!
# The ambient map of the global universal projective hypersurface

The normalized universal hypersurfaces on coefficient charts carry canonical
maps to one fixed ambient projective space.  Their agreement on overlaps
descends this map to the glued universal family.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => ParameterIdeal R σ d

/-- The canonical ambient map of a normalized universal hypersurface chart. -/
noncomputable def normalizedFamilyToAmbient (i : Monomials σ d) :
    hypersurface (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i) ⟶
      Proj (MvPolynomial.homogeneousSubmodule σ R) :=
  hypersurfaceToAmbient (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i) ≫
    ambientCoefficientMap (σ := σ) (chartBaseMap I₀ i)

/-- The two coefficient-chart maps to an overlap induce the same composite
coefficient map from the original base ring. -/
theorem chartOverlap_comp_chartBaseMap (i j : Monomials σ d) :
    (chartOverlapLeftMap I₀ i j).comp (chartBaseMap I₀ i) =
      (chartOverlapRightMap I₀ i j).comp (chartBaseMap I₀ j) := by
  ext r
  simp only [RingHom.comp_apply]
  rw [chartOverlapLeftMap_baseMap, chartOverlapRightMap_baseMap]

/-- Restriction through the left coefficient chart is compatible with the
ambient map of the common overlap hypersurface. -/
theorem normalizedOverlapToLeft_comp_hypersurfaceToAmbient (i j : Monomials σ d) :
    normalizedOverlapToLeft R σ d i j ≫
      hypersurfaceToAmbient (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i) =
    hypersurfaceToAmbient
        ((normalizedForm R σ d j).map (chartOverlapRightMap I₀ i j))
        ((normalizedForm_isHomogeneous R σ d j).map (chartOverlapRightMap I₀ i j)) ≫
      ambientCoefficientMap (σ := σ) (chartOverlapLeftMap I₀ i j) :=
  scaledHypersurfaceMap_comp_hypersurfaceToAmbient
    (chartOverlapLeftMap I₀ i j) (normalizedForm R σ d i)
    (normalizedForm_isHomogeneous R σ d i)
    ((normalizedForm R σ d j).map (chartOverlapRightMap I₀ i j))
    ((normalizedForm_isHomogeneous R σ d j).map (chartOverlapRightMap I₀ i j))
    (↑((chartOverlapUnit I₀ i j)⁻¹) : ChartOverlapRing I₀ i j)
    ((chartOverlapUnit I₀ i j)⁻¹).isUnit
    (normalizedForm_overlap_relation R σ d i j)

/-- Restriction through the right coefficient chart is compatible with the
ambient map of the common overlap hypersurface. -/
theorem normalizedOverlapToRight_comp_hypersurfaceToAmbient (i j : Monomials σ d) :
    normalizedOverlapToRight R σ d i j ≫
      hypersurfaceToAmbient (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j) =
    hypersurfaceToAmbient
        ((normalizedForm R σ d j).map (chartOverlapRightMap I₀ i j))
        ((normalizedForm_isHomogeneous R σ d j).map (chartOverlapRightMap I₀ i j)) ≫
      ambientCoefficientMap (σ := σ) (chartOverlapRightMap I₀ i j) :=
  hypersurfaceBaseChangeMap_comp_hypersurfaceToAmbient
    (chartOverlapRightMap I₀ i j) (normalizedForm R σ d j)
    (normalizedForm_isHomogeneous R σ d j)

/-- The ambient maps of normalized universal hypersurface charts agree on
their actual overlap hypersurface. -/
theorem normalizedOverlapToAmbient (i j : Monomials σ d) :
    normalizedOverlapToLeft R σ d i j ≫ normalizedFamilyToAmbient R σ d i =
      normalizedOverlapToRight R σ d i j ≫ normalizedFamilyToAmbient R σ d j := by
  unfold normalizedFamilyToAmbient
  have hbase := chartOverlap_comp_chartBaseMap R σ d i j
  have hambient := congrArg (ambientCoefficientMap (σ := σ)) hbase
  have hleft :
      (normalizedOverlapToLeft R σ d i j ≫
        hypersurfaceToAmbient (normalizedForm R σ d i)
          (normalizedForm_isHomogeneous R σ d i)) ≫
        ambientCoefficientMap (σ := σ) (chartBaseMap I₀ i) =
      (hypersurfaceToAmbient
        ((normalizedForm R σ d j).map (chartOverlapRightMap I₀ i j))
        ((normalizedForm_isHomogeneous R σ d j).map (chartOverlapRightMap I₀ i j)) ≫
        ambientCoefficientMap (σ := σ) (chartOverlapLeftMap I₀ i j)) ≫
        ambientCoefficientMap (σ := σ) (chartBaseMap I₀ i) :=
    congrArg (fun h : normalizedOverlapHypersurface R σ d i j ⟶
        Proj (MvPolynomial.homogeneousSubmodule σ (ParameterChartRing R σ d i)) ↦
      h ≫ ambientCoefficientMap (σ := σ) (chartBaseMap I₀ i))
      (normalizedOverlapToLeft_comp_hypersurfaceToAmbient R σ d i j)
  refine (Category.assoc _ _ _).symm.trans (hleft.trans ((Category.assoc _ _ _).trans ?_))
  refine (congrArg (fun h ↦ hypersurfaceToAmbient
      ((normalizedForm R σ d j).map (chartOverlapRightMap I₀ i j))
      ((normalizedForm_isHomogeneous R σ d j).map (chartOverlapRightMap I₀ i j)) ≫ h)
      (ambientCoefficientMap_comp (σ := σ) (chartBaseMap I₀ i)
        (chartOverlapLeftMap I₀ i j))).trans ?_
  refine (congrArg (fun h ↦ hypersurfaceToAmbient
      ((normalizedForm R σ d j).map (chartOverlapRightMap I₀ i j))
      ((normalizedForm_isHomogeneous R σ d j).map (chartOverlapRightMap I₀ i j)) ≫ h)
      hambient).trans ?_
  refine (congrArg (fun h ↦ hypersurfaceToAmbient
      ((normalizedForm R σ d j).map (chartOverlapRightMap I₀ i j))
      ((normalizedForm_isHomogeneous R σ d j).map (chartOverlapRightMap I₀ i j)) ≫ h)
      (ambientCoefficientMap_comp (σ := σ) (chartBaseMap I₀ j)
        (chartOverlapRightMap I₀ i j)).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun h : normalizedOverlapHypersurface R σ d i j ⟶
      Proj (MvPolynomial.homogeneousSubmodule σ (ParameterChartRing R σ d j)) ↦
    h ≫ ambientCoefficientMap (σ := σ) (chartBaseMap I₀ j))
    (normalizedOverlapToRight_comp_hypersurfaceToAmbient R σ d i j).symm).trans ?_
  exact Category.assoc _ _ _

/-- The ambient projective-space map of the glued universal hypersurface. -/
noncomputable def projectiveUniversalToAmbient :
    projectiveUniversalFamily R σ d ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) :=
  Multicoequalizer.desc (projectiveUniversalGlueData R σ d).toGlueData.diagram
    (Proj (MvPolynomial.homogeneousSubmodule σ R))
    (fun i ↦ normalizedFamilyToAmbient R σ d i.down)
    (by
      intro p
      change normalizedOverlapToLeft R σ d p.1.down p.2.down ≫
          normalizedFamilyToAmbient R σ d p.1.down =
        (normalizedOverlapSwap R σ d p.1.down p.2.down ≫
          normalizedOverlapToLeft R σ d p.2.down p.1.down) ≫
          normalizedFamilyToAmbient R σ d p.2.down
      rw [normalizedOverlapSwap_comp_left]
      exact normalizedOverlapToAmbient R σ d p.1.down p.2.down)

/-- The universal hypersurface as an incidence family inside the product of
its fixed ambient projective space and its projective coefficient space. -/
noncomputable def projectiveUniversalIncidence :
    projectiveUniversalFamily R σ d ⟶
      Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯ projectiveParameters R σ d :=
  prod.lift (projectiveUniversalToAmbient R σ d) (projectiveUniversalToBase R σ d)

/-- The first projection of the universal incidence morphism is its ambient
projective-space map. -/
theorem projectiveUniversalIncidence_fst :
    projectiveUniversalIncidence R σ d ≫ prod.fst = projectiveUniversalToAmbient R σ d :=
  prod.lift_fst _ _

/-- The second projection of the universal incidence morphism is its
coefficient-parameter map. -/
theorem projectiveUniversalIncidence_snd :
    projectiveUniversalIncidence R σ d ≫ prod.snd = projectiveUniversalToBase R σ d :=
  prod.lift_snd _ _

/-- Restricting the global ambient map to a normalized chart recovers that
chart's canonical ambient map. -/
theorem projectiveUniversalChartι_toAmbient (i : Monomials σ d) :
    projectiveUniversalChartι R σ d i ≫ projectiveUniversalToAmbient R σ d =
      normalizedFamilyToAmbient R σ d i := by
  unfold projectiveUniversalChartι projectiveUniversalToAmbient
  exact Multicoequalizer.π_desc (projectiveUniversalGlueData R σ d).toGlueData.diagram
    (Proj (MvPolynomial.homogeneousSubmodule σ R)) _ _ (ULift.up i)

/-- On each coefficient chart, the global incidence morphism is the pair of
the chart's ambient map and its coefficient-parameter map. -/
theorem projectiveUniversalChartι_toIncidence (i : Monomials σ d) :
    projectiveUniversalChartι R σ d i ≫ projectiveUniversalIncidence R σ d =
      prod.lift (normalizedFamilyToAmbient R σ d i)
        (normalizedFamilyToBase R σ d i ≫ parameterChartι R σ d i) := by
  apply prod.hom_ext
  · rw [Category.assoc, projectiveUniversalIncidence_fst,
      projectiveUniversalChartι_toAmbient, prod.lift_fst]
  · rw [Category.assoc, projectiveUniversalIncidence_snd,
      projectiveUniversalChartι_toBase, prod.lift_snd]

end UniversalHomogeneous
end AllCharacteristics
