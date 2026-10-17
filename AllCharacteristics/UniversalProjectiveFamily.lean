import AllCharacteristics.UniversalTripleFamilyPullback
import AllCharacteristics.OverlapCompositionGluing
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The global universal projective hypersurface family

The normalized hypersurfaces over the projective coefficient charts glue along
their actual overlap hypersurfaces. The gluing cocycle comes from the actual
triple intersections. Their structure maps descend to a morphism from this
glued scheme to the projective coefficient space.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The complete scheme gluing data of the normalized universal chart families. -/
noncomputable def projectiveUniversalGlueData : Scheme.GlueData.{u} := by
  let U : ULift.{u} (Monomials σ d) → Scheme.{u} := fun i ↦
    hypersurface (normalizedForm R σ d i.down) (normalizedForm_isHomogeneous R σ d i.down)
  let V : ULift.{u} (Monomials σ d) → ULift.{u} (Monomials σ d) → Scheme.{u} := fun i j ↦
    normalizedOverlapHypersurface R σ d i.down j.down
  let left : ∀ i j, V i j ⟶ U i := fun i j ↦ normalizedOverlapToLeft R σ d i.down j.down
  let right : ∀ i j, V i j ⟶ U j := fun i j ↦ normalizedOverlapToRight R σ d i.down j.down
  letI : ∀ i j, Mono (left i j) := fun i j ↦
    inferInstanceAs (Mono (normalizedOverlapToLeft R σ d i.down j.down))
  letI : ∀ i, IsIso (left i i) := fun i ↦
    inferInstanceAs (IsIso (normalizedOverlapToLeft R σ d i.down i.down))
  exact
    { toGlueData := OverlapComposition.glueData U V left right
        (fun i j ↦ normalizedOverlapSwap R σ d i.down j.down)
        (fun i j ↦ normalizedOverlapSwap_comp_left R σ d i.down j.down)
        (fun i j l ↦ normalizedOverlapCross R σ d i.down j.down l.down)
        (fun i j l ↦ normalizedOverlapCross_left R σ d i.down j.down l.down)
        (fun i j l ↦ normalizedOverlapCross_right R σ d i.down j.down l.down)
        (fun i j ↦ normalizedOverlapSwap_comp_swap R σ d i.down j.down)
        (fun i ↦ normalizedOverlapSwap_self R σ d i.down)
      f_open := fun i j ↦
        inferInstanceAs (IsOpenImmersion (normalizedOverlapToLeft R σ d i.down j.down)) }

/-- The global universal hypersurface scheme over projective equation parameters. -/
noncomputable def projectiveUniversalFamily : Scheme.{u} :=
  (projectiveUniversalGlueData R σ d).glued

/-- Each normalized universal chart family embeds in the global family. -/
noncomputable def projectiveUniversalChartι (i : Monomials σ d) :
    hypersurface (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i) ⟶
      projectiveUniversalFamily R σ d :=
  (projectiveUniversalGlueData R σ d).ι (ULift.up i)

/-- The normalized chart embeddings are open immersions. -/
instance isOpenImmersion_projectiveUniversalChartι (i : Monomials σ d) :
    IsOpenImmersion (projectiveUniversalChartι R σ d i) :=
  Scheme.GlueData.ι_isOpenImmersion (projectiveUniversalGlueData R σ d) (ULift.up i)

/-- Every point of the glued universal family belongs to a normalized chart family. -/
theorem projectiveUniversalChartι_jointly_surjective (x : projectiveUniversalFamily R σ d) :
    ∃ (i : Monomials σ d)
      (y : hypersurface (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)),
      projectiveUniversalChartι R σ d i y = x := by
  obtain ⟨i, y, hy⟩ := (projectiveUniversalGlueData R σ d).ι_jointly_surjective x
  exact ⟨i.down, y, hy⟩

/-- The two chart structure maps agree on the actual overlap over projective parameters. -/
theorem normalizedOverlapTo_projectiveBase (i j : Monomials σ d) :
    normalizedOverlapToLeft R σ d i j ≫ normalizedFamilyToBase R σ d i ≫ parameterChartι R σ d i =
      normalizedOverlapToRight R σ d i j ≫ normalizedFamilyToBase R σ d j ≫
        parameterChartι R σ d j := by
  change normalizedOverlapToLeft R σ d i j ≫ normalizedFamilyToBase R σ d i ≫
      chartι (ParameterIdeal R σ d) i =
    normalizedOverlapToRight R σ d i j ≫ normalizedFamilyToBase R σ d j ≫
      chartι (ParameterIdeal R σ d) j
  rw [← Category.assoc, (isPullback_normalizedOverlapToLeft R σ d i j).w,
    Category.assoc, chartOverlapLeftMap_toProj,
    ← chartOverlapRightMap_toProj (ParameterIdeal R σ d) i j,
    ← Category.assoc, ← (isPullback_normalizedOverlapToRight R σ d i j).w, Category.assoc]

/-- The global universal family's structure map to the projective coefficient space. -/
noncomputable def projectiveUniversalToBase :
    projectiveUniversalFamily R σ d ⟶ projectiveParameters R σ d :=
  Multicoequalizer.desc (projectiveUniversalGlueData R σ d).toGlueData.diagram
    (projectiveParameters R σ d)
    (fun i ↦ normalizedFamilyToBase R σ d i.down ≫ parameterChartι R σ d i.down)
    (by
      intro p
      change normalizedOverlapToLeft R σ d p.1.down p.2.down ≫
          (normalizedFamilyToBase R σ d p.1.down ≫ parameterChartι R σ d p.1.down) =
        (normalizedOverlapSwap R σ d p.1.down p.2.down ≫
          normalizedOverlapToLeft R σ d p.2.down p.1.down) ≫
          (normalizedFamilyToBase R σ d p.2.down ≫ parameterChartι R σ d p.2.down)
      rw [normalizedOverlapSwap_comp_left]
      exact normalizedOverlapTo_projectiveBase R σ d p.1.down p.2.down)

/-- Restricting the global structure map recovers each normalized chart structure map. -/
theorem projectiveUniversalChartι_toBase (i : Monomials σ d) :
    projectiveUniversalChartι R σ d i ≫ projectiveUniversalToBase R σ d =
      normalizedFamilyToBase R σ d i ≫ parameterChartι R σ d i :=
by
  unfold projectiveUniversalChartι projectiveUniversalToBase
  exact Multicoequalizer.π_desc (projectiveUniversalGlueData R σ d).toGlueData.diagram
    (projectiveParameters R σ d) _ _ (ULift.up i)

/-- The two embeddings of an overlap agree in the global universal family. -/
theorem projectiveUniversalChartι_overlap (i j : Monomials σ d) :
    normalizedOverlapToLeft R σ d i j ≫ projectiveUniversalChartι R σ d i =
      normalizedOverlapToRight R σ d i j ≫ projectiveUniversalChartι R σ d j := by
  have h := (projectiveUniversalGlueData R σ d).glue_condition (ULift.up i) (ULift.up j)
  change normalizedOverlapSwap R σ d i j ≫ normalizedOverlapToLeft R σ d j i ≫
    projectiveUniversalChartι R σ d j =
      normalizedOverlapToLeft R σ d i j ≫ projectiveUniversalChartι R σ d i at h
  rw [← Category.assoc, normalizedOverlapSwap_comp_left] at h
  exact h.symm

end UniversalHomogeneous
end AllCharacteristics
