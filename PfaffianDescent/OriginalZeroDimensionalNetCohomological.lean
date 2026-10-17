import PfaffianDescent.OriginalCubicFiniteNetCohomological
import PfaffianDescent.OriginalThreeQuadricOTwoCohomologicalHZero
import PfaffianDescent.ProjectiveZeroDimensionalFiniteStructure
import AllCharacteristics.SectionFour

/-! SOURCE ONLY / UNVERIFIED. Literal lem:net-of-quadrics with the actual
zero-dimensional intersection hypothesis. All finite morphisms, the original
closed lift, regularity, exactness, cohomology and decomposition are derived
internally. Original Z, cubic F and three ground quadrics remain unchanged. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

abbrev originalLiteralQuadraticNetIdeal (f g h : PS 2) :=
  tripleCompleteIntersectionHomogeneousIdeal
    (K := K) (a := 2) (b := 2) (c := 2)
    f.val g.val h.val f.property g.property h.property

/-- Literal original-cubic net lemma; smoothness is not necessary here. -/
theorem originalZeroDimensionalNet_decomposition_by_cohomology
    (f g h : PS 2) (F : PS 3)
    (hW : topologicalKrullDim (scheme (originalLiteralQuadraticNetIdeal f g h)) ≤ 0)
    {Z : Scheme.{u}}
    (j : Z ⟶ hypersurface F.val F.property) [IsClosedImmersion j]
    (hker : (quotientProjMap (originalLiteralQuadraticNetIdeal f g h)).ker ≤
      (j ≫ hypersurfaceToAmbient F.val F.property).ker)
    (hZ : letI : IsFinite (toBase (originalLiteralQuadraticNetIdeal f g h)) :=
        projectiveHomogeneousIdeal_isFinite_of_zeroDimensional _ hW
      letI : IsFinite (j ≫ hypersurfaceToBase F.val F.property) :=
        p3OriginalCubicFiniteNet_source_isFinite f g h F j hker
      AllCharacteristics.finiteSchemeRank (j ≫ hypersurfaceToBase F.val F.property) = 8) :
    ∃ H : PS 1 × PS 1 × PS 1,
      F.val = f.val * H.1.val + g.val * H.2.1.val + h.val * H.2.2.val := by
  letI : IsFinite (toBase (originalLiteralQuadraticNetIdeal f g h)) :=
    projectiveHomogeneousIdeal_isFinite_of_zeroDimensional _ hW
  exact p3OriginalCubicFiniteNet_decomposition_by_cohomology f g h F j hker hZ

private theorem literalNet_rank_eq_of_map_eq {X : Scheme.{u}}
    (a b : X ⟶ Spec (.of K)) [IsFinite a] [IsFinite b] (hab : a = b) :
    AllCharacteristics.finiteSchemeRank a = AllCharacteristics.finiteSchemeRank b := by
  subst b
  rfl

private theorem literalNet_idealHZero_finrank_eq_of_map_eq {Z : Scheme.{u}}
    (a b : Z ⟶ Proj PS) [IsClosedImmersion a] [IsClosedImmersion b] (hab : a = b) :
    Module.finrank K (SchemeModuleGlobalSectionsOver
      (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist a (ProjectiveNegativeTwist.positiveSheafOfModules PS 2))) =
    Module.finrank K (SchemeModuleGlobalSectionsOver
      (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist b (ProjectiveNegativeTwist.positiveSheafOfModules PS 2))) := by
  subst b
  rfl

/-- Literal rem:h^0(I_Z)=3 with zero-dimensional W and original Z in cubic.
The dimension is derived by the actual O(2) tensor resolution and sheaf LES. -/
theorem originalZeroDimensionalNet_idealHZero_finrank_by_cohomology
    (f g h : PS 2) (F : PS 3)
    (hW : topologicalKrullDim (scheme (originalLiteralQuadraticNetIdeal f g h)) ≤ 0)
    {Z : Scheme.{u}}
    (j : Z ⟶ hypersurface F.val F.property) [IsClosedImmersion j]
    (hker : (quotientProjMap (originalLiteralQuadraticNetIdeal f g h)).ker ≤
      (j ≫ hypersurfaceToAmbient F.val F.property).ker)
    (hZ : letI : IsFinite (toBase (originalLiteralQuadraticNetIdeal f g h)) :=
        projectiveHomogeneousIdeal_isFinite_of_zeroDimensional _ hW
      letI : IsFinite (j ≫ hypersurfaceToBase F.val F.property) :=
        p3OriginalCubicFiniteNet_source_isFinite f g h F j hker
      AllCharacteristics.finiteSchemeRank (j ≫ hypersurfaceToBase F.val F.property) = 8) :
    letI : IsClosedImmersion (hypersurfaceToAmbient F.val F.property) :=
      hypersurfaceToAmbient_isClosedImmersion F.val F.property
    letI : IsClosedImmersion (j ≫ hypersurfaceToAmbient F.val F.property) :=
      IsClosedImmersion.comp j (hypersurfaceToAmbient F.val F.property)
    Module.finrank K (SchemeModuleGlobalSectionsOver
      (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (j ≫ hypersurfaceToAmbient F.val F.property)
        (ProjectiveNegativeTwist.positiveSheafOfModules PS 2))) = 3 := by
  letI : IsFinite (toBase (originalLiteralQuadraticNetIdeal f g h)) :=
    projectiveHomogeneousIdeal_isFinite_of_zeroDimensional _ hW
  letI : IsFinite (j ≫ hypersurfaceToBase F.val F.property) :=
    p3OriginalCubicFiniteNet_source_isFinite f g h F j hker
  letI : IsClosedImmersion (hypersurfaceToAmbient F.val F.property) :=
    hypersurfaceToAmbient_isClosedImmersion F.val F.property
  letI : IsClosedImmersion (j ≫ hypersurfaceToAmbient F.val F.property) :=
    IsClosedImmersion.comp j (hypersurfaceToAmbient F.val F.property)
  have hZl : AllCharacteristics.finiteSchemeRank
      (p3OriginalCubicFiniteNetLift f g h F j hker ≫
        toBase (originalLiteralQuadraticNetIdeal f g h)) = 8 :=
    (literalNet_rank_eq_of_map_eq _ _
      (p3OriginalCubicFiniteNetLift_base f g h F j hker)).trans hZ
  have hd := p3OriginalThreeQuadricOTwoIdealHZero_finrank_by_cohomology
    f g h (p3OriginalCubicFiniteNetLift f g h F j hker) hZl
  exact (literalNet_idealHZero_finrank_eq_of_map_eq _ _
    (p3OriginalCubicFiniteNetLift_ambient f g h F j hker)).symm.trans hd

/-- The literal net lemma gives an actual ground section of the original cubic. -/
theorem originalZeroDimensionalNet_section_by_cohomology
    (f g h : PS 2) (F : PS 3)
    (hW : topologicalKrullDim (scheme (originalLiteralQuadraticNetIdeal f g h)) ≤ 0)
    {Z : Scheme.{u}}
    (j : Z ⟶ hypersurface F.val F.property) [IsClosedImmersion j]
    (hker : (quotientProjMap (originalLiteralQuadraticNetIdeal f g h)).ker ≤
      (j ≫ hypersurfaceToAmbient F.val F.property).ker)
    (hZ : letI : IsFinite (toBase (originalLiteralQuadraticNetIdeal f g h)) :=
        projectiveHomogeneousIdeal_isFinite_of_zeroDimensional _ hW
      letI : IsFinite (j ≫ hypersurfaceToBase F.val F.property) :=
        p3OriginalCubicFiniteNet_source_isFinite f g h F j hker
      AllCharacteristics.finiteSchemeRank (j ≫ hypersurfaceToBase F.val F.property) = 8) :
    ∃ s : Spec (.of K) ⟶ hypersurface F.val F.property,
      s ≫ hypersurfaceToBase F.val F.property = 𝟙 _ := by
  obtain ⟨H, hdecomp⟩ :=
    originalZeroDimensionalNet_decomposition_by_cohomology f g h F hW j hker hZ
  apply AllCharacteristics.sectionFour_section_of_cubic_mem_three_quadrics
    F.val f.val g.val h.val F.property f.property g.property h.property
  rw [hdecomp]
  apply Ideal.add_mem
  · apply Ideal.add_mem
    · exact Ideal.mul_mem_right _ _
        (Ideal.subset_span (by simp : f.val ∈ ({f.val, g.val, h.val} : Set _)))
    · exact Ideal.mul_mem_right _ _
        (Ideal.subset_span (by simp : g.val ∈ ({f.val, g.val, h.val} : Set _)))
  · exact Ideal.mul_mem_right _ _
      (Ideal.subset_span (by simp : h.val ∈ ({f.val, g.val, h.val} : Set _)))

end PfaffianDescent
