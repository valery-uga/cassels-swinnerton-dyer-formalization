import PfaffianDescent.IntrinsicGroundQuadraticBasisIdeal
import PfaffianDescent.ActualP3IdealQuadraticGlobalBase
import PfaffianDescent.OriginalThreeQuadricContainedCubicSection
import AllCharacteristics.SectionFour
import PfaffianDescent.ProjectiveZeroDimensionalFiniteStructure

/-! SOURCE ONLY / UNVERIFIED. The original full quadratic base constructs
its ground basis, then the literal O(3) cohomological proof yields the cubic
decomposition and a ground section. The ground dimension predecessor must
first be checked with its genuine O(2) proof replacement. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem groundNet_rank_eq_of_map_eq {X : Scheme.{u}}
    (a b : X ⟶ Spec (.of K)) [IsFinite a] [IsFinite b] (hab : a = b) :
    AllCharacteristics.finiteSchemeRank a = AllCharacteristics.finiteSchemeRank b := by
  subst b
  rfl

/-- No basis, finite triple, regularity, resolution, H0 dimension or
decomposition is supplied by the caller. -/
theorem originalFullQuadraticBase_section_by_cohomology
    {Z : Scheme.{u}} (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    [IsFinite (i ≫ ambientToBase)]
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ ambientToBase) = 8)
    [IsFinite (toBase (p3ActualIdealQuadraticGlobalBaseIdeal i))]
    (F : PS 3)
    (hF : (hypersurfaceToAmbient F.val F.property).ker ≤ i.ker) :
    ∃ s : Spec (.of K) ⟶ hypersurface F.val F.property,
      s ≫ hypersurfaceToBase F.val F.property = 𝟙 _ := by
  letI : IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i)) := by
    rw [← p3ActualIdealQuadraticGlobalBaseIdeal_eq_intrinsic i]
    infer_instance
  let b := intrinsicGroundQuadraticBasis i hZ
  let f : PS 2 := ⟨(b 0).val,
    intrinsicFullQuadraticSystem_homogeneous i _ (b 0).property⟩
  let g : PS 2 := ⟨(b 1).val,
    intrinsicFullQuadraticSystem_homogeneous i _ (b 1).property⟩
  let h : PS 2 := ⟨(b 2).val,
    intrinsicFullQuadraticSystem_homogeneous i _ (b 2).property⟩
  let T := tripleCompleteIntersectionHomogeneousIdeal
    (K := K) (a := 2) (b := 2) (c := 2)
    f.val g.val h.val f.property g.property h.property
  letI : IsFinite (toBase T) := intrinsicGroundQuadraticBasis_triple_isFinite i hZ
  have hker : (quotientProjMap T).ker ≤ i.ker :=
    intrinsicFullQuadraticTripleIdeal_ker_le i b
  let l := IsClosedImmersion.lift (quotientProjMap T) i hker
  have hl : l ≫ quotientProjMap T = i :=
    IsClosedImmersion.lift_fac (quotientProjMap T) i hker
  letI : IsClosedImmersion (l ≫ quotientProjMap T) := hl.symm ▸ inferInstance
  letI : IsClosedImmersion l := IsClosedImmersion.of_comp l (quotientProjMap T)
  have hb : l ≫ toBase T = i ≫ ambientToBase := by
    rw [← quotientProjMap_toBase T, ← Category.assoc, hl]
  have hZl : AllCharacteristics.finiteSchemeRank (l ≫ toBase T) = 8 :=
    (groundNet_rank_eq_of_map_eq _ _ hb).trans hZ
  have hFl : (hypersurfaceToAmbient F.val F.property).ker ≤
      (l ≫ quotientProjMap T).ker := by
    rw [hl]
    exact hF
  obtain ⟨H, hdecomp⟩ :=
    p3OriginalThreeQuadricContainedCubic_decomposition_by_cohomology
      f g h l hZl F hFl
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

/-- Literal zero-dimensional full-base hypothesis, on the original ambient Z.
Finiteness of that base is derived internally, including its nilpotents. -/
theorem originalZeroDimensionalFullQuadraticBase_section_by_cohomology
    {Z : Scheme.{u}} (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    [IsFinite (i ≫ ambientToBase)]
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ ambientToBase) = 8)
    (hzero : topologicalKrullDim
      (scheme (p3ActualIdealQuadraticGlobalBaseIdeal i)) ≤ 0)
    (F : PS 3)
    (hF : (hypersurfaceToAmbient F.val F.property).ker ≤ i.ker) :
    ∃ s : Spec (.of K) ⟶ hypersurface F.val F.property,
      s ≫ hypersurfaceToBase F.val F.property = 𝟙 _ := by
  letI : IsFinite (toBase (p3ActualIdealQuadraticGlobalBaseIdeal i)) :=
    projectiveHomogeneousIdeal_isFinite_of_zeroDimensional _ hzero
  exact originalFullQuadraticBase_section_by_cohomology i hZ F hF

/-- Original-cubic version of prop:existence-of-point. The actual closed
Z is preserved; no quadrics, basis, H0 dimension or decomposition is supplied.
Smoothness is unnecessary for this implication. -/
theorem originalCubicZeroDimensionalFullQuadraticBase_section_by_cohomology
    (F : PS 3) {Z : Scheme.{u}}
    (j : Z ⟶ hypersurface F.val F.property) [IsClosedImmersion j]
    [IsFinite (j ≫ hypersurfaceToBase F.val F.property)]
    (hZ : AllCharacteristics.finiteSchemeRank
      (j ≫ hypersurfaceToBase F.val F.property) = 8)
    (hzero : letI : IsClosedImmersion (hypersurfaceToAmbient F.val F.property) :=
        hypersurfaceToAmbient_isClosedImmersion F.val F.property
      letI : IsClosedImmersion (j ≫ hypersurfaceToAmbient F.val F.property) :=
        IsClosedImmersion.comp j (hypersurfaceToAmbient F.val F.property)
      topologicalKrullDim (scheme (p3ActualIdealQuadraticGlobalBaseIdeal
        (j ≫ hypersurfaceToAmbient F.val F.property))) ≤ 0) :
    ∃ s : Spec (.of K) ⟶ hypersurface F.val F.property,
      s ≫ hypersurfaceToBase F.val F.property = 𝟙 _ := by
  letI : IsClosedImmersion (hypersurfaceToAmbient F.val F.property) :=
    hypersurfaceToAmbient_isClosedImmersion F.val F.property
  let i := j ≫ hypersurfaceToAmbient F.val F.property
  letI : IsClosedImmersion i :=
    IsClosedImmersion.comp j (hypersurfaceToAmbient F.val F.property)
  have hb : i ≫ ambientToBase = j ≫ hypersurfaceToBase F.val F.property := by
    exact (Category.assoc j (hypersurfaceToAmbient F.val F.property)
      (ambientToBase (R := K) (σ := Fin 4))).trans
      (congrArg (fun a => j ≫ a)
        (quotientProjMap_toBase (R := K) (σ := Fin 4)
          (equationIdeal F.val F.property)))
  letI : IsFinite (i ≫ ambientToBase) := by
    rw [hb]
    infer_instance
  have hZi : AllCharacteristics.finiteSchemeRank (i ≫ ambientToBase) = 8 :=
    (groundNet_rank_eq_of_map_eq _ _ hb).trans hZ
  exact originalZeroDimensionalFullQuadraticBase_section_by_cohomology
    i hZi hzero F
    (hypersurface_ker_le_of_factor F.val F.property j i rfl)

end PfaffianDescent
