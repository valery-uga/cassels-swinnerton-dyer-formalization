import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Grading a quotient by a homogeneous ideal

The images of the homogeneous pieces give an actual direct-sum grading of the
quotient ring. This supplies the coordinate-ring grading used for projective
hypersurfaces over arbitrary coefficient rings.
-/

open DirectSum
namespace AllCharacteristics
universe u v w
variable {R : Type u} {A : Type v} {ι : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommMonoid ι] [DecidableEq ι]
variable (𝒜 : ι → Submodule R A) [GradedRing 𝒜] (I : Ideal A)

/-- The homogeneous pieces of the quotient are the images of the original
homogeneous pieces under the quotient map. -/
def quotientGrading (i : ι) : Submodule R (A ⧸ I) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap

/-- The images of homogeneous pieces respect the unit and multiplication. -/
instance quotientGrading_gradedMonoid : SetLike.GradedMonoid (quotientGrading 𝒜 I) where
  one_mem := ⟨1, SetLike.one_mem_graded 𝒜, map_one (Ideal.Quotient.mkₐ R I)⟩
  mul_mem i j x y hx hy := by
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul (Ideal.Quotient.mkₐ R I) a b⟩

/-- The images of all homogeneous pieces span the quotient. -/
theorem quotientGrading_iSup_eq_top : ⨆ i, quotientGrading 𝒜 I i = ⊤ := by
  unfold quotientGrading
  rw [← Submodule.map_iSup, (DirectSum.Decomposition.isInternal 𝒜).submodule_iSup_eq_top,
    Submodule.map_top, LinearMap.range_eq_top]
  exact Ideal.Quotient.mkₐ_surjective R I

/-- A homogeneous ideal introduces no relations between different degrees. -/
theorem quotientGrading_iSupIndep (hI : I.IsHomogeneous 𝒜) :
    iSupIndep (quotientGrading 𝒜 I) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hv0 j hj
  have hlift : ∀ i, ∃ a ∈ 𝒜 i,
      i ∈ s → (Ideal.Quotient.mkₐ R I) a = v i := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨a, ha, he⟩ := hv i hi
      exact ⟨a, ha, fun _ ↦ he⟩
    · exact ⟨0, (𝒜 i).zero_mem, fun h ↦ (hi h).elim⟩
  choose a ha he using hlift
  have hsum : ∑ i ∈ s, a i ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ R I) (∑ i ∈ s, a i) = 0
    rw [map_sum]
    exact (Finset.sum_congr rfl (fun i hi ↦ he i hi)).trans hv0
  have hcomp : (DirectSum.decompose 𝒜 (∑ i ∈ s, a i) j : A) = a j := by
    change GradedRing.proj 𝒜 j (∑ i ∈ s, a i) = a j
    rw [map_sum]
    calc
      ∑ i ∈ s, GradedRing.proj 𝒜 j (a i) = GradedRing.proj 𝒜 j (a j) :=
        Finset.sum_eq_single j (fun i _ hij ↦ DirectSum.decompose_of_mem_ne 𝒜 (ha i) hij)
          (fun h ↦ (h hj).elim)
      _ = a j := DirectSum.decompose_of_mem_same 𝒜 (ha j)
  have haj : a j ∈ I := hcomp ▸ hI j hsum
  exact (he j hj).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr haj)

/-- The quotient by a homogeneous ideal inherits a genuine graded-ring
structure. The homogeneity condition is proved when this is applied to a
homogeneous equation. -/
@[instance_reducible]
noncomputable def quotientGradedRing (hI : I.IsHomogeneous 𝒜) :
    GradedRing (quotientGrading 𝒜 I) where
  toGradedMonoid := quotientGrading_gradedMonoid 𝒜 I
  toDecomposition := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (quotientGrading_iSupIndep 𝒜 I hI) (quotientGrading_iSup_eq_top 𝒜 I)).chooseDecomposition

end AllCharacteristics
