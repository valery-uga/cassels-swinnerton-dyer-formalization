import PfaffianDescent.NativeFiniteFamilyOpenLocus314
import AllCharacteristics.ProjectiveCommonAffineNeighborhood
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Cover.Open

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u v
variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
set_option autoImplicit false

/-- All positive homogeneous principal charts, with no selected coordinate cover. -/
def projectivePositiveHomogeneousChartIndex001 : Type u :=
  {a : A // ∃ d : ℕ, 0 < d ∧ a ∈ 𝒜 d}

/-- Every indexed actual principal open is affine. -/
theorem projectivePositiveHomogeneousChart_isAffine001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    IsAffineOpen (Proj.basicOpen 𝒜 a.val) := by
  obtain ⟨d, hd, ha⟩ := a.property
  exact Proj.isAffineOpen_basicOpen 𝒜 a.val ha hd

/-- Maximal good base open for the SAME whole family in the actual chart preimage. -/
def finiteFamilyProjectiveHomogeneousChartLocus001
    {X B : Scheme.{u}} (q : X ⟶ Proj 𝒜) (F : X ⟶ B)
    (n : ℕ) (P : FiniteFlatHilbertPoint195 F n)
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) : B.Opens :=
  finiteFamilyWholeOpenLocus314 F n P (q ⁻¹ᵁ Proj.basicOpen 𝒜 a.val)

/-- The actual finite fiber constructs one homogeneous affine chart containing its
entire image. The original whole-family good locus contains the original base point;
no reducedness, separability, infinite-field or supplied cover hypothesis is used. -/
theorem finiteFamilyProjective_exists_homogeneousWholeChartLocus001
    {X B : Scheme.{u}} (q : X ⟶ Proj 𝒜) (F : X ⟶ B)
    (n : ℕ) (P : FiniteFlatHilbertPoint195 F n) (b : B) :
    ∃ a : projectivePositiveHomogeneousChartIndex001 𝒜,
      b ∈ finiteFamilyProjectiveHomogeneousChartLocus001 𝒜 q F n P a := by
  classical
  let f := P.val.subschemeι ≫ F
  let qZ := P.val.subschemeι ≫ q
  letI : IsFinite f := P.property.1
  let s : Set (Proj 𝒜) := qZ '' (f ⁻¹' {b})
  have hs : s.Finite := (f.finite_preimage_singleton b).image qZ
  obtain ⟨d, hd, a, ha, hAvoid⟩ :=
    AllCharacteristics.exists_positive_homogeneous_avoiding_projective_points 𝒜 hs.toFinset
  refine ⟨⟨a, d, hd, ha⟩, ?_⟩
  change b ∈ finiteFamilyWholeOpenLocus314 F n P (q ⁻¹ᵁ Proj.basicOpen 𝒜 a)
  apply (mem_finiteFamilyWholeOpenLocus_iff314 F n P
    (q ⁻¹ᵁ Proj.basicOpen 𝒜 a) b).mpr
  intro z hz
  change a ∉ (qZ z).asHomogeneousIdeal
  apply hAvoid
  apply hs.mem_toFinset.mpr
  refine ⟨z, ?_, rfl⟩
  change f z = b
  exact hz

/-- The maximal WHOLE-family loci for all homogeneous affine charts cover the base. -/
theorem finiteFamilyProjectiveHomogeneousChartLocus_iSup_eq_top001
    {X B : Scheme.{u}} (q : X ⟶ Proj 𝒜) (F : X ⟶ B)
    (n : ℕ) (P : FiniteFlatHilbertPoint195 F n) :
    (⨆ a : projectivePositiveHomogeneousChartIndex001 𝒜,
      finiteFamilyProjectiveHomogeneousChartLocus001 𝒜 q F n P a) = ⊤ := by
  apply top_unique
  intro b _
  exact TopologicalSpace.Opens.mem_iSup.mpr
    (finiteFamilyProjective_exists_homogeneousWholeChartLocus001 𝒜 q F n P b)

/-- A genuine scheme open cover constructed from the original finite-flat family.
Each cover map is the actual inclusion of its maximal good base open. The existing
314 source restriction, finite-flat degree-n projection and actual chart lift apply
to the SAME P on each member, retaining nilpotents and its original base maps. -/
def finiteFamilyProjectiveHomogeneousWholeChartOpenCover001
    {X B : Scheme.{u}} (q : X ⟶ Proj 𝒜) (F : X ⟶ B)
    (n : ℕ) (P : FiniteFlatHilbertPoint195 F n) : B.OpenCover where
  I₀ := projectivePositiveHomogeneousChartIndex001 𝒜
  X a := (finiteFamilyProjectiveHomogeneousChartLocus001 𝒜 q F n P a).toScheme
  f a := (finiteFamilyProjectiveHomogeneousChartLocus001 𝒜 q F n P a).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro b
    obtain ⟨a, ha⟩ := finiteFamilyProjective_exists_homogeneousWholeChartLocus001 𝒜 q F n P b
    refine ⟨a, ?_⟩
    rw [(finiteFamilyProjectiveHomogeneousChartLocus001 𝒜 q F n P a).range_ι]
    exact ha

end PfaffianDescent
