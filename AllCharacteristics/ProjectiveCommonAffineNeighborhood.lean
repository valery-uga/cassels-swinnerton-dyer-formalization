import AllCharacteristics.HomogeneousFinitePrimeAvoidance
import AllCharacteristics.RelativeCommonOpenLocus
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Common affine neighborhoods and full ordered-power coverage for Proj

Every finite set of points of an actual projective spectrum lies in one
homogeneous affine basic open. Consequently the common-affine-open charts
cover every ordered relative power of that scheme, over any base scheme.
The previously constructed open locus is therefore the whole ordered power.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Any finite set of actual Proj points lies in one actual affine open subscheme. -/
theorem exists_affineOpen_containing_projective_finset (s : Finset (Proj 𝒜)) :
    ∃ U : (Proj 𝒜).affineOpens, ∀ p ∈ s, p ∈ U.val := by
  obtain ⟨d, hd, a, ha, hn⟩ := exists_positive_homogeneous_avoiding_projective_points 𝒜 s
  exact ⟨⟨Proj.basicOpen 𝒜 a, Proj.isAffineOpen_basicOpen 𝒜 a ha hd⟩, hn⟩

/-- Every point of an ordered relative power of Proj has all its coordinates
in one affine open of the original Proj scheme. -/
theorem exists_commonAffineOpen_orderedProjectivePoint {S : Scheme.{u}}
    (f : Proj 𝒜 ⟶ S) (n : ℕ) (x : (orderedFamilyPowerOver f n).left) :
    ∃ U : (Proj 𝒜).affineOpens, x ∈ orderedFamilyCommonOpen f U.val n := by
  classical
  let p (i : Fin n) := Over.Hom.left (orderedFamilyCoordinate f n i) x
  obtain ⟨U, hU⟩ := exists_affineOpen_containing_projective_finset 𝒜 (Finset.univ.image p)
  refine ⟨U, (mem_orderedFamilyCommonOpen_iff f U.val n x).mpr ?_⟩
  intro i
  exact hU (p i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The actual common-affine-open locus covers the entire ordered relative power of Proj. -/
instance surjective_orderedCommonOpenGluedToPower_projective {S : Scheme.{u}}
    (f : Proj 𝒜 ⟶ S) (n : ℕ) : Surjective (orderedCommonOpenGluedToPower f n) := by
  constructor
  intro x
  obtain ⟨U, hU⟩ := exists_commonAffineOpen_orderedProjectivePoint 𝒜 f n x
  exact (Set.ext_iff.mp (orderedCommonOpenGluedToPower_range f n) x).mpr
    (Set.mem_iUnion.mpr ⟨U, hU⟩)

/-- For actual Proj schemes the constructed ordered common-open locus is
isomorphic to the whole original ordered relative power. -/
instance isIso_orderedCommonOpenGluedToPower_projective {S : Scheme.{u}}
    (f : Proj 𝒜 ⟶ S) (n : ℕ) : IsIso (orderedCommonOpenGluedToPower f n) :=
  (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

end AllCharacteristics
