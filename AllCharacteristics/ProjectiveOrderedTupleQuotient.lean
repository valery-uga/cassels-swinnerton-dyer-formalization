import AllCharacteristics.ProjectiveCommonAffineNeighborhood
import AllCharacteristics.RelativeGlobalQuotientProperties

/-!
# The actual finite unordered-tuple quotient of a projective spectrum

The proved common-affine coverage identifies the ordered-chart source with
the whole original relative power. Transporting the constructed global
quotient gives an actual finite surjective morphism from that whole power,
with the original base map and original chart quotients preserved.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- The actual quotient scheme for unordered tuples in a projective spectrum over an affine base. -/
noncomputable def projectiveOrderedTupleQuotient : Scheme.{u} := commonOpenTupleQuotientGlued f n

/-- The actual quotient morphism from the whole original ordered relative power. -/
noncomputable def projectiveOrderedTupleQuotientMap :
    (orderedFamilyPowerOver f n).left ⟶ projectiveOrderedTupleQuotient 𝒜 f n :=
  inv (orderedCommonOpenGluedToPower f n) ≫ orderedCommonOpenGlobalQuotientMap f n

/-- The unordered projective tuples carry the original affine base morphism. -/
noncomputable def projectiveOrderedTupleQuotientToBase : projectiveOrderedTupleQuotient 𝒜 f n ⟶ S :=
  commonOpenTupleQuotientGluedToBase f n

/-- Transport from the proved ordered-chart model recovers the previously constructed global quotient. -/
theorem projectiveOrderedTupleQuotientMap_fromGlued :
    orderedCommonOpenGluedToPower f n ≫ projectiveOrderedTupleQuotientMap 𝒜 f n =
      orderedCommonOpenGlobalQuotientMap f n := by
  change orderedCommonOpenGluedToPower f n ≫
    (inv (orderedCommonOpenGluedToPower f n) ≫ orderedCommonOpenGlobalQuotientMap f n) = _
  rw [IsIso.hom_inv_id_assoc]

/-- The full projective quotient map retains the actual original chart quotients. -/
theorem projectiveOrderedTupleQuotientMap_chart (U : (Proj 𝒜).affineOpens) :
    (orderedFamilyCommonOpen f U.val n).ι ≫ projectiveOrderedTupleQuotientMap 𝒜 f n =
      commonOpenTupleQuotientMap f U.val n U.property ≫ commonOpenTupleQuotientGluedChart f n U := by
  rw [← orderedCommonOpenGluedChart_toPower f n U, Category.assoc,
    projectiveOrderedTupleQuotientMap_fromGlued]
  exact orderedCommonOpenGlobalQuotientMap_chart f n U

/-- The full quotient map factors the actual original family base map. -/
theorem projectiveOrderedTupleQuotientMap_toBase :
    projectiveOrderedTupleQuotientMap 𝒜 f n ≫ projectiveOrderedTupleQuotientToBase 𝒜 f n =
      (orderedFamilyPowerOver f n).hom := by
  change (inv (orderedCommonOpenGluedToPower f n) ≫ orderedCommonOpenGlobalQuotientMap f n) ≫
    commonOpenTupleQuotientGluedToBase f n = _
  rw [Category.assoc, orderedCommonOpenGlobalQuotientMap_toBase, IsIso.inv_hom_id_assoc]

/-- The quotient of the entire ordered relative power is integral. -/
instance isIntegralHom_projectiveOrderedTupleQuotientMap :
    IsIntegralHom (projectiveOrderedTupleQuotientMap 𝒜 f n) := by
  change IsIntegralHom (inv (orderedCommonOpenGluedToPower f n) ≫ orderedCommonOpenGlobalQuotientMap f n)
  infer_instance

/-- The quotient of the entire ordered relative power is surjective. -/
instance surjective_projectiveOrderedTupleQuotientMap :
    Surjective (projectiveOrderedTupleQuotientMap 𝒜 f n) := by
  change Surjective (inv (orderedCommonOpenGluedToPower f n) ≫ orderedCommonOpenGlobalQuotientMap f n)
  infer_instance

/-- For a locally finite-type projective family the full unordered-tuple quotient morphism is finite. -/
instance isFinite_projectiveOrderedTupleQuotientMap [LocallyOfFiniteType f] :
    IsFinite (projectiveOrderedTupleQuotientMap 𝒜 f n) := by
  change IsFinite (inv (orderedCommonOpenGluedToPower f n) ≫ orderedCommonOpenGlobalQuotientMap f n)
  infer_instance

/-- For a locally finite-type projective family the full unordered-tuple quotient morphism is proper. -/
instance isProper_projectiveOrderedTupleQuotientMap [LocallyOfFiniteType f] :
    IsProper (projectiveOrderedTupleQuotientMap 𝒜 f n) := by
  infer_instance

/-- If the original projective family is proper, its full unordered-tuple
quotient is universally closed over the same base.  This is the existence
part needed to specialize a generic effective cycle; separatedness of the
quotient is not required. -/
instance universallyClosed_projectiveOrderedTupleQuotientToBase [IsProper f] :
    UniversallyClosed (projectiveOrderedTupleQuotientToBase 𝒜 f n) := by
  let q := projectiveOrderedTupleQuotientMap 𝒜 f n
  let g := projectiveOrderedTupleQuotientToBase 𝒜 f n
  letI : UniversallyClosed (q ≫ g) := by
    dsimp only [q, g]
    rw [projectiveOrderedTupleQuotientMap_toBase]
    infer_instance
  letI : Surjective q := by
    dsimp only [q]
    infer_instance
  exact UniversallyClosed.of_comp_surjective q g

end AllCharacteristics
