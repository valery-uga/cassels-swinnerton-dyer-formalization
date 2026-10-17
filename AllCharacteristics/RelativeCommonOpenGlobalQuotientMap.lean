import AllCharacteristics.RelativeCommonOpenLocus
import AllCharacteristics.RelativeCommonOpenQuotientGluing

/-!
# The actual global quotient map on common-affine-open tuples

The original finite-group chart quotients form a compatible cocone and
hence give an actual global scheme morphism. The morphism is surjective
and preserves the original family base.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] (n : ℕ)
variable [hSep : X.IsSeparated]

/-- The actual chart quotients define a cocone from the original ordered charts. -/
noncomputable def orderedCommonOpenQuotientCocone : Cocone (orderedCommonOpenDiagram f n) where
  pt := commonOpenTupleQuotientGlued f n
  ι := {
    app := fun U ↦ commonOpenTupleQuotientMap f U.val n U.property ≫
      commonOpenTupleQuotientGluedChart f n U
    naturality := fun U V h ↦ by
      change (orderedFamilyPowerOver f n).left.homOfLE (orderedFamilyCommonOpen_mono f n h.le) ≫
        (commonOpenTupleQuotientMap f V.val n V.property ≫ commonOpenTupleQuotientGluedChart f n V) =
          (commonOpenTupleQuotientMap f U.val n U.property ≫ commonOpenTupleQuotientGluedChart f n U) ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc,
        ← commonOpenTupleQuotientInclusion_square f h.le n U.property V.property,
        Category.assoc, commonOpenTupleQuotientGluedChart_naturality f n h] }

/-- The actual global quotient morphism from the original common-affine-open tuple locus. -/
noncomputable def orderedCommonOpenGlobalQuotientMap :
    orderedCommonOpenGlued f n ⟶ commonOpenTupleQuotientGlued f n :=
  colimit.desc (orderedCommonOpenDiagram f n) (orderedCommonOpenQuotientCocone f n)

include hSep in
/-- The global morphism restricts to the originally constructed invariant-spectrum quotient map. -/
theorem orderedCommonOpenGlobalQuotientMap_chart (U : X.affineOpens) :
    orderedCommonOpenGluedChart f n U ≫ orderedCommonOpenGlobalQuotientMap f n =
      commonOpenTupleQuotientMap f U.val n U.property ≫ commonOpenTupleQuotientGluedChart f n U :=
  colimit.ι_desc (orderedCommonOpenQuotientCocone f n) U

/-- The constructed global quotient morphism is surjective. -/
instance surjective_orderedCommonOpenGlobalQuotientMap :
    Surjective (orderedCommonOpenGlobalQuotientMap f n) := by
  constructor
  intro y
  obtain ⟨U, z, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (commonOpenTupleQuotientDiagram f n) y
  have hU : IsAffineOpen U.val := U.property
  have hs : Surjective (commonOpenTupleQuotientMap f U.val n hU) :=
    surjective_commonOpenTupleQuotientMap f U.val n hU
  obtain ⟨p, rfl⟩ := (commonOpenTupleQuotientMap f U.val n hU).surjective z
  refine ⟨orderedCommonOpenGluedChart f n U p, ?_⟩
  exact congrArg (fun m : (orderedFamilyCommonOpen f U.val n).toScheme ⟶
    commonOpenTupleQuotientGlued f n ↦ m p) (orderedCommonOpenGlobalQuotientMap_chart f n U)

include hSep in
/-- The actual global quotient morphism preserves the original base map of the ordered power. -/
theorem orderedCommonOpenGlobalQuotientMap_toBase :
    orderedCommonOpenGlobalQuotientMap f n ≫ commonOpenTupleQuotientGluedToBase f n =
      orderedCommonOpenGluedToPower f n ≫ (orderedFamilyPowerOver f n).hom := by
  apply colimit.hom_ext
  intro U
  change orderedCommonOpenGluedChart f n U ≫
      (orderedCommonOpenGlobalQuotientMap f n ≫ commonOpenTupleQuotientGluedToBase f n) =
    orderedCommonOpenGluedChart f n U ≫
      (orderedCommonOpenGluedToPower f n ≫ (orderedFamilyPowerOver f n).hom)
  rw [← Category.assoc, orderedCommonOpenGlobalQuotientMap_chart,
    Category.assoc, commonOpenTupleQuotientGluedChart_toBase]
  have hb := commonOpenTupleQuotientMap_toBase f U.val n U.property
  rw [hb, ← Category.assoc, orderedCommonOpenGluedChart_toPower]

end AllCharacteristics
