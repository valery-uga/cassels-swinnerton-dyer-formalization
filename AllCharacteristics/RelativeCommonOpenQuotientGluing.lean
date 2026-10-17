import AllCharacteristics.RelativeCommonOpenQuotientIntersections
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing the actual affine unordered-tuple quotient charts

The proved open-immersion transition maps and exact intersection lifts make
the diagram locally directed. Its actual scheme colimit has the original
invariant spectra as an open cover and carries their common base morphism.
Coverage of the entire ordered power by common affine opens is a separate
geometric statement and is not assumed in this construction.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] (n : ℕ)

/-- The actual diagram of affine unordered-tuple quotient schemes. -/
noncomputable def commonOpenTupleQuotientDiagram : X.affineOpens ⥤ Scheme.{u} :=
  commonOpenTupleQuotientFunctor f n ⋙ Over.forget S

/-- Every transition in the actual quotient diagram is an open immersion. -/
instance isOpenImmersion_commonOpenTupleQuotientDiagram_map
    {U V : X.affineOpens} (h : U ⟶ V) :
    IsOpenImmersion ((commonOpenTupleQuotientDiagram f n).map h) :=
  isOpenImmersion_commonOpenTupleQuotientFunctor_map f n h

variable [hSep : X.IsSeparated]

/-- The actual quotient diagram is locally directed because its points lift
through the actual affine intersection charts. -/
instance isLocallyDirected_commonOpenTupleQuotientDiagram :
    (commonOpenTupleQuotientDiagram f n ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro U V W hUW hVW x y hxy
  let I : X.affineOpens := ⟨U.val ⊓ V.val, U.property.inf V.property⟩
  obtain ⟨z, hzx, hzy⟩ := exists_commonOpenTupleQuotient_intersection f n hUW.le hVW.le
    U.property V.property W.property I.property x y hxy
  have hIU : I ≤ U := show U.val ⊓ V.val ≤ U.val from inf_le_left
  have hIV : I ≤ V := show U.val ⊓ V.val ≤ V.val from inf_le_right
  exact ⟨I, homOfLE hIU, homOfLE hIV, z, hzx, hzy⟩

/-- The actual scheme obtained by gluing the affine unordered-tuple quotients. -/
noncomputable def commonOpenTupleQuotientGlued : Scheme.{u} :=
  colimit (commonOpenTupleQuotientDiagram f n)

/-- The actual map from an invariant-spectrum chart to the glued quotient scheme. -/
noncomputable def commonOpenTupleQuotientGluedChart (U : X.affineOpens) :
    commonOpenTupleQuotient f U.val n ⟶ commonOpenTupleQuotientGlued f n :=
  colimit.ι (commonOpenTupleQuotientDiagram f n) U

/-- The constructed invariant-spectrum charts are open immersions in the glued scheme. -/
instance isOpenImmersion_commonOpenTupleQuotientGluedChart (U : X.affineOpens) :
    IsOpenImmersion (commonOpenTupleQuotientGluedChart f n U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (commonOpenTupleQuotientDiagram f n) U))

/-- The actual invariant-spectrum charts form an open cover of the glued scheme. -/
noncomputable def commonOpenTupleQuotientGluedCover :
    (commonOpenTupleQuotientGlued f n).OpenCover :=
  Scheme.IsLocallyDirected.openCover (commonOpenTupleQuotientDiagram f n)

/-- The original base maps of all quotient charts form a cocone. -/
noncomputable def commonOpenTupleQuotientBaseCocone : Cocone (commonOpenTupleQuotientDiagram f n) where
  pt := S
  ι := {
    app := fun U ↦ commonOpenTupleQuotientToBase f U.val n
    naturality := fun U V h ↦ by
      change commonOpenTupleQuotientInclusion f h.le n ≫ commonOpenTupleQuotientToBase f V.val n =
        commonOpenTupleQuotientToBase f U.val n ≫ 𝟙 S
      rw [Category.comp_id]
      exact commonOpenTupleQuotientInclusion_toBase f h.le n U.property V.property }

/-- The glued quotient carries the original base morphism. -/
noncomputable def commonOpenTupleQuotientGluedToBase : commonOpenTupleQuotientGlued f n ⟶ S :=
  colimit.desc (commonOpenTupleQuotientDiagram f n) (commonOpenTupleQuotientBaseCocone f n)

include hSep in
/-- Every quotient chart retains its actual original base morphism after gluing. -/
theorem commonOpenTupleQuotientGluedChart_toBase (U : X.affineOpens) :
    commonOpenTupleQuotientGluedChart f n U ≫ commonOpenTupleQuotientGluedToBase f n =
      commonOpenTupleQuotientToBase f U.val n :=
  colimit.ι_desc (commonOpenTupleQuotientBaseCocone f n) U

include hSep in
/-- The quotient chart inclusions agree with their actual transition maps after gluing. -/
theorem commonOpenTupleQuotientGluedChart_naturality {U V : X.affineOpens} (h : U ⟶ V) :
    commonOpenTupleQuotientInclusion f h.le n ≫ commonOpenTupleQuotientGluedChart f n V =
      commonOpenTupleQuotientGluedChart f n U :=
  colimit.w (commonOpenTupleQuotientDiagram f n) h

end AllCharacteristics
