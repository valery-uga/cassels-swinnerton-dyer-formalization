import AllCharacteristics.RelativeCommonOpenDiagram
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Glued ordered common-open charts as an actual open of the relative power

The ordered-chart colimit embeds as the union of the original common-affine
opens. This identifies the source to be used for the global quotient map
without assuming that the common affine opens cover the whole power.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)

/-- The original ordered-chart embeddings form a cocone to the relative power. -/
noncomputable def orderedCommonOpenPowerCocone : Cocone (orderedCommonOpenDiagram f n) where
  pt := (orderedFamilyPowerOver f n).left
  ι := {
    app := fun U ↦ (orderedFamilyCommonOpen f U.val n).ι
    naturality := fun U V h ↦ by
      change (orderedFamilyPowerOver f n).left.homOfLE (orderedFamilyCommonOpen_mono f n h.le) ≫
        (orderedFamilyCommonOpen f V.val n).ι = (orderedFamilyCommonOpen f U.val n).ι ≫ 𝟙 _
      rw [Category.comp_id, Scheme.homOfLE_ι] }

variable [hSep : X.IsSeparated]

/-- The actual scheme colimit of the original ordered common-affine-open charts. -/
noncomputable def orderedCommonOpenGlued : Scheme.{u} := colimit (orderedCommonOpenDiagram f n)

/-- The original common-open chart map into the ordered-chart colimit. -/
noncomputable def orderedCommonOpenGluedChart (U : X.affineOpens) :
    (orderedFamilyCommonOpen f U.val n).toScheme ⟶ orderedCommonOpenGlued f n :=
  colimit.ι (orderedCommonOpenDiagram f n) U

/-- The map from the ordered-chart colimit to the original ordered relative power. -/
noncomputable def orderedCommonOpenGluedToPower :
    orderedCommonOpenGlued f n ⟶ (orderedFamilyPowerOver f n).left :=
  colimit.desc (orderedCommonOpenDiagram f n) (orderedCommonOpenPowerCocone f n)

include hSep in
/-- Each chart maps to the original power by its actual original open inclusion. -/
theorem orderedCommonOpenGluedChart_toPower (U : X.affineOpens) :
    orderedCommonOpenGluedChart f n U ≫ orderedCommonOpenGluedToPower f n =
      (orderedFamilyCommonOpen f U.val n).ι :=
  colimit.ι_desc (orderedCommonOpenPowerCocone f n) U

/-- Gluing introduces no identifications beyond equality in the original ordered power. -/
theorem orderedCommonOpenGluedToPower_injective :
    Function.Injective (orderedCommonOpenGluedToPower f n) := by
  intro x y hxy
  obtain ⟨U, p, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (orderedCommonOpenDiagram f n) x
  obtain ⟨V, q, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (orderedCommonOpenDiagram f n) y
  have he (W : X.affineOpens) (z : (orderedFamilyCommonOpen f W.val n).toScheme) :
      orderedCommonOpenGluedToPower f n (colimit.ι (orderedCommonOpenDiagram f n) W z) = z.val :=
    congrArg (fun m : (orderedFamilyCommonOpen f W.val n).toScheme ⟶
      (orderedFamilyPowerOver f n).left ↦ m z) (orderedCommonOpenGluedChart_toPower f n W)
  have hval := (he U p).symm.trans (hxy.trans (he V q))
  obtain ⟨z, hzp, hzq⟩ := exists_orderedCommonOpen_intersection_point f n U.val V.val p q hval
  let I : X.affineOpens := ⟨U.val ⊓ V.val, U.property.inf V.property⟩
  have hIU : I ≤ U := show U.val ⊓ V.val ≤ U.val from inf_le_left
  have hIV : I ≤ V := show U.val ⊓ V.val ≤ V.val from inf_le_right
  exact (Scheme.IsLocallyDirected.ι_eq_ι_iff (orderedCommonOpenDiagram f n)).mpr
    ⟨I, homOfLE hIU, homOfLE hIV, z, hzp, hzq⟩

/-- The glued ordered-chart source is an actual open subscheme of the original relative power. -/
instance isOpenImmersion_orderedCommonOpenGluedToPower :
    IsOpenImmersion (orderedCommonOpenGluedToPower f n) := by
  apply IsOpenImmersion.of_openCover_source (orderedCommonOpenGluedToPower f n)
    (Scheme.IsLocallyDirected.openCover (orderedCommonOpenDiagram f n))
    (orderedCommonOpenGluedToPower_injective f n)
  intro U
  change X.affineOpens at U
  change IsOpenImmersion (orderedCommonOpenGluedChart f n U ≫ orderedCommonOpenGluedToPower f n)
  rw [orderedCommonOpenGluedChart_toPower]
  infer_instance

/-- The precise image of the ordered-chart colimit is the union of the actual common-affine opens. -/
theorem orderedCommonOpenGluedToPower_range :
    Set.range (orderedCommonOpenGluedToPower f n) =
      ⋃ U : X.affineOpens, (orderedFamilyCommonOpen f U.val n : Set (orderedFamilyPowerOver f n).left) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨U, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (orderedCommonOpenDiagram f n) x
    have he : orderedCommonOpenGluedToPower f n (colimit.ι (orderedCommonOpenDiagram f n) U y) = y.val :=
      congrArg (fun m : (orderedFamilyCommonOpen f U.val n).toScheme ⟶
        (orderedFamilyPowerOver f n).left ↦ m y) (orderedCommonOpenGluedChart_toPower f n U)
    exact Set.mem_iUnion.mpr ⟨U, he.symm ▸ y.property⟩
  · intro hp
    obtain ⟨U, hU⟩ := Set.mem_iUnion.mp hp
    refine ⟨colimit.ι (orderedCommonOpenDiagram f n) U ⟨p, hU⟩, ?_⟩
    exact congrArg (fun m : (orderedFamilyCommonOpen f U.val n).toScheme ⟶
      (orderedFamilyPowerOver f n).left ↦ m ⟨p, hU⟩) (orderedCommonOpenGluedChart_toPower f n U)

end AllCharacteristics
