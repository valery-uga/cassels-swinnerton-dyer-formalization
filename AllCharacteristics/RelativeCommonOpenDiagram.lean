import AllCharacteristics.RelativeCommonOpenIntersections
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The actual diagram of ordered common-affine-open charts

The diagram uses the original open subschemes of the ordered relative
power. Their exact intersections make it locally directed for a separated
original scheme.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)

/-- Common-open charts, indexed by the actual affine opens of the original scheme. -/
noncomputable def orderedCommonOpenFunctor :
    X.affineOpens ⥤ (orderedFamilyPowerOver f n).left.Opens where
  obj U := orderedFamilyCommonOpen f U.val n
  map h := homOfLE (orderedFamilyCommonOpen_mono f n h.le)

/-- The actual diagram of original ordered common-open chart schemes. -/
noncomputable def orderedCommonOpenDiagram : X.affineOpens ⥤ Scheme.{u} :=
  orderedCommonOpenFunctor f n ⋙ (orderedFamilyPowerOver f n).left.restrictFunctor ⋙
    Over.forget (orderedFamilyPowerOver f n).left

/-- Every transition is the original open-subscheme inclusion. -/
instance isOpenImmersion_orderedCommonOpenDiagram_map
    {U V : X.affineOpens} (h : U ⟶ V) :
    IsOpenImmersion ((orderedCommonOpenDiagram f n).map h) :=
  inferInstanceAs (IsOpenImmersion ((orderedFamilyPowerOver f n).left.homOfLE
    (orderedFamilyCommonOpen_mono f n h.le)))

/-- Two points of common-open charts with the same original point come from
the actual common-open chart of their intersection. -/
theorem exists_orderedCommonOpen_intersection_point (U V : X.Opens)
    (x : (orderedFamilyCommonOpen f U n).toScheme)
    (y : (orderedFamilyCommonOpen f V n).toScheme) (hxy : x.val = y.val) :
    ∃ z : (orderedFamilyCommonOpen f (U ⊓ V) n).toScheme,
      (orderedFamilyPowerOver f n).left.homOfLE
        (orderedFamilyCommonOpen_mono f n (show U ⊓ V ≤ U from inf_le_left)) z = x ∧
      (orderedFamilyPowerOver f n).left.homOfLE
        (orderedFamilyCommonOpen_mono f n (show U ⊓ V ≤ V from inf_le_right)) z = y := by
  have hx : x.val ∈ orderedFamilyCommonOpen f (U ⊓ V) n := by
    rw [orderedFamilyCommonOpen_inf]
    exact ⟨x.property, hxy.symm ▸ y.property⟩
  refine ⟨⟨x.val, hx⟩, ?_, ?_⟩
  · apply Subtype.ext
    exact Scheme.homOfLE_apply _ _
  · apply Subtype.ext
    exact (Scheme.homOfLE_apply _ _).trans hxy

variable [X.IsSeparated]

/-- The original ordered-chart diagram is locally directed by its actual intersections. -/
instance isLocallyDirected_orderedCommonOpenDiagram :
    (orderedCommonOpenDiagram f n ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro U V W hUW hVW x y hxy
  change (orderedFamilyPowerOver f n).left.homOfLE
    (orderedFamilyCommonOpen_mono f n hUW.le) x =
      (orderedFamilyPowerOver f n).left.homOfLE
        (orderedFamilyCommonOpen_mono f n hVW.le) y at hxy
  have he := congrArg (fun z : (orderedFamilyCommonOpen f W.val n).toScheme ↦ z.val) hxy
  have hval : x.val = y.val :=
    (Scheme.homOfLE_apply _ _).symm.trans (he.trans (Scheme.homOfLE_apply _ _))
  obtain ⟨z, hzx, hzy⟩ := exists_orderedCommonOpen_intersection_point f n U.val V.val x y hval
  let I : X.affineOpens := ⟨U.val ⊓ V.val, U.property.inf V.property⟩
  have hIU : I ≤ U := show U.val ⊓ V.val ≤ U.val from inf_le_left
  have hIV : I ≤ V := show U.val ⊓ V.val ≤ V.val from inf_le_right
  exact ⟨I, homOfLE hIU, homOfLE hIV, z, hzx, hzy⟩

end AllCharacteristics
