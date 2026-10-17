import AllCharacteristics.RelativeCommonOpenQuotientInclusions

/-!
# Coherent functor of actual unordered-tuple quotient charts

The quotient-chart inclusion maps satisfy identity and composition. They
therefore define an actual functor from the poset of affine opens of the
original family to schemes over the original affine base.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] (n : ℕ)

/-- Original affine tuple-chart quotient maps cancel against maps to affine schemes. -/
theorem commonOpenTupleQuotientMap_cancel (U : X.Opens) (hU : IsAffineOpen U)
    {T : Scheme.{u}} [IsAffine T] {a b : commonOpenTupleQuotient f U n ⟶ T}
    (h : commonOpenTupleQuotientMap f U n hU ≫ a = commonOpenTupleQuotientMap f U n hU ≫ b) :
    a = b := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  exact affineSchemeActionQuotientMap_cancel (Equiv.Perm (Fin n))
    (commonOpenRightAction f U n) (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n) h

/-- Identity inclusion induces the identity on an actual affine quotient chart. -/
theorem commonOpenTupleQuotientInclusion_id (U : X.Opens) (hU : IsAffineOpen U) :
    commonOpenTupleQuotientInclusion f (le_refl U) n = 𝟙 (commonOpenTupleQuotient f U n) := by
  apply commonOpenTupleQuotientMap_cancel f n U hU
  rw [commonOpenTupleQuotientInclusion_square f (le_refl U) n hU hU,
    Category.comp_id, Scheme.homOfLE_rfl, Category.id_comp]

/-- Actual quotient-chart inclusion maps compose as the original open inclusions. -/
theorem commonOpenTupleQuotientInclusion_comp {U V W : X.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    commonOpenTupleQuotientInclusion f hUV n ≫ commonOpenTupleQuotientInclusion f hVW n =
      commonOpenTupleQuotientInclusion f (hUV.trans hVW) n := by
  apply commonOpenTupleQuotientMap_cancel f n U hU
  rw [← Category.assoc, commonOpenTupleQuotientInclusion_square f hUV n hU hV,
    Category.assoc, commonOpenTupleQuotientInclusion_square f hVW n hV hW,
    commonOpenTupleQuotientInclusion_square f (hUV.trans hVW) n hU hW,
    ← Category.assoc, Scheme.homOfLE_homOfLE]

/-- The constructed unordered-tuple quotient charts form an actual functor over the original base. -/
noncomputable def commonOpenTupleQuotientFunctor : X.affineOpens ⥤ Over S where
  obj U := Over.mk (commonOpenTupleQuotientToBase f U.val n)
  map {U V} h := Over.homMk (commonOpenTupleQuotientInclusion f h.le n)
    (commonOpenTupleQuotientInclusion_toBase f h.le n U.property V.property)
  map_id U := by
    apply Over.OverMorphism.ext
    exact commonOpenTupleQuotientInclusion_id f n U.val U.property
  map_comp {U V W} hUV hVW := by
    apply Over.OverMorphism.ext
    exact (commonOpenTupleQuotientInclusion_comp f n hUV.le hVW.le U.property V.property W.property).symm

end AllCharacteristics
