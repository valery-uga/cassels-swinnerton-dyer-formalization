import AllCharacteristics.FiniteFlatCycle

/-!
# Ranks of finite schemes after field extension

The finite rank of a scheme over a field is preserved by a specified
field-extension base change.  This is phrased through the actual pullback
scheme, so it applies to projective schemes once their base-change
identification is available.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics

universe u

/-- An isomorphic field-extension base change has the same finite scheme
rank as the original finite scheme. -/
theorem finiteSchemeRank_eq_of_field_baseChange
    {k K : Type u} [Field k] [Field K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (b : Spec (.of K) ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of K))
    [IsFinite f] [IsFinite g]
    (e : Y ≅ pullback f b)
    (hbase : e.hom ≫ pullback.snd f b = g) :
    finiteSchemeRank f = finiteSchemeRank g := by
  rw [finiteSchemeRank_eq_finrank, finiteSchemeRank_eq_finrank]
  have hb : b (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint k :=
    Subsingleton.elim _ _
  calc
    f.finrank (IsLocalRing.closedPoint k) =
        f.finrank (b (IsLocalRing.closedPoint K)) := by rw [hb]
    _ = (pullback.snd f b).finrank (IsLocalRing.closedPoint K) :=
      (Scheme.Hom.finrank_pullback_snd f b (IsLocalRing.closedPoint K)).symm
    _ = ((e.hom ≫ pullback.snd f b)).finrank (IsLocalRing.closedPoint K) := by
      rw [Scheme.Hom.finrank_comp_left_of_isIso e.hom (pullback.snd f b)]
    _ = g.finrank (IsLocalRing.closedPoint K) := by rw [hbase]

end AllCharacteristics
