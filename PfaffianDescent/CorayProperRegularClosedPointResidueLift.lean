import AllCharacteristics.RegularLocalLowDimension
import AllCharacteristics.ClosedImmersionCyclePushforward
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! Generic proper lifting at an OWN regular local curve point, retaining
its entire residue field. The generic point above X is a genuine scheme
morphism. The actual normalization caller constructs it canonically.
SOURCE ONLY / UNVERIFIED. Regularity is an explicit natural hypothesis. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual regular-local specialization theorem on the pullback of a
proper morphism gives a point with values in the SAME full residue field.
No normalization locus isomorphism or residue-degree certificate is an input. -/
theorem properMorph_regularCurvePoint_exists_residuePoint
    {X Y : Scheme.{u}} [IsIntegral X]
    (f : Y ⟶ X) [IsProper f] (P : X)
    (hregular : IsRegularLocalRing (X.presheaf.stalk P))
    (hdim : ringKrullDim (X.presheaf.stalk P) ≤ 1)
    (a : Spec X.functionField ⟶ Y)
    (ha : a ≫ f = X.fromSpecStalk (genericPoint X)) :
    ∃ s : Spec (X.residueField P) ⟶ Y,
      s ≫ f = X.fromSpecResidueField P := by
  let R := X.presheaf.stalk P
  let F := X.functionField
  letI : IsRegularLocalRing R := hregular
  let W := pullback f (X.fromSpecStalk P)
  let g : W ⟶ Spec R := pullback.snd f (X.fromSpecStalk P)
  letI : IsProper g := inferInstance
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ X.fromSpecStalk P =
      X.fromSpecStalk (genericPoint X) := by
    change Spec.map (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial)) ≫ X.fromSpecStalk P = _
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  have hgeneric : HasPointOver g (algebraMap R F) := by
    refine ⟨pullback.lift a (Spec.map (CommRingCat.ofHom (algebraMap R F)))
      (ha.trans hbase.symm), ?_⟩
    exact pullback.lift_snd _ _ _
  obtain ⟨t, ht⟩ := specialize_proper_point_regularLocal_dim_le_one
    (R := R) (K := F) (f := g) hdim hgeneric
  refine ⟨t ≫ pullback.fst f (X.fromSpecStalk P), ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, ht]
  rfl

/-- At an actual CLOSED regular point, the SAME specialized residue-point
map is a closed immersion. Its image is an actual closed point with relative
residue degree ONE, actual residue map an isomorphism, and degree unchanged
to ANY further scheme base pi. Regularity and low dimension remain explicit. -/
theorem properMorph_regularClosedCurvePoint_exists_degree_preserving_closedPoint
    {X Y Z : Scheme.{u}} [IsIntegral X]
    (f : Y ⟶ X) [IsProper f] (pi : X ⟶ Z) (P : closedPoints X)
    (hregular : IsRegularLocalRing (X.presheaf.stalk P.1))
    (hdim : ringKrullDim (X.presheaf.stalk P.1) ≤ 1)
    (a : Spec X.functionField ⟶ Y)
    (ha : a ≫ f = X.fromSpecStalk (genericPoint X)) :
    ∃ Q : closedPoints Y,
      f Q.1 = P.1 ∧ IsIso (f.residueFieldMap Q.1) ∧
      f.residueDegree Q.1 = 1 ∧ (f ≫ pi).residueDegree Q.1 = pi.residueDegree P.1 := by
  classical
  obtain ⟨s, hs⟩ := properMorph_regularCurvePoint_exists_residuePoint f P.1 hregular hdim a ha
  letI : IsClosedImmersion (X.fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion (s ≫ f) := hs.symm ▸ inferInstance
  letI : IsClosedImmersion s := IsClosedImmersion.of_comp s f
  let b : Spec (X.residueField P.1) := IsLocalRing.closedPoint (X.residueField P.1)
  let Q : closedPoints Y := ⟨s b, by
    change IsClosed ({s b} : Set Y)
    rw [← Set.image_singleton]
    exact s.isClosedMap _ isClosed_singleton⟩
  have hpoint : f Q.1 = P.1 := by
    change (s ≫ f) b = P.1
    rw [hs]
    exact Scheme.fromSpecResidueField_apply (X := X) P.1 b
  have hrel : f.residueDegree Q.1 = 1 := by
    have hd := residueDegree_comp s f b
    rw [hs, residueDegree_one_of_isClosedImmersion (X.fromSpecResidueField P.1) b,
      residueDegree_one_of_isClosedImmersion s b, mul_one] at hd
    exact hd.symm
  refine ⟨Q, hpoint, isIso_residueFieldMap_of_degree_one f Q.1 hrel, hrel, ?_⟩
  rw [residueDegree_comp, hpoint, hrel, mul_one]

end PfaffianDescent.Coray
