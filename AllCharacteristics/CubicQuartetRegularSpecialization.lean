import AllCharacteristics.CubicQuarticSubschemeSection
import AllCharacteristics.FlatStalkCharacteristic
import AllCharacteristics.RegularLocalSpecialization
import AllCharacteristics.UniversalQuartetSubscheme

/-! # Specializing the universal quartic subscheme

The finite flat rank-four subscheme gives a point on every field-valued fiber
whose parameter stalk is regular and of characteristic zero.  This is the
scheme-theoretic specialization step used by the universal quartet argument.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
open HomogeneousProjective
namespace UniversalHomogeneous
universe u

/-- A rank-four finite subscheme in a cubic family lifts from a regular
characteristic-zero stalk to the residue-field fiber. -/
theorem cubicFamily_specialize_quarticSubscheme_at_regular_point
    {R : Type u} [CommRing R] (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    {B : Scheme.{u}} (b : B ⟶ Spec (.of R))
    (D : FiniteSubschemeDatum (pullback.snd (hypersurfaceToBase p hp) b) 4)
  (x : B) [IsRegularLocalRing (B.presheaf.stalk x)]
    [CharZero (B.presheaf.stalk x)] :
    ∃ q : Spec (B.residueField x) ⟶ pullback (hypersurfaceToBase p hp) b,
      q ≫ pullback.snd (hypersurfaceToBase p hp) b = B.fromSpecResidueField x := by
  letI : IsDomain (B.presheaf.stalk x) := isDomain_of_regularLocalRing _
  let K := FractionRing (B.presheaf.stalk x)
  letI : Field K := inferInstance
  letI : CharZero K := IsFractionRing.charZero_of_isFractionRing
    (B.presheaf.stalk x)
  let c : Spec (.of K) ⟶ Spec (B.presheaf.stalk x) :=
    Spec.map (CommRingCat.ofHom (algebraMap (B.presheaf.stalk x) K))
  let f := pullback.snd (hypersurfaceToBase p hp) b
  obtain ⟨q, hq⟩ := cubicFamily_fieldLift_of_quarticSubscheme
    (k := K) p hp b D (c ≫ B.fromSpecStalk x)
  let fb := pullback.snd f (B.fromSpecStalk x)
  have hg : HasPointOver fb (algebraMap (B.presheaf.stalk x) K) := by
    refine ⟨pullback.lift q c hq, ?_⟩
    exact pullback.lift_snd _ _ _
  obtain ⟨t, ht⟩ := @specialize_proper_point_regularLocal
    (B.presheaf.stalk x) K _ inferInstance _ _ _ _ fb _ hg
  refine ⟨t ≫ pullback.fst f (B.fromSpecStalk x), ?_⟩
  change (t ≫ pullback.fst f (B.fromSpecStalk x)) ≫ f = _
  rw [Category.assoc, pullback.condition, ← Category.assoc, ht]
  rfl

/-- The same specialization result after identifying the residue field of a
field-valued parameter with its chosen ground field. -/
theorem cubicFamily_fieldLift_quarticSubscheme_at_regular_point
    {R k : Type u} [CommRing R] [Field k]
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    {B : Scheme.{u}} (b : B ⟶ Spec (.of R))
    (D : FiniteSubschemeDatum (pullback.snd (hypersurfaceToBase p hp) b) 4)
    (a : Spec (.of k) ⟶ B)
    [IsRegularLocalRing (B.presheaf.stalk (a (IsLocalRing.closedPoint k)))]
    [CharZero (B.presheaf.stalk (a (IsLocalRing.closedPoint k)))] :
    ∃ q : Spec (.of k) ⟶ pullback (hypersurfaceToBase p hp) b,
      q ≫ pullback.snd (hypersurfaceToBase p hp) b = a := by
  obtain ⟨q, hq⟩ := cubicFamily_specialize_quarticSubscheme_at_regular_point p hp b D
    (a (IsLocalRing.closedPoint k))
  let e := B.descResidueField (Scheme.stalkClosedPointTo a)
  refine ⟨Spec.map e ≫ q, ?_⟩
  rw [Category.assoc, hq]
  exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k B a

/-- The universal smooth distinct-quartet family has a residue-field point
above every field-valued parameter over a regular characteristic-zero domain. -/
theorem cubicSmoothDistinctQuartet_fieldLift
    (R : Type u) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R]
    (hR : IsRegularRing R) {k : Type u} [Field k]
    (a : Spec (.of k) ⟶ smoothDistinctCubicQuartetBase R) :
    ∃ q : Spec (.of k) ⟶ cubicOverSmoothDistinctQuartets R,
      q ≫ cubicOverSmoothDistinctQuartetsToBase R = a := by
  have hreg : IsRegularLocalRing ((smoothDistinctCubicQuartetBase R).presheaf.stalk
      (a (IsLocalRing.closedPoint k))) :=
    isRegularLocalRing_smoothDistinctCubicQuartet_stalk R hR
      (a (IsLocalRing.closedPoint k))
  letI := hreg
  letI : CharZero ((smoothDistinctCubicQuartetBase R).presheaf.stalk
      (a (IsLocalRing.closedPoint k))) :=
    charZero_stalk_of_flat_over_domain R (smoothDistinctCubicQuartetToBaseRing R)
      (a (IsLocalRing.closedPoint k))
  exact cubicFamily_fieldLift_quarticSubscheme_at_regular_point
    (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)
    (smoothDistinctCubicQuartetToCoefficients R)
    (smoothDistinctCubicQuartetFiniteSubscheme R) a

end UniversalHomogeneous
end AllCharacteristics
