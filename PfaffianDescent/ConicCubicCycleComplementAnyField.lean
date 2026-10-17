import PfaffianDescent.ConicCubicLengthAnyField
import PfaffianDescent.FiniteClosedSubschemeCycleComplement
import AllCharacteristics.ClosedPointRank

/-! SOURCE ONLY / UNVERIFIED. The literal Section 2 cycle residual of the
actual conic/cubic intersection, with canonical addition equality over every
ground field. Actual stalk lengths, including nilpotents, are retained. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory AllCharacteristics
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]

/-- Removing an actual closed rank-d subscheme from the actual conic/cubic
intersection gives the canonical effective cycle of degree six minus d. -/
theorem conic_cubic_effective_complement_cycle_anyField
    (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q f)
    {Z : Scheme.{u}} (i : Z ⟶ scheme (conicCubicHomogeneousIdeal q f hq hf))
    [IsClosedImmersion i] (d : ℕ)
    (hZ : letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
      finiteSchemeRank (i ≫ toBase (conicCubicHomogeneousIdeal q f hq hf)) = d) :
    letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
    ∃ r : EffectiveZeroCycle (scheme (conicCubicHomogeneousIdeal q f hq hf)),
      finiteSchemeFundamentalCycle (toBase (conicCubicHomogeneousIdeal q f hq hf)) =
        r + pushforwardClosedCycle i
          (finiteSchemeFundamentalCycle (i ≫ toBase (conicCubicHomogeneousIdeal q f hq hf))) ∧
      EffectiveZeroCycle.degree (toBase (conicCubicHomogeneousIdeal q f hq hf)) r = 6 - d := by
  letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
  let g := toBase (conicCubicHomogeneousIdeal q f hq hf)
  refine ⟨finiteClosedSubschemeComplementCycle i g,
    finiteClosedSubschemeComplementCycle_add i g, ?_⟩
  rw [finiteClosedSubschemeComplementCycle_degree,
    conic_cubic_intersection_length_six_anyField q f hq hf hq0 hrel, hZ]

/-- For the canonical residue-field closed subscheme of an original closed
point, the removed cycle is precisely that point with multiplicity one. -/
theorem conic_cubic_closedPoint_complement_cycle_anyField
    (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q f)
    (x : closedPoints (scheme (conicCubicHomogeneousIdeal q f hq hf)))
    (d : ℕ) (hx : (toBase (conicCubicHomogeneousIdeal q f hq hf)).residueDegree x.1 = d) :
    letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
    ∃ r : EffectiveZeroCycle (scheme (conicCubicHomogeneousIdeal q f hq hf)),
      finiteSchemeFundamentalCycle (toBase (conicCubicHomogeneousIdeal q f hq hf)) =
        r + Finsupp.single x 1 ∧
      EffectiveZeroCycle.degree (toBase (conicCubicHomogeneousIdeal q f hq hf)) r = 6 - d := by
  letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
  let W := scheme (conicCubicHomogeneousIdeal q f hq hf)
  let g := toBase (conicCubicHomogeneousIdeal q f hq hf)
  let i : Spec (.of (W.residueField x.1)) ⟶ W := W.fromSpecResidueField x.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp x.2
  have hZ : finiteSchemeRank (i ≫ g) = d :=
    (closedPoint_finiteSchemeRank_eq_residueDegree g x).trans hx
  obtain ⟨r, hr, hdegree⟩ :=
    conic_cubic_effective_complement_cycle_anyField q f hq hf hq0 hrel i d hZ
  have hpoint : pushforwardClosedCycle i (finiteSchemeFundamentalCycle (i ≫ g)) =
      Finsupp.single x 1 := by
    classical
    let y : closedPoints (Spec (.of (W.residueField x.1))) :=
      ⟨IsLocalRing.closedPoint (W.residueField x.1), isClosed_singleton⟩
    have hfund : finiteSchemeFundamentalCycle (i ≫ g) = Finsupp.single y 1 := by
      change fundamentalZeroCycle (Spec (.of (W.residueField x.1))) = _
      exact fundamentalZeroCycle_Spec_field (W.residueField x.1) y
    have himage : closedPointMap i y = x := by
      apply Subtype.ext
      exact W.fromSpecResidueField_apply x.1
        (IsLocalRing.closedPoint (W.residueField x.1))
    rw [hfund]
    unfold pushforwardClosedCycle
    rw [Finsupp.mapDomain_single, himage]
  exact ⟨r, hr.trans (congrArg (fun z => r + z) hpoint), hdegree⟩

/-- The same canonical complementary cycle and original closed-point cycle
push through the actual supplied ambient embedding, preserving degree. -/
theorem conic_cubic_closedPoint_complement_cycle_in_ambient_anyField
    (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q f)
    {X : Scheme.{u}} (c : scheme (conicCubicHomogeneousIdeal q f hq hf) ⟶ X)
    [IsClosedImmersion c] (g : X ⟶ Spec (.of K))
    (hbase : c ≫ g = toBase (conicCubicHomogeneousIdeal q f hq hf))
    (x : closedPoints (scheme (conicCubicHomogeneousIdeal q f hq hf)))
    (d : ℕ) (hx : (toBase (conicCubicHomogeneousIdeal q f hq hf)).residueDegree x.1 = d) :
    letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
    ∃ r : EffectiveZeroCycle X,
      pushforwardClosedCycle c
        (finiteSchemeFundamentalCycle (toBase (conicCubicHomogeneousIdeal q f hq hf))) =
        r + Finsupp.single (closedPointMap c x) 1 ∧
      EffectiveZeroCycle.degree g r = 6 - d := by
  letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
  obtain ⟨r, hr, hdegree⟩ :=
    conic_cubic_closedPoint_complement_cycle_anyField q f hq hf hq0 hrel x d hx
  refine ⟨pushforwardClosedCycle c r, ?_, ?_⟩
  · rw [hr]
    unfold pushforwardClosedCycle
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  · rw [degree_pushforwardClosedCycle, hbase]
    exact hdegree

end PfaffianDescent

