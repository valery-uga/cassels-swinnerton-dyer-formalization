import AllCharacteristics.CubicDegreeThreeCycle
import AllCharacteristics.ExternalDegreeReduction
import AllCharacteristics.SchemeQuadraticDescent
import PfaffianDescent.VoisinCycleArithmetic
import PfaffianDescent.VoisinFiniteSubschemeRankTwoFamily
import PfaffianDescent.SerreExtensionPencilGluing

/-!
# Voisin's reduction of Coray's degree-ten alternative

Coray's theorem reduces a degree-one zero-cycle on a smooth cubic surface in
characteristic zero to a closed point of degree `1`, `4`, or `10`.  The only
part of Voisin's Theorem 1.5 needed after that result is the elimination of the
degree-ten case.  This file states the three concrete geometric effectivity
constructions used in that elimination and proves that, once constructed,
they give Voisin's conclusion.

Unlike the former `VoisinDegreeOneOrFourFor` interface, the source theorem is
not treated as one opaque implication.  The residual and rank-two-bundle
steps live in `PfaffianDescent.VoisinDegreeTenSteps`, over the quotient by
actual finite-flat curve families.
-/

open AlgebraicGeometry CategoryTheory PfaffianDescent
namespace AllCharacteristics
open HomogeneousProjective
universe u

/-- Coray's allowed external input, with its three alternatives stated using
the actual residue degrees of closed points. -/
def CorayDegreeOneFourOrTenFor (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
    p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
    ∀ z : ZeroCycle (hypersurface p hp),
      ZeroCycle.degree (hypersurfaceToBase p hp) z = 1 →
      ∃ x : closedPoints (hypersurface p hp),
        (hypersurfaceToBase p hp).residueDegree x.1 = 1 ∨
        (hypersurfaceToBase p hp).residueDegree x.1 = 4 ∨
        (hypersurfaceToBase p hp).residueDegree x.1 = 10

/-- The precise remaining geometric content of the degree-ten part of
Voisin's proof on a fixed cubic surface: a degree-three reference cycle and
the three effectivity constructions attached to its class. -/
def VoisinDegreeTenGeometryFor (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
    p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
      ∃ h : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 ∧
        VoisinDegreeTenSteps (hypersurfaceToBase p hp) h

/-- The degree-ten input with each residual construction represented by an
actual finite-flat family over the projective line. -/
def VoisinDegreeTenFamilyGeometryFor (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
    p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
      ∃ h : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 ∧
        VoisinDegreeTenFamilySteps (hypersurfaceToBase p hp) h

/-- The exact degree-ten input required after Coray has selected a closed
point of degree ten.  This is weaker than the historical uniform interface:
the paper constructs only the three residual classes attached to that point,
not a construction for every cycle of degree `16`, `11`, or `8`. -/
def VoisinDegreeTenPointGeometryFor (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
    p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
      ∀ x : closedPoints (hypersurface p hp),
        (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10) →
        ∃ h : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 ∧
          VoisinDegreeTenPointSteps (hypersurfaceToBase p hp) h (Finsupp.single x 1)

/-- The weakest degree-ten input needed for the rational-point conclusion:
every degree-ten closed point on a smooth cubic surface leads to some
effective zero-cycle of degree four.  Unlike the stronger interfaces above,
this does not retain rational-equivalence classes that are only needed for
Voisin's broader Chow-group statements. -/
def VoisinDegreeTenEffectiveDegreeFourFor
    (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
    p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
      ∀ x : closedPoints (hypersurface p hp),
        (hypersurfaceToBase p hp).residueDegree x.1 = 10 →
        ∃ z₄ : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₄ = 4

/-- A concrete family-level strengthening of
`VoisinDegreeTenPointGeometryFor`.  It retains one finite-flat endpoint
family for each residual class. -/
def VoisinDegreeTenPointFamilyGeometryFor (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
    p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
      ∀ x : closedPoints (hypersurface p hp),
        (hypersurfaceToBase p hp).residueDegree x.1 = 10 →
        ∃ h : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 ∧
          Nonempty (VoisinDegreeTenPointFamilySteps (hypersurfaceToBase p hp) h
            (Finsupp.single x 1))

/-- A scheme-level version of the point-specific geometry: all three moving
constructions are finite-flat pencils with their actual endpoint subschemes.
The conversion to `VoisinDegreeTenPointFamilyGeometryFor` is proved below,
so later work can construct the pencils themselves instead of postulating
cycle equalities. -/
def VoisinDegreeTenPointPencilGeometryFor (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
    p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
      ∀ x : closedPoints (hypersurface p hp),
        (hypersurfaceToBase p hp).residueDegree x.1 = 10 →
        ∃ h : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 ∧
          Nonempty (VoisinDegreeTenPointPencilSteps (hypersurfaceToBase p hp) h
            (Finsupp.single x 1))

/-- The point-specific family input with the degree-three cycle fixed to the
canonical finite line-section cycle.  This is the narrow geometric statement
needed for Coray's degree-ten alternative: it allows a non-split degree-ten
closed point while retaining the actual line-section reference cycle. -/
def VoisinDegreeTenPointLineSectionFamilyGeometryFor
    (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hne : p ≠ 0), Smooth (hypersurfaceToBase p hp) →
      ∀ x : closedPoints (hypersurface p hp),
        (hypersurfaceToBase p hp).residueDegree x.1 = 10 →
        Nonempty (VoisinDegreeTenPointFamilySteps (hypersurfaceToBase p hp)
          (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne)
          (Finsupp.single x 1))

/-- The scheme-level line-section formulation retains the three finite-flat
pencils used in Voisin's argument.  It is the concrete geometric input needed
after Coray has produced a degree-ten closed point. -/
def VoisinDegreeTenPointLineSectionPencilGeometryFor
    (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hne : p ≠ 0), Smooth (hypersurfaceToBase p hp) →
      ∀ x : closedPoints (hypersurface p hp),
        (hypersurfaceToBase p hp).residueDegree x.1 = 10 →
        Nonempty (VoisinDegreeTenPointPencilSteps (hypersurfaceToBase p hp)
          (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne)
          (Finsupp.single x 1))

/-- The scheme-level inputs still needed from Voisin after Coray supplies a
degree-ten point.  Endpoint calculations are equalities in the quotient by
finite-flat curve families, as required for rational equivalence; they are
not literal equalities of the effective cycles of distinct line sections. -/
def VoisinDegreeTenPointLineSectionPencilClassGeometryFor
    (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hne : p ≠ 0), Smooth (hypersurfaceToBase p hp) →
      ∀ x : closedPoints (hypersurface p hp),
        (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10) →
        ∃ C : DegreeTenRankSixteenCompletion p hp
            (finiteSubschemeDatumOfClosedPointOfResidueDegree
              (hypersurfaceToBase p hp) x 10 hx),
          ∃ S : VoisinDegreeTenPointPencilData (hypersurfaceToBase p hp),
            S.D₁₆ = C.datum ∧
            curveFamilyCycleClass (hypersurfaceToBase p hp)
              (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.first).toZeroCycle =
                curveFamilyCycleClass (hypersurfaceToBase p hp)
                  (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne).toZeroCycle ∧
            curveFamilyCycleClass (hypersurfaceToBase p hp)
              (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.second).toZeroCycle =
                curveFamilyCycleClass (hypersurfaceToBase p hp)
                  (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne).toZeroCycle ∧
            curveFamilyCycleClass (hypersurfaceToBase p hp)
              (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) S.D₂₇).toZeroCycle =
                9 • curveFamilyCycleClass (hypersurfaceToBase p hp)
                  (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne).toZeroCycle ∧
            curveFamilyCycleClass (hypersurfaceToBase p hp)
              (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) S.D₃).toZeroCycle =
                curveFamilyCycleClass (hypersurfaceToBase p hp)
                  (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne).toZeroCycle ∧
            curveFamilyCycleClass (hypersurfaceToBase p hp)
              (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) S.D₁₂).toZeroCycle =
                4 • curveFamilyCycleClass (hypersurfaceToBase p hp)
                  (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne).toZeroCycle

/-- The scheme-level degree-ten input with the first endpoint identified by
an isomorphism over the cubic surface.  A complete-intersection construction
usually produces this isomorphism, rather than definitional equality between
two separately presented closed subschemes. -/
def VoisinDegreeTenPointLineSectionPencilClassGeometryForIso
    (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hne : p ≠ 0), Smooth (hypersurfaceToBase p hp) →
      ∀ x : closedPoints (hypersurface p hp),
        (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10) →
        ∃ C : DegreeTenRankSixteenCompletion p hp
            (finiteSubschemeDatumOfClosedPointOfResidueDegree
              (hypersurfaceToBase p hp) x 10 hx),
          ∃ S : VoisinDegreeTenPointPencilData (hypersurfaceToBase p hp),
            (∃ e : S.D₁₆.val.subscheme ≅ C.datum.val.subscheme,
              e.hom ≫ C.datum.val.subschemeι = S.D₁₆.val.subschemeι) ∧
            curveFamilyCycleClass (hypersurfaceToBase p hp)
              (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.first).toZeroCycle =
                curveFamilyCycleClass (hypersurfaceToBase p hp)
                  (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne).toZeroCycle ∧
            curveFamilyCycleClass (hypersurfaceToBase p hp)
              (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.second).toZeroCycle =
                curveFamilyCycleClass (hypersurfaceToBase p hp)
                  (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne).toZeroCycle ∧
            curveFamilyCycleClass (hypersurfaceToBase p hp)
              (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) S.D₂₇).toZeroCycle =
                9 • curveFamilyCycleClass (hypersurfaceToBase p hp)
                  (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne).toZeroCycle ∧
            curveFamilyCycleClass (hypersurfaceToBase p hp)
              (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) S.D₃).toZeroCycle =
                curveFamilyCycleClass (hypersurfaceToBase p hp)
                  (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne).toZeroCycle ∧
            curveFamilyCycleClass (hypersurfaceToBase p hp)
              (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) S.D₁₂).toZeroCycle =
                4 • curveFamilyCycleClass (hypersurfaceToBase p hp)
                  (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne).toZeroCycle

/-- The line-section formulation supplies the previously factored
point-specific family geometry. -/
theorem voisinDegreeTenPointFamilyGeometryFor_of_lineSectionFamilyGeometryFor
    {k : Type u} [Field k] [CharZero k]
    (lineGeometry : VoisinDegreeTenPointLineSectionFamilyGeometryFor k) :
    VoisinDegreeTenPointFamilyGeometryFor k := by
  intro p hp hne hs x hx₁₀
  refine ⟨PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne,
    PfaffianDescent.cubicLineSectionCycle_degree (by decide) p hp hne, ?_⟩
  exact lineGeometry p hp hne hs x hx₁₀

/-- Concrete line-section pencils supply the point-specific pencil geometry. -/
theorem voisinDegreeTenPointPencilGeometryFor_of_lineSectionPencilGeometryFor
    {k : Type u} [Field k] [CharZero k]
    (lineGeometry : VoisinDegreeTenPointLineSectionPencilGeometryFor k) :
    VoisinDegreeTenPointPencilGeometryFor k := by
  intro p hp hne hs x hx₁₀
  refine ⟨PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne,
    PfaffianDescent.cubicLineSectionCycle_degree (by decide) p hp hne, ?_⟩
  exact lineGeometry p hp hne hs x hx₁₀

/-- The pencil data with quotient-level endpoint calculations gives the exact
point-specific geometry required to eliminate Coray's degree-ten branch. -/
theorem voisinDegreeTenPointGeometryFor_of_lineSectionPencilClassGeometryFor
    {k : Type u} [Field k] [CharZero k]
    (geometry : VoisinDegreeTenPointLineSectionPencilClassGeometryFor k) :
    VoisinDegreeTenPointGeometryFor k := by
  intro p hp hne hs x hx₁₀
  obtain ⟨C, S, hD₁₆, hfirst, hsecond, h₂₇, h₃, h₁₂⟩ :=
    geometry p hp hne hs x hx₁₀
  refine ⟨PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne,
    PfaffianDescent.cubicLineSectionCycle_degree (by decide) p hp hne, ?_⟩
  exact voisinDegreeTenPointSteps_of_completion_and_cycleClasses p hp x hx₁₀ C
    (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne)
    hfirst hsecond S hD₁₆ h₂₇ h₃ h₁₂

/-- The isomorphism-based endpoint formulation gives the same degree-ten
conclusion.  This is the version suited to actual finite-subscheme pencils,
whose endpoints are canonically isomorphic to the selected residual data. -/
theorem voisinDegreeTenPointGeometryFor_of_lineSectionPencilClassGeometryForIso
    {k : Type u} [Field k] [CharZero k]
    (geometry : VoisinDegreeTenPointLineSectionPencilClassGeometryForIso k) :
    VoisinDegreeTenPointGeometryFor k := by
  intro p hp hne hs x hx₁₀
  obtain ⟨C, S, e₁₆, hfirst, hsecond, h₂₇, h₃, h₁₂⟩ :=
    geometry p hp hne hs x hx₁₀
  obtain ⟨e, he⟩ := e₁₆
  refine ⟨PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne,
    PfaffianDescent.cubicLineSectionCycle_degree (by decide) p hp hne, ?_⟩
  exact voisinDegreeTenPointSteps_of_completion_and_cycleClasses_of_iso p hp x hx₁₀ C
    (PfaffianDescent.cubicLineSectionCycle (by decide) p hp hne)
    hfirst hsecond S e he h₂₇ h₃ h₁₂

/-- The concrete family formulation implies the quotient-level geometry used
by the degree-ten arithmetic. -/
theorem voisinDegreeTenGeometryFor_of_familyGeometryFor
    {k : Type u} [Field k] [CharZero k]
    (familyGeometry : VoisinDegreeTenFamilyGeometryFor k) :
    VoisinDegreeTenGeometryFor k := by
  intro p hp hne hs
  obtain ⟨h, hh, families⟩ := familyGeometry p hp hne hs
  exact ⟨h, hh, voisinDegreeTenSteps_of_familySteps
    (hypersurfaceToBase p hp) h families⟩

/-- The historical uniform family statement entails the point-specific form
needed after Coray supplies a degree-ten closed point. -/
theorem voisinDegreeTenPointFamilyGeometryFor_of_familyGeometryFor
    {k : Type u} [Field k] [CharZero k]
    (familyGeometry : VoisinDegreeTenFamilyGeometryFor k) :
    VoisinDegreeTenPointFamilyGeometryFor k := by
  intro p hp hne hs x hx₁₀
  obtain ⟨h, hh, families⟩ := familyGeometry p hp hne hs
  let z₁₀ : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
  have hz₁₀ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₁₀ = 10 := by
    simp [z₁₀, EffectiveZeroCycle.degree, hx₁₀]
  exact ⟨h, hh, nonempty_voisinDegreeTenPointFamilySteps_of_familySteps
    (hypersurfaceToBase p hp) h z₁₀ hh families hz₁₀⟩

/-- Concrete endpoint families imply the quotient-level point-specific
geometry used by Voisin's proof. -/
theorem voisinDegreeTenPointGeometryFor_of_pointFamilyGeometryFor
    {k : Type u} [Field k] [CharZero k]
    (familyGeometry : VoisinDegreeTenPointFamilyGeometryFor k) :
    VoisinDegreeTenPointGeometryFor k := by
  intro p hp hne hs x hx₁₀
  obtain ⟨h, hh, hsteps⟩ := familyGeometry p hp hne hs x hx₁₀
  exact ⟨h, hh, voisinDegreeTenPointSteps_of_familySteps
    (hypersurfaceToBase p hp) h (Finsupp.single x 1) (Classical.choice hsteps)⟩

/-- The concrete pencil formulation implies the point-specific endpoint-family
geometry used after Coray's degree-ten alternative. -/
theorem voisinDegreeTenPointFamilyGeometryFor_of_pointPencilGeometryFor
    {k : Type u} [Field k] [CharZero k]
    (pencilGeometry : VoisinDegreeTenPointPencilGeometryFor k) :
    VoisinDegreeTenPointFamilyGeometryFor k := by
  intro p hp hne hs x hx₁₀
  obtain ⟨h, hh, hpencils⟩ := pencilGeometry p hp hne hs x hx₁₀
  exact ⟨h, hh, ⟨(Classical.choice hpencils).toFamilySteps
    (hypersurfaceToBase p hp)⟩⟩

/-- The exact line-section family input also gives the quotient-level
point-specific geometry. -/
theorem voisinDegreeTenPointGeometryFor_of_lineSectionFamilyGeometryFor
    {k : Type u} [Field k] [CharZero k]
    (lineGeometry : VoisinDegreeTenPointLineSectionFamilyGeometryFor k) :
    VoisinDegreeTenPointGeometryFor k :=
  voisinDegreeTenPointGeometryFor_of_pointFamilyGeometryFor
    (voisinDegreeTenPointFamilyGeometryFor_of_lineSectionFamilyGeometryFor
      lineGeometry)

/-- The earlier uniform family interface entails the exact point-specific
quotient-level interface. -/
theorem voisinDegreeTenPointGeometryFor_of_familyGeometryFor
    {k : Type u} [Field k] [CharZero k]
    (familyGeometry : VoisinDegreeTenFamilyGeometryFor k) :
    VoisinDegreeTenPointGeometryFor k := by
  exact voisinDegreeTenPointGeometryFor_of_pointFamilyGeometryFor
    (voisinDegreeTenPointFamilyGeometryFor_of_familyGeometryFor familyGeometry)

/-- The class-level point-specific construction supplies the weaker
existence-only input used by the rational-point proof. -/
theorem voisinDegreeTenEffectiveDegreeFourFor_of_pointGeometryFor
    {k : Type u} [Field k] [CharZero k]
    (geometry : VoisinDegreeTenPointGeometryFor k) :
    VoisinDegreeTenEffectiveDegreeFourFor k := by
  intro p hp hne hs x hx₁₀
  obtain ⟨h, hh, steps⟩ := geometry p hp hne hs x hx₁₀
  let z₁₀ : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
  have hz₁₀ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₁₀ = 10 := by
    simp [z₁₀, EffectiveZeroCycle.degree, hx₁₀]
  exact effective_degree_four_of_voisin_degree_ten_point_steps
    (hypersurfaceToBase p hp) h z₁₀ hh hz₁₀ steps

/- This deliberately stronger uniform interface may be applied to the
degree-three line-section cycle constructed below.  It does not assert that
every degree-three cycle has the line-section rational-equivalence properties
used by Voisin's geometric argument. -/
theorem voisinDegreeTenFamilyGeometryFor_of_uniform_familySteps
    {k : Type u} [Field k] [CharZero k]
    (familySteps : ∀ (p : MvPolynomial (Fin 4) k)
      (hp : p.IsHomogeneous 3), p ≠ 0 →
      Smooth (hypersurfaceToBase p hp) →
      ∀ h : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 →
        VoisinDegreeTenFamilySteps (hypersurfaceToBase p hp) h) :
    VoisinDegreeTenFamilyGeometryFor k := by
  intro p hp hne hs
  obtain ⟨h, hh⟩ := hypersurface_exists_lineSection_effective_degree_three
    (k := k) (n := 4) (by decide) p hp hne
  exact ⟨h, hh, familySteps p hp hne hs h hh⟩

/-- A rational section determines an actual closed point of residue degree
one. -/
theorem exists_closedPoint_degree_one_of_section
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    ∃ x : closedPoints X, f.residueDegree x.1 = 1 := by
  have his : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id f s hs
  let b : closedPoints (Spec (.of k)) :=
    ⟨IsLocalRing.closedPoint k, isClosed_singleton⟩
  let x : closedPoints X := ⟨s b.1, by
    change IsClosed {s b.1}
    rw [← Set.image_singleton]
    exact s.isClosedMap _ b.2⟩
  refine ⟨x, ?_⟩
  have hd := residueDegree_comp s f b.1
  rw [hs, Scheme.Hom.residueDegree_id] at hd
  change 1 = f.residueDegree x.1 * s.residueDegree b.1 at hd
  exact Nat.eq_one_of_mul_eq_one_right hd.symm

/-- Coray's three alternatives yield a rational point as soon as the
degree-ten branch supplies an effective degree-four cycle.  This is the
minimal Voisin interface needed by the paper's rational-point conclusion;
no rational-equivalence identity for the intermediate cycles is used. -/
theorem cubic_section_of_zeroCycle_degree_one_of_coray_and_effectiveDegreeFour
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenEffectiveDegreeFourFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨x, hx₁ | hx₄ | hx₁₀⟩ := coray p hp hne inferInstance z hz
  · exact section_of_residueDegree_one (hypersurfaceToBase p hp) x.1 hx₁
  · exact hypersurface_section_of_closedPoint_degree_four p hp x hx₄
  · obtain ⟨z₄, hz₄⟩ := geometry p hp hne inferInstance x hx₁₀
    exact hypersurface_section_of_effective_degree_four p hp z₄ hz₄

/-- For the rational-point argument, the effective degree-four output also
supplies Voisin's closed-point alternative: a degree-four cycle either has a
degree-four closed point or yields a rational section. -/
theorem voisinDegreeOneOrFourFor_of_coray_and_effectiveDegreeFour
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenEffectiveDegreeFourFor k) :
    VoisinDegreeOneOrFourFor k := by
  intro p hp hne hs z hz
  letI : Smooth (hypersurfaceToBase p hp) := hs
  obtain ⟨x, hx₁ | hx₄ | hx₁₀⟩ := coray p hp hne inferInstance z hz
  · exact ⟨x, Or.inl hx₁⟩
  · exact ⟨x, Or.inr hx₄⟩
  · obtain ⟨z₄, hz₄⟩ := geometry p hp hne inferInstance x hx₁₀
    rcases hypersurface_section_or_quartic_of_effective_degree_four p hp z₄ hz₄ with
      ⟨q, hq⟩ | ⟨y, _, hy⟩
    · obtain ⟨y, hy⟩ := exists_closedPoint_degree_one_of_section
        (hypersurfaceToBase p hp) q hq
      exact ⟨y, Or.inl hy⟩
    · exact ⟨y, Or.inr hy⟩

/-- Coray's alternatives together with the point-specific endpoint-family
chain eliminate precisely its degree-ten branch. -/
theorem voisin_degree_one_or_four_of_coray_and_degree_ten_point_family_geometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenPointFamilyGeometryFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ x : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree x.1 = 1 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 4 := by
  obtain ⟨x, hx₁ | hx₄ | hx₁₀⟩ := coray p hp hne inferInstance z hz
  · exact ⟨x, Or.inl hx₁⟩
  · exact ⟨x, Or.inr hx₄⟩
  · obtain ⟨h, hh, hsteps⟩ := geometry p hp hne inferInstance x hx₁₀
    let z₁₀ : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
    have hz₁₀ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₁₀ = 10 := by
      simp [z₁₀, EffectiveZeroCycle.degree, hx₁₀]
    let steps := Classical.choice hsteps
    obtain ⟨z₄, hz₄⟩ := effective_degree_four_of_voisin_degree_ten_point_family_steps
      (hypersurfaceToBase p hp) h z₁₀ hh hz₁₀ steps
    rcases hypersurface_section_or_quartic_of_effective_degree_four p hp z₄ hz₄ with
      ⟨q, hq⟩ | ⟨y, _, hy⟩
    · obtain ⟨y, hy⟩ := exists_closedPoint_degree_one_of_section
        (hypersurfaceToBase p hp) q hq
      exact ⟨y, Or.inl hy⟩
    · exact ⟨y, Or.inr hy⟩

/-- Coray's alternatives together with the three quotient-level residual
classes attached to a degree-ten point eliminate precisely that branch. -/
theorem voisin_degree_one_or_four_of_coray_and_degree_ten_point_geometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenPointGeometryFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ x : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree x.1 = 1 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 4 := by
  obtain ⟨x, hx₁ | hx₄ | hx₁₀⟩ := coray p hp hne inferInstance z hz
  · exact ⟨x, Or.inl hx₁⟩
  · exact ⟨x, Or.inr hx₄⟩
  · obtain ⟨h, hh, steps⟩ := geometry p hp hne inferInstance x hx₁₀
    let z₁₀ : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
    have hz₁₀ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₁₀ = 10 := by
      simp [z₁₀, EffectiveZeroCycle.degree, hx₁₀]
    obtain ⟨z₄, hz₄⟩ := effective_degree_four_of_voisin_degree_ten_point_steps
      (hypersurfaceToBase p hp) h z₁₀ hh hz₁₀ steps
    rcases hypersurface_section_or_quartic_of_effective_degree_four p hp z₄ hz₄ with
      ⟨q, hq⟩ | ⟨y, _, hy⟩
    · obtain ⟨y, hy⟩ := exists_closedPoint_degree_one_of_section
        (hypersurfaceToBase p hp) q hq
      exact ⟨y, Or.inl hy⟩
    · exact ⟨y, Or.inr hy⟩

/-- The point-specific endpoint-family form already gives the rational
section required by the characteristic-zero cubic-surface argument. -/
theorem cubic_section_of_zeroCycle_degree_one_of_coray_and_degree_ten_point_family_geometry_direct
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenPointFamilyGeometryFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨x, hx₁ | hx₄⟩ :=
    voisin_degree_one_or_four_of_coray_and_degree_ten_point_family_geometry
      coray geometry p hp hne z hz
  · exact section_of_residueDegree_one (hypersurfaceToBase p hp) x.1 hx₁
  · let z₄ : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
    have hz₄ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₄ = 4 := by
      simp [z₄, EffectiveZeroCycle.degree, hx₄]
    exact cubic_section_of_effective_degree_four_or_five p hp hne z₄ (Or.inl hz₄)

/-- Coray's alternative plus the endpoint families attached to each
degree-ten point gives the reusable closed-point form of Voisin's theorem. -/
theorem voisinDegreeOneOrFourFor_of_coray_and_degree_ten_point_family_geometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenPointFamilyGeometryFor k) :
    VoisinDegreeOneOrFourFor k := by
  intro p hp hne hs z hz
  letI : Smooth (hypersurfaceToBase p hp) := hs
  exact voisin_degree_one_or_four_of_coray_and_degree_ten_point_family_geometry
    coray geometry p hp hne z hz

/-- Coray's degree-ten alternative is eliminated once Voisin's three moving
constructions have been supplied as concrete finite-flat pencils. -/
theorem voisinDegreeOneOrFourFor_of_coray_and_degree_ten_point_pencil_geometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (pencilGeometry : VoisinDegreeTenPointPencilGeometryFor k) :
    VoisinDegreeOneOrFourFor k :=
  voisinDegreeOneOrFourFor_of_coray_and_degree_ten_point_family_geometry coray
    (voisinDegreeTenPointFamilyGeometryFor_of_pointPencilGeometryFor pencilGeometry)

/-- Coray's alternative and the three concrete pencils based at the canonical
line section eliminate the degree-ten branch. -/
theorem voisinDegreeOneOrFourFor_of_coray_and_degree_ten_lineSectionPencilGeometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (lineGeometry : VoisinDegreeTenPointLineSectionPencilGeometryFor k) :
    VoisinDegreeOneOrFourFor k :=
  voisinDegreeOneOrFourFor_of_coray_and_degree_ten_point_pencil_geometry coray
    (voisinDegreeTenPointPencilGeometryFor_of_lineSectionPencilGeometryFor
      lineGeometry)

/-- Coray's theorem and the quotient-level pencil calculations from Voisin's
degree-ten construction imply the degree-one-or-four alternative. -/
theorem voisinDegreeOneOrFourFor_of_coray_and_degree_ten_lineSectionPencilClassGeometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenPointLineSectionPencilClassGeometryFor k) :
    VoisinDegreeOneOrFourFor k := by
  intro p hp hne hs z hz
  letI : Smooth (hypersurfaceToBase p hp) := hs
  exact voisin_degree_one_or_four_of_coray_and_degree_ten_point_geometry coray
    (voisinDegreeTenPointGeometryFor_of_lineSectionPencilClassGeometryFor geometry)
    p hp hne z hz

/-- The same Coray--Voisin conclusion from the endpoint formulation used by
actual complete-intersection families.  Their special fiber is canonically
isomorphic over the cubic surface to the completed rank-sixteen datum, rather
than definitionally equal to it. -/
theorem voisinDegreeOneOrFourFor_of_coray_and_degree_ten_lineSectionPencilClassGeometryForIso
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenPointLineSectionPencilClassGeometryForIso k) :
    VoisinDegreeOneOrFourFor k := by
  intro p hp hne hs z hz
  letI : Smooth (hypersurfaceToBase p hp) := hs
  exact voisin_degree_one_or_four_of_coray_and_degree_ten_point_geometry coray
    (voisinDegreeTenPointGeometryFor_of_lineSectionPencilClassGeometryForIso geometry)
    p hp hne z hz

/-- Coray's alternative and the three endpoint families for the canonical
line-section cycle yield the formal closed-point conclusion of Voisin's
degree-ten reduction. -/
theorem voisinDegreeOneOrFourFor_of_coray_and_degree_ten_lineSectionFamilyGeometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (lineGeometry : VoisinDegreeTenPointLineSectionFamilyGeometryFor k) :
    VoisinDegreeOneOrFourFor k :=
  voisinDegreeOneOrFourFor_of_coray_and_degree_ten_point_family_geometry coray
    (voisinDegreeTenPointFamilyGeometryFor_of_lineSectionFamilyGeometryFor
      lineGeometry)

/-- The quotient-level point-specific form gives the same rational-section
conclusion, with no choice of a single family representing a rational
equivalence class. -/
theorem cubic_section_of_zeroCycle_degree_one_of_coray_and_degree_ten_point_geometry_direct
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenPointGeometryFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨x, hx₁ | hx₄⟩ :=
    voisin_degree_one_or_four_of_coray_and_degree_ten_point_geometry
      coray geometry p hp hne z hz
  · exact section_of_residueDegree_one (hypersurfaceToBase p hp) x.1 hx₁
  · let z₄ : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
    have hz₄ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₄ = 4 := by
      simp [z₄, EffectiveZeroCycle.degree, hx₄]
    exact cubic_section_of_effective_degree_four_or_five p hp hne z₄ (Or.inl hz₄)

/-- Coray's alternative together with the exact point-specific degree-ten
cycle classes yields Voisin's reusable characteristic-zero interface. -/
theorem voisinDegreeOneOrFourFor_of_coray_and_degree_ten_point_geometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenPointGeometryFor k) :
    VoisinDegreeOneOrFourFor k := by
  intro p hp hne hs z hz
  letI : Smooth (hypersurfaceToBase p hp) := hs
  exact voisin_degree_one_or_four_of_coray_and_degree_ten_point_geometry
    coray geometry p hp hne z hz

/-- Coray's `1/4/10` theorem plus Voisin's three explicit degree-ten
constructions gives the exact closed-point conclusion of Voisin's theorem. -/
theorem voisin_degree_one_or_four_of_coray_and_degree_ten_geometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenGeometryFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ x : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree x.1 = 1 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 4 := by
  obtain ⟨x, hx₁ | hx₄ | hx₁₀⟩ := coray p hp hne inferInstance z hz
  · exact ⟨x, Or.inl hx₁⟩
  · exact ⟨x, Or.inr hx₄⟩
  · obtain ⟨h, hh, steps⟩ := geometry p hp hne inferInstance
    let z₁₀ : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
    have hz₁₀ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₁₀ = 10 := by
      simp [z₁₀, EffectiveZeroCycle.degree, hx₁₀]
    obtain ⟨z₄, hz₄⟩ := effective_degree_four_of_voisin_degree_ten_steps
      (hypersurfaceToBase p hp) h hh steps z₁₀ hz₁₀
    rcases hypersurface_section_or_quartic_of_effective_degree_four p hp z₄ hz₄ with
      ⟨q, hq⟩ | ⟨y, _, hy⟩
    · obtain ⟨y, hy⟩ := exists_closedPoint_degree_one_of_section
        (hypersurfaceToBase p hp) q hq
      exact ⟨y, Or.inl hy⟩
    · exact ⟨y, Or.inr hy⟩

/- The direct cubic-cycle descent turns the `1/4` output above into a
   rational section without introducing the intermediate Voisin interface.
   In particular, the degree-four branch needs no separate quadratic-
   effectivity hypothesis. -/
theorem cubic_section_of_zeroCycle_degree_one_of_coray_and_degree_ten_geometry_direct
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenGeometryFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨x, hx₁ | hx₄⟩ := voisin_degree_one_or_four_of_coray_and_degree_ten_geometry
    coray geometry p hp hne z hz
  · exact section_of_residueDegree_one (hypersurfaceToBase p hp) x.1 hx₁
  · let z₄ : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
    have hz₄ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₄ = 4 := by
      simp [z₄, EffectiveZeroCycle.degree, hx₄]
    exact cubic_section_of_effective_degree_four_or_five p hp hne z₄ (Or.inl hz₄)

/- In characteristic zero the degree-four residual is itself enough to
produce a section, so the degree-ten branch can be isolated as a direct
point-producing theorem. -/
theorem cubic_section_of_degree_ten_point_of_degree_ten_geometry
    {k : Type u} [Field k] [CharZero k]
    (geometry : VoisinDegreeTenGeometryFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx₁₀ : (hypersurfaceToBase p hp).residueDegree x.1 = 10) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨h, hh, steps⟩ := geometry p hp hne inferInstance
  let z₁₀ : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
  have hz₁₀ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₁₀ = 10 := by
    simp [z₁₀, EffectiveZeroCycle.degree, hx₁₀]
  obtain ⟨z₄, hz₄⟩ := effective_degree_four_of_voisin_degree_ten_steps
    (hypersurfaceToBase p hp) h hh steps z₁₀ hz₁₀
  exact hypersurface_section_of_effective_degree_four p hp z₄ hz₄

/-- The exact Voisin input used by the characteristic-zero reduction follows
from Coray's `1/4/10` alternative once the three degree-ten constructions are
available.  This packages the two paper dependencies without introducing a
stronger opaque `VoisinDegreeOneOrFourFor` hypothesis. -/
theorem voisinDegreeOneOrFourFor_of_coray_and_degree_ten_geometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenGeometryFor k) :
    VoisinDegreeOneOrFourFor k := by
  intro p hp hne hs z hz
  letI : Smooth (hypersurfaceToBase p hp) := hs
  exact voisin_degree_one_or_four_of_coray_and_degree_ten_geometry
    coray geometry p hp hne z hz

/-- Coray's alternative and explicit endpoint families imply Voisin's exact
characteristic-zero closed-point conclusion. -/
theorem voisinDegreeOneOrFourFor_of_coray_and_degree_ten_family_geometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (familyGeometry : VoisinDegreeTenFamilyGeometryFor k) :
    VoisinDegreeOneOrFourFor k := by
  exact voisinDegreeOneOrFourFor_of_coray_and_degree_ten_geometry coray
    (voisinDegreeTenGeometryFor_of_familyGeometryFor familyGeometry)

/- The family formulation also gives the closed-point `1/4` conclusion
directly, before packaging it as the reusable Voisin interface. -/
theorem voisin_degree_one_or_four_of_coray_and_degree_ten_family_geometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (familyGeometry : VoisinDegreeTenFamilyGeometryFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ x : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree x.1 = 1 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 4 := by
  exact voisin_degree_one_or_four_of_coray_and_degree_ten_geometry coray
    (voisinDegreeTenGeometryFor_of_familyGeometryFor familyGeometry)
    p hp hne z hz

/-- Coordinate form of the characteristic-zero reduction with the two paper
dependencies exposed separately. -/
theorem charZero_smooth_cubic_coordinates_of_coray_and_degree_ten_geometry
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenGeometryFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  exact charZero_smooth_cubic_coordinates_of_voisin
    (voisinDegreeOneOrFourFor_of_coray_and_degree_ten_geometry coray geometry)
    p hp hne z hz

end AllCharacteristics
