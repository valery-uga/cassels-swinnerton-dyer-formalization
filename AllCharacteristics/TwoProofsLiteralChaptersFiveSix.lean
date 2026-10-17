import AllCharacteristics.TwoProofs
import AllCharacteristics.FinitelyGeneratedSubschemeLifting
import AllCharacteristics.DVRSourceCycleLifting
import AllCharacteristics.CubicFiberDegreeThree
import AllCharacteristics.DVRDirectedColimit
import AllCharacteristics.AlgebraicExtensionDirectedUnion
import AllCharacteristics.CompatibleDirectedDVRLifting
import AllCharacteristics.CompleteDVRLiftTowerData
import AllCharacteristics.CompleteDVRLiftLimitData
import AllCharacteristics.AlgebraicExtensionTransfiniteDVRGlobal

/-!
# Literal paper-facing statements for Chapters 5 and 6

This module records the theorem statements in the specialization and
singular-surface chapters of `2-proofs.tex` in the homogeneous-projective
language used by the development.  The public conclusions use Coray and the internally proved actual native
degree-four factory. Conditional adapters retain the minimal effective-cycle
input. No stronger residual-class construction bundle is inferred or assumed.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
open HomogeneousProjective

universe u

/-- The conclusion of the paper's `lem:lift` for one field, cubic surface,
and closed point.  This is stated separately so that the unrestricted
Cohen-ring input is an exact, reviewable proposition rather than an implicit
parameter of the specialization proof. -/
def ChapterFiveLiftFor (k : Type u) [Field k] : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3), p ≠ 0 →
    Smooth (hypersurfaceToBase p hp) →
    ∀ x : closedPoints (hypersurface p hp),
      ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (_ : CharZero R)
        (b : R →+* k), Function.Surjective b ∧
        ∃ q : MvPolynomial (Fin 4) R, ∃ hq : q.IsHomogeneous 3,
          ∃ he : q.map b = p, Smooth (hypersurfaceToBase q hq) ∧
          ∃ (Z : Scheme.{u}) (i : Z ⟶ hypersurface q hq)
            (j : Spec (.of ((hypersurface p hp).residueField x.1)) ⟶ Z),
            IsClosedImmersion i ∧ IsFinite (i ≫ hypersurfaceToBase q hq) ∧
            Flat (i ≫ hypersurfaceToBase q hq) ∧
            (∀ r, (i ≫ hypersurfaceToBase q hq).finrank r =
              (hypersurfaceToBase p hp).residueDegree x.1) ∧
            IsPullback j ((hypersurface p hp).fromSpecResidueField x.1)
              i (hypersurfaceReductionMap b q hq p hp he)

/-- The unrestricted, literal statement of Chapter 5's `lem:lift`.

The Cohen-ring construction used in its arbitrary-field case is assembled
by well-order induction in `AlgebraicExtensionTransfiniteDVRGlobal`: finite
successors use finite-extension lifting, limit stages use a directed colimit
and completion, and the resulting compatible tower supplies the prescribed
residue field. -/
def ChapterFiveLiftStatement : Prop :=
  ∀ (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ],
    ChapterFiveLiftFor k

/-- The arithmetic input used by the unrestricted lifting lemma: a complete
mixed-characteristic DVR presenting each positive-characteristic field as
its residue field. -/
def ChapterFiveCohenRingStatement : Prop :=
  ∀ (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ],
    HasCompleteCharZeroDVRLift k

/-- The algebraic-extension closure principle in the Cohen-ring
construction. -/
def CompleteCharZeroDVRLiftAlgebraicExtensionClosure : Prop :=
  ∀ {K L : Type u} [Field K] [Field L] [Algebra K L],
    Algebra.IsAlgebraic K L →
    HasCompleteCharZeroDVRLift K → HasCompleteCharZeroDVRLift L

/-- Every finite node in an algebraic extension has a constructed complete
characteristic-zero DVR lift. -/
theorem hasCompleteCharZeroDVRLift_algebraicFiniteSubextension
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (hK : HasCompleteCharZeroDVRLift K) (s : Finset L) :
    HasCompleteCharZeroDVRLift (algebraicFiniteSubextension (K := K) s) := by
  letI : FiniteDimensional K (algebraicFiniteSubextension (K := K) s) :=
    finiteDimensional_algebraicFiniteSubextension s
  exact hK.finite_extension

/-- The literal geometric conclusion of `lem:lift`, over a supplied complete
characteristic-zero DVR with residue field `k`.  The pullback square is the
scheme-theoretic statement that the special fiber of the finite flat
subscheme is the original closed point. -/
theorem twoProofs_chapterFive_lift_of_completeCharZeroDVR
    {k : Type u} [Field k]
    (hR : HasCompleteCharZeroDVRLift k)
    {p : MvPolynomial (Fin 4) k} (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp)) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (_ : CharZero R)
      (b : R →+* k), Function.Surjective b ∧
      ∃ q : MvPolynomial (Fin 4) R, ∃ hq : q.IsHomogeneous 3,
        ∃ he : q.map b = p, Smooth (hypersurfaceToBase q hq) ∧
        ∃ (Z : Scheme.{u}) (i : Z ⟶ hypersurface q hq)
          (j : Spec (.of ((hypersurface p hp).residueField x.1)) ⟶ Z),
          IsClosedImmersion i ∧ IsFinite (i ≫ hypersurfaceToBase q hq) ∧
          Flat (i ≫ hypersurfaceToBase q hq) ∧
          (∀ r, (i ≫ hypersurfaceToBase q hq).finrank r =
            (hypersurfaceToBase p hp).residueDegree x.1) ∧
          IsPullback j ((hypersurface p hp).fromSpecResidueField x.1)
            i (hypersurfaceReductionMap b q hq p hp he) := by
  obtain ⟨R, _, _, _, _, _, b, hb⟩ := hR
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, b, hb, ?_⟩
  exact exists_smooth_lift_with_closed_subscheme b hb p hp hne x

/-- The exact Chapter 5 lifting conclusion holds over any field once its
complete characteristic-zero DVR lifting base has been constructed. -/
theorem chapterFiveLiftFor_of_completeCharZeroDVR
    {k : Type u} [Field k] (hR : HasCompleteCharZeroDVRLift k) :
    ChapterFiveLiftFor k := by
  intro ℓ _ _ p hp hne hs x
  letI : Smooth (hypersurfaceToBase p hp) := hs
  exact twoProofs_chapterFive_lift_of_completeCharZeroDVR hR hp hne x

/-- The literal lifting lemma for every finitely generated positive-
characteristic field.  This is the arbitrary-imperfection version already
constructed by the DVR-lifting development. -/
theorem twoProofs_chapterFive_lift_fg_positive
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] [Field.FG k]
    {p : MvPolynomial (Fin 4) k} (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp)) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (_ : CharZero R)
      (b : R →+* k), Function.Surjective b ∧
      ∃ q : MvPolynomial (Fin 4) R, ∃ hq : q.IsHomogeneous 3,
        ∃ he : q.map b = p, Smooth (hypersurfaceToBase q hq) ∧
        ∃ (Z : Scheme.{u}) (i : Z ⟶ hypersurface q hq)
          (j : Spec (.of ((hypersurface p hp).residueField x.1)) ⟶ Z),
          IsClosedImmersion i ∧ IsFinite (i ≫ hypersurfaceToBase q hq) ∧
          Flat (i ≫ hypersurfaceToBase q hq) ∧
          (∀ r, (i ≫ hypersurfaceToBase q hq).finrank r =
            (hypersurfaceToBase p hp).residueDegree x.1) ∧
          IsPullback j ((hypersurface p hp).fromSpecResidueField x.1)
            i (hypersurfaceReductionMap b q hq p hp he) :=
  exists_smooth_charZero_lift_with_closed_subscheme_fg_positive ℓ p hp hne x

/-- The literal lifting lemma in the perfect positive-characteristic case.
Here the required Cohen ring is the Witt ring, so all the data in the
statement is constructed without an additional existence hypothesis. -/
theorem twoProofs_chapterFive_lift_perfect_positive
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ]
    {p : MvPolynomial (Fin 4) k} (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp)) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (_ : CharZero R)
      (b : R →+* k), Function.Surjective b ∧
      ∃ q : MvPolynomial (Fin 4) R, ∃ hq : q.IsHomogeneous 3,
        ∃ he : q.map b = p, Smooth (hypersurfaceToBase q hq) ∧
        ∃ (Z : Scheme.{u}) (i : Z ⟶ hypersurface q hq)
          (j : Spec (.of ((hypersurface p hp).residueField x.1)) ⟶ Z),
          IsClosedImmersion i ∧ IsFinite (i ≫ hypersurfaceToBase q hq) ∧
          Flat (i ≫ hypersurfaceToBase q hq) ∧
          (∀ r, (i ≫ hypersurfaceToBase q hq).finrank r =
            (hypersurfaceToBase p hp).residueDegree x.1) ∧
          IsPullback j ((hypersurface p hp).fromSpecResidueField x.1)
            i (hypersurfaceReductionMap b q hq p hp he) :=
  twoProofs_chapterFive_lift_of_completeCharZeroDVR
    (hasCompleteCharZeroDVRLift_of_perfect_positive ℓ k) hp hne x

/-- The exact Chapter 5 lifting conclusion for every perfect field of the
given positive characteristic. -/
theorem chapterFiveLiftFor_perfect_positive
    {k : Type u} [Field k] (ℓ : ℕ) [_hprime₀ : Fact ℓ.Prime]
    [hchar₀ : CharP k ℓ] [PerfectRing k ℓ] :
    ChapterFiveLiftFor k := by
  intro ℓ' hprime hchar p hp hne hs x
  letI : Fact ℓ'.Prime := hprime
  letI : CharP k ℓ' := hchar
  have hℓ : ℓ' = ℓ := CharP.eq k hchar hchar₀
  subst ℓ'
  letI : Smooth (hypersurfaceToBase p hp) := hs
  exact twoProofs_chapterFive_lift_perfect_positive ℓ hp hne x

/-- The exact Chapter 5 lifting conclusion for every finitely generated
positive-characteristic field, with no perfectness condition. -/
theorem chapterFiveLiftFor_fg_positive
    {k : Type u} [Field k] (ℓ : ℕ) [_hprime₀ : Fact ℓ.Prime]
    [hchar₀ : CharP k ℓ] [Field.FG k] :
    ChapterFiveLiftFor k := by
  intro ℓ' hprime hchar p hp hne hs x
  letI : Fact ℓ'.Prime := hprime
  letI : CharP k ℓ' := hchar
  have hℓ : ℓ' = ℓ := CharP.eq k hchar hchar₀
  subst ℓ'
  letI : Smooth (hypersurfaceToBase p hp) := hs
  exact twoProofs_chapterFive_lift_fg_positive ℓ hp hne x

/-- The unrestricted Chapter 5 lifting lemma itself yields the corresponding
complete characteristic-zero DVR lift.  Thus the lifting statement is
equivalent to the Cohen-ring existence statement. -/
theorem hasCompleteCharZeroDVRLift_of_chapterFiveLiftFor
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (h : ChapterFiveLiftFor k) : HasCompleteCharZeroDVRLift k := by
  by_cases h3 : (3 : k) = 0
  · letI : Fact (3 : ℕ).Prime := ⟨by decide⟩
    letI : CharP k 3 :=
      (CharP.charP_iff_prime_eq_zero (by decide)).2 h3
    let q := characteristicThreeCubic k
    let hq := characteristicThreeCubic_isHomogeneous (k := k)
    let y : Fin 4 → k := fun i => if i = 3 then 1 else 0
    have hy : y ≠ 0 := by
      intro hy
      have hzero := congrFun hy (3 : Fin 4)
      simp [y] at hzero
    have hey : q.eval y = 0 := by
      simp [q, y, characteristicThreeCubic]
    have hsmooth : Smooth (hypersurfaceToBase q hq) := by
      exact smooth_characteristicThreeCubic
    obtain ⟨s, hsection⟩ := hypersurface_point_of_coordinates (RingHom.id k) q hq y hy hey
    obtain ⟨x, _⟩ := exists_closedPoint_degree_one_of_section
      (hypersurfaceToBase q hq) s (by simpa using hsection)
    obtain ⟨R, _, _, _, _, _, b, hb, _⟩ :=
      h 3 q hq characteristicThreeCubic_ne_zero hsmooth x
    exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, b, hb⟩
  · let q := fermatCubic k
    let hq := fermatCubic_isHomogeneous (k := k)
    let y : Fin 4 → k := fun i => if i = 0 then 1 else if i = 1 then -1 else 0
    have hy : y ≠ 0 := by
      intro hy
      have hzero := congrFun hy (0 : Fin 4)
      simp [y] at hzero
    have hey : q.eval y = 0 := by
      simp [q, y, fermatCubic]
      ring
    have hsmooth : Smooth (hypersurfaceToBase q hq) := by
      exact smooth_fermatCubic h3
    obtain ⟨s, hsection⟩ := hypersurface_point_of_coordinates (RingHom.id k) q hq y hy hey
    obtain ⟨x, _⟩ := exists_closedPoint_degree_one_of_section
      (hypersurfaceToBase q hq) s (by simpa using hsection)
    obtain ⟨R, _, _, _, _, _, b, hb, _⟩ := h ℓ q hq fermatCubic_ne_zero hsmooth x
    exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, b, hb⟩

/-- For a positive-characteristic field, the literal Chapter 5 lifting lemma
is equivalent to the existence of its complete characteristic-zero DVR lift:
the project has already formalized all of the geometric lifting work in the
forward direction from such a DVR. -/
theorem chapterFiveLiftFor_iff_hasCompleteCharZeroDVRLift
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] :
    ChapterFiveLiftFor k ↔ HasCompleteCharZeroDVRLift k :=
  ⟨hasCompleteCharZeroDVRLift_of_chapterFiveLiftFor ℓ,
    chapterFiveLiftFor_of_completeCharZeroDVR⟩

/-- Globally, the literal lifting lemma is equivalent to the Cohen-ring
statement.  The equivalence is proved in Lean, so it exposes the remaining
arbitrary-field construction without hiding any geometric argument. -/
theorem chapterFiveLiftStatement_iff_cohenRingStatement :
    ChapterFiveLiftStatement.{u} ↔ ChapterFiveCohenRingStatement.{u} := by
  constructor
  · intro h k _ ℓ _ _
    exact hasCompleteCharZeroDVRLift_of_chapterFiveLiftFor ℓ (h k ℓ)
  · intro h k _ ℓ _ _
    exact chapterFiveLiftFor_of_completeCharZeroDVR (h k ℓ)

/-- Arbitrary residue fields reduce to algebraic-extension closure. Starting
from the finite prime field, the development lifts an arbitrary
transcendence basis by the rational-function construction; the resulting
extension to the original field is algebraic. -/
theorem chapterFiveCohenRingStatement_of_algebraicExtensionClosure
    (hclosure : CompleteCharZeroDVRLiftAlgebraicExtensionClosure.{u}) :
    ChapterFiveCohenRingStatement.{u} := by
  intro k _ ℓ _ _
  let F := (⊥ : Subfield k)
  have hfinite : Finite F := primeSubfield_finite_positive ℓ k
  letI : Finite F := hfinite
  have hF : HasCompleteCharZeroDVRLift F :=
    hasCompleteCharZeroDVRLift_of_perfect_positive ℓ F
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F k
  let K := IntermediateField.adjoin F (Set.range (Subtype.val : s → k))
  have hKalg : Algebra.IsAlgebraic K k := hs.isAlgebraic_field
  have hK : HasCompleteCharZeroDVRLift K :=
    (hF.rationalFunction s).of_equiv hs.1.aevalEquivField.toRingEquiv
  exact hclosure hKalg hK

/-- Consequently, the single algebraic-extension closure principle proves
the unrestricted literal lifting lemma itself. -/
theorem chapterFiveLiftStatement_of_algebraicExtensionClosure
    (hclosure : CompleteCharZeroDVRLiftAlgebraicExtensionClosure.{u}) :
    ChapterFiveLiftStatement.{u} :=
  chapterFiveLiftStatement_iff_cohenRingStatement.mpr
    (chapterFiveCohenRingStatement_of_algebraicExtensionClosure hclosure)

/-- Complete characteristic-zero DVR lifts pass through arbitrary algebraic
residue-field extensions by the compatible transfinite tower construction. -/
theorem completeCharZeroDVRLiftAlgebraicExtensionClosure :
    CompleteCharZeroDVRLiftAlgebraicExtensionClosure.{u} := by
  intro K L _ _ _ hKL hK
  letI : Algebra.IsAlgebraic K L := hKL
  exact hK.algebraic_extension

/-- The unrestricted literal lifting lemma of Chapter 5. -/
theorem twoProofs_chapterFive_lift : ChapterFiveLiftStatement.{u} :=
  chapterFiveLiftStatement_of_algebraicExtensionClosure
    completeCharZeroDVRLiftAlgebraicExtensionClosure

/-- `thm:charzero` from Chapter 5. -/
theorem twoProofs_chapterFive_charzero_of_effectiveDegreeFour
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenEffectiveDegreeFourFor K)
    {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  cubic_section_of_zeroCycle_degree_one_of_voisin
    (fun K _ _ => voisinDegreeOneOrFourFor_of_coray_and_effectiveDegreeFour
      (coray K) (geometry K)) p hp z hz

/-- The specialization proof of `thm:smooth` once the complete DVR in
`lem:lift` has been constructed.  It lifts the degree-one cycle to the
characteristic-zero fraction field, applies `thm:charzero`, and specializes
the resulting homogeneous point. -/
theorem twoProofs_chapterFive_smooth_of_completeCharZeroDVR_of_effectiveDegreeFour
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenEffectiveDegreeFourFor K)
    {k : Type u} [Field k] (hR : HasCompleteCharZeroDVRLift k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨R, _, _, _, _, _, b, hb⟩ := hR
  let K := FractionRing R
  let g := algebraMap R K
  obtain ⟨q, hq, hred, _, hsK, w, hw⟩ :=
    exists_smooth_lift_with_zeroCycle b hb g p hp hne z
  letI : Smooth (hypersurfaceToBase (q.map g) (hq.map g)) := hsK
  obtain ⟨a, ha⟩ := twoProofs_chapterFive_charzero_of_effectiveDegreeFour coray geometry
    (q.map g) (hq.map g) w (hw.trans hz)
  obtain ⟨v, hv, heval⟩ := hypersurface_coordinates_of_point (RingHom.id K)
    (q.map g) (hq.map g) a (by simpa using ha)
  have hgeneric : q.eval₂ g v = 0 := by
    rw [MvPolynomial.eval₂_eq_eval_map]
    exact heval
  obtain ⟨y, hy, hey⟩ := specialize_homogeneous_polynomial q hq b v hv hgeneric
  have hpval : p.eval y = 0 := by
    rw [MvPolynomial.eval₂_eq_eval_map, hred] at hey
    exact hey
  obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp y hy hpval
  exact ⟨s, by simpa using hs⟩

/-- The selected-closed-point proof of Chapter 5's `thm:smooth`, after its
Cohen-ring base is supplied.  The finite flat lift of the selected point has
the same rank on the generic fiber; its fundamental cycle and the cubic
line-intersection cycle yield degree one, exactly as in the paper. -/
theorem twoProofs_chapterFive_smooth_of_coprime_closedPoint_and_completeCharZeroDVR_of_effectiveDegreeFour
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenEffectiveDegreeFourFor K)
    {k : Type u} [Field k] (hR : HasCompleteCharZeroDVRLift k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨R, _, _, _, _, _, b, hb⟩ := hR
  let K := FractionRing R
  let g := algebraMap R K
  obtain ⟨q, hq, hred, hs, Z, i, j, hclosed, hfinite, hflat, hrank, hpull⟩ :=
    exists_smooth_lift_with_closed_subscheme b hb p hp hne x
  letI : Smooth (hypersurfaceToBase q hq) := hs
  letI : IsClosedImmersion i := hclosed
  letI : IsFinite (i ≫ hypersurfaceToBase q hq) := hfinite
  letI : Flat (i ≫ hypersurfaceToBase q hq) := hflat
  let r : closedPoints (Spec (.of R)) :=
    ⟨IsLocalRing.closedPoint R, IsLocalRing.isClosed_singleton_closedPoint R⟩
  have hi : Nat.Coprime
      ((i ≫ hypersurfaceToBase q hq).finrank (IsLocalRing.closedPoint R)) 3 := by
    change Nat.Coprime ((i ≫ hypersurfaceToBase q hq).finrank r.1) 3
    rw [hrank r]
    exact hx
  obtain ⟨z, hz⟩ := cubic_finite_flat_fiber_exists_zeroCycle_degree_one q hq i hi g
  obtain ⟨w, hw⟩ := exists_zeroCycle_mapped_of_fiber_cycle q hq g z
  have hsK : Smooth (hypersurfaceToBase (q.map g) (hq.map g)) :=
    smooth_hypersurfaceToBase_map g q hq
  letI : Smooth (hypersurfaceToBase (q.map g) (hq.map g)) := hsK
  obtain ⟨a, ha⟩ := twoProofs_chapterFive_charzero_of_effectiveDegreeFour coray geometry
    (q.map g) (hq.map g) w (hw.trans hz)
  obtain ⟨v, hv, heval⟩ := hypersurface_coordinates_of_point (RingHom.id K)
    (q.map g) (hq.map g) a (by simpa using ha)
  have hgeneric : q.eval₂ g v = 0 := by
    rw [MvPolynomial.eval₂_eq_eval_map]
    exact heval
  obtain ⟨y, hy, hey⟩ := specialize_homogeneous_polynomial q hq b v hv hgeneric
  have hpval : p.eval y = 0 := by
    rw [MvPolynomial.eval₂_eq_eval_map, hred] at hey
    exact hey
  obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp y hy hpval
  exact ⟨s, by simpa using hs⟩

/-- The manuscript's proof of `thm:smooth` directly from `lem:lift`.  It
selects a prime-to-three closed point from the input cycle, invokes the
literal finite-flat lifting conclusion for that point, makes the generic
degree-one cycle by Bézout, and specializes the resulting generic point. -/
theorem twoProofs_chapterFive_smooth_of_lift_by_selected_closedPoint_of_effectiveDegreeFour
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenEffectiveDegreeFourFor K)
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (lift : ChapterFiveLiftFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (w : ZeroCycle (hypersurface p hp))
    (hw : ZeroCycle.degree (hypersurfaceToBase p hp) w = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  let f := hypersurfaceToBase p hp
  obtain ⟨x, _, hx⟩ := ZeroCycle.exists_coprime_degree f w hw
  obtain ⟨R, _, _, _, _, _, b, hb, q, hq, hred, hs, Z, i, j,
      hclosed, hfinite, hflat, hrank, hpull⟩ :=
    lift ℓ p hp hne inferInstance x
  let K := FractionRing R
  let g := algebraMap R K
  letI : Smooth (hypersurfaceToBase q hq) := hs
  letI : IsClosedImmersion i := hclosed
  letI : IsFinite (i ≫ hypersurfaceToBase q hq) := hfinite
  letI : Flat (i ≫ hypersurfaceToBase q hq) := hflat
  let r : closedPoints (Spec (.of R)) :=
    ⟨IsLocalRing.closedPoint R, IsLocalRing.isClosed_singleton_closedPoint R⟩
  have hi : Nat.Coprime
      ((i ≫ hypersurfaceToBase q hq).finrank (IsLocalRing.closedPoint R)) 3 := by
    change Nat.Coprime ((i ≫ hypersurfaceToBase q hq).finrank r.1) 3
    rw [hrank r]
    exact hx
  obtain ⟨z, hz⟩ := cubic_finite_flat_fiber_exists_zeroCycle_degree_one q hq i hi g
  obtain ⟨v, hv⟩ := exists_zeroCycle_mapped_of_fiber_cycle q hq g z
  have hsK : Smooth (hypersurfaceToBase (q.map g) (hq.map g)) :=
    smooth_hypersurfaceToBase_map g q hq
  letI : Smooth (hypersurfaceToBase (q.map g) (hq.map g)) := hsK
  obtain ⟨a, ha⟩ := twoProofs_chapterFive_charzero_of_effectiveDegreeFour coray geometry
    (q.map g) (hq.map g) v (hv.trans hz)
  obtain ⟨u, hu, heval⟩ := hypersurface_coordinates_of_point (RingHom.id K)
    (q.map g) (hq.map g) a (by simpa using ha)
  have hgeneric : q.eval₂ g u = 0 := by
    rw [MvPolynomial.eval₂_eq_eval_map]
    exact heval
  obtain ⟨y, hy, hey⟩ := specialize_homogeneous_polynomial q hq b u hu hgeneric
  have hpval : p.eval y = 0 := by
    rw [MvPolynomial.eval₂_eq_eval_map, hred] at hey
    exact hey
  obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp y hy hpval
  exact ⟨s, by simpa using hs⟩

/-- The literal Chapter 5 lifting lemma implies its smooth-surface theorem
in positive characteristic.  The preceding equivalence extracts the required
complete DVR from the lifting lemma, after which the checked specialization
argument applies. -/
theorem twoProofs_chapterFive_smooth_of_lift_of_effectiveDegreeFour
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenEffectiveDegreeFourFor K)
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (lift : ChapterFiveLiftFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  twoProofs_chapterFive_smooth_of_lift_by_selected_closedPoint_of_effectiveDegreeFour
    coray geometry ℓ lift p hp hne z hz

/-- `thm:smooth` from Chapter 5.  The all-characteristic proof uses the
internally proved Ma lifting theorem and specializes the characteristic-zero
input supplied by `coray` and `geometry`. -/
theorem twoProofs_chapterFive_smooth_of_effectiveDegreeFour
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenEffectiveDegreeFourFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  cubic_section_of_zeroCycle_degree_one_of_voisin
    (fun K _ _ => voisinDegreeOneOrFourFor_of_coray_and_effectiveDegreeFour
      (coray K) (geometry K)) p hp z hz

/-- The `lem:singular-point` alternative from Chapter 6, expressed by
homogeneous coordinates for the point over the finite extension. -/
theorem twoProofs_chapterSix_singular_point
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0) :
    (∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0) ∨
      ∃ q : Fin 4 → L,
        IsSmoothCubicCoordinatePoint (p.map (algebraMap k L)) q :=
  twoProofs_singular_point_or_smooth_extension_point p hp hdegree x hx heval

/-- Scheme-level literal form of `lem:singular-point`.  Starting with an
actual point of the base-changed cubic, it returns either a rational section
of the ground cubic or an actual point of the relative smooth locus over the
same finite extension. -/
theorem twoProofs_chapterSix_singular_point_scheme
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (a : Spec (.of L) ⟶ hypersurface (p.map (algebraMap k L))
      (hp.map (algebraMap k L)))
    (ha : a ≫ hypersurfaceToBase (p.map (algebraMap k L))
      (hp.map (algebraMap k L)) = 𝟙 _) :
    (∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
      ∃ q : Spec (.of L) ⟶ hypersurface (p.map (algebraMap k L))
        (hp.map (algebraMap k L)),
        q ≫ hypersurfaceToBase (p.map (algebraMap k L))
          (hp.map (algebraMap k L)) = 𝟙 _ ∧
        q (IsLocalRing.closedPoint L) ∈
          (hypersurfaceToBase (p.map (algebraMap k L))
            (hp.map (algebraMap k L))).smoothLocus := by
  let pL := p.map (algebraMap k L)
  let hpL := hp.map (algebraMap k L)
  obtain ⟨x, hx, heval⟩ := hypersurface_coordinates_of_point (RingHom.id L) pL hpL a (by
    simpa [pL, hpL] using ha)
  have heval' : p.eval₂ (algebraMap k L) x = 0 := by
    dsimp [pL] at heval
    rw [← MvPolynomial.eval₂_eq_eval_map] at heval
    exact heval
  obtain hground | ⟨q, hq⟩ :=
    twoProofs_chapterSix_singular_point p hp hdegree x hx heval'
  · left
    obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp hground.choose
      hground.choose_spec.1 hground.choose_spec.2
    exact ⟨s, by simpa using hs⟩
  · right
    obtain ⟨hq0, hqeval, hderiv⟩ := hq
    obtain ⟨s, hs, hsm⟩ := exists_hypersurface_point_mem_smoothLocus_of_pderiv
      pL hpL (RingHom.id L) q hq0 hqeval hderiv
    exact ⟨s, by simpa using hs, hsm⟩

/-- Coordinate form of the Chapter 6 smoothing proposition after a point of
degree prime to three has been selected from the zero-cycle. -/
theorem cubic_coordinates_of_finite_point_coprime_of_powerSeriesSmooth
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (smoothGeneric : SmoothCubicZeroCyclePointFor (FractionRing (PowerSeries k)))
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain hground | ⟨x', hx'⟩ :=
    cubic_point_or_smooth_extension_point p hp hdegree x hx heval
  · exact hground
  · obtain ⟨q, hq, hq0, hqs⟩ := smoothCubicReferenceFor k
    exact cubic_coordinates_of_smooth_extension_point_of_powerSeriesSmooth_ma
      smoothGeneric (maCubicPencilPointLiftingFor k)
      p q hp hq hq0 hqs x' hx' hdegree

/-- `prop:smoothing` from Chapter 6.  The hypothesis is precisely the
smooth-cubic degree-one criterion over `k((t))`, represented as the fraction
field of `k`-power series. -/
theorem twoProofs_chapterSix_smoothing
    {k : Type u} [Field k]
    (smoothGeneric : SmoothCubicZeroCyclePointFor (FractionRing (PowerSeries k)))
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  let f := hypersurfaceToBase p hp
  obtain ⟨x, _, hx⟩ := ZeroCycle.exists_coprime_degree f z hz
  letI : Algebra k ((hypersurface p hp).residueField x.1) := pointAlgebra f x.1
  letI : Module.Finite k ((hypersurface p hp).residueField x.1) :=
    closedPoint_moduleFinite f x
  obtain ⟨v, hv, he⟩ := hypersurface_residueField_coordinates p hp x.1
  have hdegree : Nat.Coprime
      (Module.finrank k ((hypersurface p hp).residueField x.1)) 3 := by
    rw [closedPoint_finrank_eq_residueDegree f x]
    exact hx
  obtain ⟨y, hy, hey⟩ := cubic_coordinates_of_finite_point_coprime_of_powerSeriesSmooth
    smoothGeneric p hp hdegree v hv he
  obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp y hy hey
  exact ⟨s, by simpa using hs⟩

/-- The final assembly in Chapter 6 from its stated smoothing proposition.
The first implication selects a degree-one closed point from a rational
section; the reverse implication first forms the degree-one zero-cycle used
by `prop:smoothing`. -/
theorem twoProofs_chapterSix_main_of_smoothing
    {k : Type u} [Field k]
    (smoothGeneric : SmoothCubicZeroCyclePointFor (FractionRing (PowerSeries k)))
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    ((∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ↔
      ∃ x : closedPoints (hypersurface p hp),
        Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ∧
    ((∃ x : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ↔
      ∃ z : ZeroCycle (hypersurface p hp),
        ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) := by
  constructor
  · constructor
    · rintro ⟨s, hs⟩
      obtain ⟨x, hx⟩ := exists_closedPoint_degree_one_of_section
        (hypersurfaceToBase p hp) s hs
      refine ⟨x, ?_⟩
      rw [hx]
      norm_num
    · rintro ⟨x, hx⟩
      obtain ⟨z, hz⟩ := twoProofs_zeroCycle_degree_one_of_closedPoint_coprime p hp x hx
      exact twoProofs_chapterSix_smoothing smoothGeneric p hp z hz
  · exact twoProofs_closedPoint_coprime_iff_zeroCycle_degree_one p hp

/-- The paper's final Chapter 6 route: apply `thm:smooth` from Chapter 5 to
the Laurent-series field in the hypothesis of `prop:smoothing`, then invoke
the preceding literal final assembly. -/
theorem twoProofs_chapterSix_main_via_chapterFive_of_effectiveDegreeFour
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenEffectiveDegreeFourFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    ((∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ↔
      ∃ x : closedPoints (hypersurface p hp),
        Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ∧
    ((∃ x : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ↔
      ∃ z : ZeroCycle (hypersurface p hp),
        ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) := by
  apply twoProofs_chapterSix_main_of_smoothing (p := p) (hp := hp)
  intro q hq hne hs z hz
  letI : Smooth (hypersurfaceToBase q hq) := hs
  exact twoProofs_chapterFive_smooth_of_effectiveDegreeFour coray geometry q hq z hz

/-- `thm:main` from Chapter 6, retaining both finite-cycle formulations
which the text calls equivalent. -/
theorem twoProofs_chapterSix_main_of_effectiveDegreeFour
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenEffectiveDegreeFourFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    ((∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ↔
      ∃ x : closedPoints (hypersurface p hp),
        Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ∧
    ((∃ x : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ↔
      ∃ z : ZeroCycle (hypersurface p hp),
        ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) := by
  exact twoProofs_chapterSix_main_via_chapterFive_of_effectiveDegreeFour coray geometry p hp

/-- Uses the internally proved actual native degree-four factory; only Coray remains external. -/
theorem twoProofs_chapterFive_charzero
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  twoProofs_chapterFive_charzero_of_effectiveDegreeFour coray
    (fun K _ _ => PfaffianDescent.voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory (K := K)) p hp z hz

/-- Uses the internally proved actual native degree-four factory; only Coray remains external. -/
theorem twoProofs_chapterFive_smooth_of_completeCharZeroDVR
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k : Type u} [Field k] (hR : HasCompleteCharZeroDVRLift k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  twoProofs_chapterFive_smooth_of_completeCharZeroDVR_of_effectiveDegreeFour coray
    (fun K _ _ => PfaffianDescent.voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory (K := K)) hR p hp hne z hz

/-- Uses the internally proved actual native degree-four factory; only Coray remains external. -/
theorem twoProofs_chapterFive_smooth_of_coprime_closedPoint_and_completeCharZeroDVR
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k : Type u} [Field k] (hR : HasCompleteCharZeroDVRLift k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  twoProofs_chapterFive_smooth_of_coprime_closedPoint_and_completeCharZeroDVR_of_effectiveDegreeFour coray
    (fun K _ _ => PfaffianDescent.voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory (K := K)) hR p hp hne x hx

/-- Uses the internally proved actual native degree-four factory; only Coray remains external. -/
theorem twoProofs_chapterFive_smooth_of_lift_by_selected_closedPoint
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (lift : ChapterFiveLiftFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (w : ZeroCycle (hypersurface p hp))
    (hw : ZeroCycle.degree (hypersurfaceToBase p hp) w = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  twoProofs_chapterFive_smooth_of_lift_by_selected_closedPoint_of_effectiveDegreeFour coray
    (fun K _ _ => PfaffianDescent.voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory (K := K)) ℓ lift p hp hne w hw

/-- Uses the internally proved actual native degree-four factory; only Coray remains external. -/
theorem twoProofs_chapterFive_smooth_of_lift
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (lift : ChapterFiveLiftFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  twoProofs_chapterFive_smooth_of_lift_of_effectiveDegreeFour coray
    (fun K _ _ => PfaffianDescent.voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory (K := K)) ℓ lift p hp hne z hz

/-- Uses the internally proved actual native degree-four factory; only Coray remains external. -/
theorem twoProofs_chapterFive_smooth
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  twoProofs_chapterFive_smooth_of_effectiveDegreeFour coray
    (fun K _ _ => PfaffianDescent.voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory (K := K)) p hp z hz

/-- Uses the internally proved actual native degree-four factory; only Coray remains external. -/
theorem twoProofs_chapterSix_main_via_chapterFive
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    ((∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ↔
      ∃ x : closedPoints (hypersurface p hp),
        Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ∧
    ((∃ x : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ↔
      ∃ z : ZeroCycle (hypersurface p hp),
        ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :=
  twoProofs_chapterSix_main_via_chapterFive_of_effectiveDegreeFour coray
    (fun K _ _ => PfaffianDescent.voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory (K := K)) p hp

/-- Uses the internally proved actual native degree-four factory; only Coray remains external. -/
theorem twoProofs_chapterSix_main
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    ((∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ↔
      ∃ x : closedPoints (hypersurface p hp),
        Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ∧
    ((∃ x : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ↔
      ∃ z : ZeroCycle (hypersurface p hp),
        ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :=
  twoProofs_chapterSix_main_of_effectiveDegreeFour coray
    (fun K _ _ => PfaffianDescent.voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory (K := K)) p hp

end AllCharacteristics
