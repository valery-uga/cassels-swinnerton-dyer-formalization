import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.Algebraic.Integral

/-! SOURCE ONLY / UNVERIFIED148. Algebraic foundation for genuine generic
hyperplane transversality. No smooth section, Hilbert lower bound, genus,
Euler identity, or constants-field identification is a premise or conclusion.
The public field-of-coordinates obstruction constructs its algebraicity
internally from actual rational expressions. Root owns all compiler checks. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
universe u v w

section RationalGenerators
variable {K : Type u} {A : Type v} {ι : Type w}
variable [Field K] [Field A] [Algebra K A]

/-- A field consisting of rational expressions in x is algebraic over the
literal polynomial subalgebra K[x]. This uses the actual numerator and
inverse-denominator algebraic witnesses, rather than a dimension premise. -/
theorem rationallyGeneratedField_algebraIsAlgebraic
    (x : ι → A)
    (hgen : ∀ a : A, ∃ p q : MvPolynomial ι K,
      a = MvPolynomial.aeval x p / MvPolynomial.aeval x q) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) A := by
  let B := Algebra.adjoin K (Set.range x)
  have heval (p : MvPolynomial ι K) : MvPolynomial.aeval x p ∈ B := by
    change MvPolynomial.aeval x p ∈ Algebra.adjoin K (Set.range x)
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨p, rfl⟩
  refine ⟨fun a => ?_⟩
  obtain ⟨p, q, rfl⟩ := hgen a
  have hp : IsAlgebraic B (MvPolynomial.aeval x p) :=
    isAlgebraic_algebraMap (⟨MvPolynomial.aeval x p, heval p⟩ : B)
  have hq : IsAlgebraic B (MvPolynomial.aeval x q) :=
    isAlgebraic_algebraMap (⟨MvPolynomial.aeval x q, heval q⟩ : B)
  simpa only [div_eq_mul_inv] using hp.mul hq.inv

/-- In a field algebraic over n polynomial generators, n independent
parameters force those same generators to be independent. The finite
cardinal argument uses the native transcendence-basis theorem. -/
theorem algebraicGenerators_independent_of_independentParameters
    [Finite ι] (x t : ι → A)
    [Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) A]
    (ht : AlgebraicIndependent K t) : AlgebraicIndependent K x := by
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite
    K x ht.lift_cardinalMk_le_trdeg).1

end RationalGenerators

section ActualCoordinateField
variable {K : Type u} {M : Type v} {ι : Type w}
variable [Field K] [Field M] [Algebra K M]

/-- The actual coordinate tuple inside its field of rational functions. -/
def coordinateFieldTuple (x : ι → M) :
    ι → IntermediateField.adjoin K (Set.range x) :=
  fun i => ⟨x i, IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩

/-- Every element of the actual field K(x) has an actual numerator and
actual denominator in the native tuple, with all subtype maps preserved. -/
theorem coordinateFieldTuple_rationallyGenerates (x : ι → M) :
    ∀ a : IntermediateField.adjoin K (Set.range x),
      ∃ p q : MvPolynomial ι K,
        a = MvPolynomial.aeval (coordinateFieldTuple x) p /
          MvPolynomial.aeval (coordinateFieldTuple x) q := by
  intro a
  obtain ⟨p, q, hpq⟩ :=
    (IntermediateField.mem_adjoin_range_iff K x a.1).mp a.2
  refine ⟨p, q, ?_⟩
  apply Subtype.ext
  change a.1 =
    ((MvPolynomial.aeval (coordinateFieldTuple x) p :
      IntermediateField.adjoin K (Set.range x)) : M) /
    ((MvPolynomial.aeval (coordinateFieldTuple x) q :
      IntermediateField.adjoin K (Set.range x)) : M)
  have hp :
      (IntermediateField.adjoin K (Set.range x)).val
        (MvPolynomial.aeval (coordinateFieldTuple x) p) = MvPolynomial.aeval x p :=
    MvPolynomial.comp_aeval_apply (coordinateFieldTuple x) (IntermediateField.adjoin K (Set.range x)).val p
  have hq :
      (IntermediateField.adjoin K (Set.range x)).val
        (MvPolynomial.aeval (coordinateFieldTuple x) q) = MvPolynomial.aeval x q :=
    MvPolynomial.comp_aeval_apply (coordinateFieldTuple x) (IntermediateField.adjoin K (Set.range x)).val q
  exact hpq.trans (congrArg₂ (fun a b : M => a / b) hp.symm hq.symm)

/-- A genuinely dependent n-tuple cannot have n independent parameters
inside its actual field K(x). Algebraicity of that field is constructed
here; the final caller supplies only the literal polynomial relation and
membership of the literal parameters. -/
theorem independentParameters_not_all_mem_dependentCoordinateField
    [Finite ι] (x t : ι → M)
    (P : MvPolynomial ι K) (hP : P ≠ 0)
    (hPx : MvPolynomial.aeval x P = 0)
    (ht : AlgebraicIndependent K t) :
    ¬ ∀ i, t i ∈ IntermediateField.adjoin K (Set.range x) := by
  intro hmem
  let A := IntermediateField.adjoin K (Set.range x)
  let xA : ι → A := coordinateFieldTuple x
  let tA : ι → A := fun i => ⟨t i, hmem i⟩
  letI : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range xA)) A :=
    rationallyGeneratedField_algebraIsAlgebraic xA
      (coordinateFieldTuple_rationallyGenerates x)
  have htA : AlgebraicIndependent K tA := by
    apply AlgebraicIndependent.of_comp A.val
    change AlgebraicIndependent K t
    exact ht
  have hxA : AlgebraicIndependent K xA :=
    algebraicGenerators_independent_of_independentParameters xA tA htA
  have hPzero : MvPolynomial.aeval xA P = 0 := by
    apply Subtype.ext
    change A.val (MvPolynomial.aeval xA P) = 0
    have he : A.val (MvPolynomial.aeval xA P) = MvPolynomial.aeval x P :=
      MvPolynomial.comp_aeval_apply xA A.val P
    exact he.trans hPx
  exact hP (hxA.eq_zero_of_aeval_eq_zero P hPzero)

end ActualCoordinateField
end PfaffianDescent.Coray
