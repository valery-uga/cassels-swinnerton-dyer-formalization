import PfaffianDescent.CorayPlaneHyperplaneRestriction
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! SOURCE ONLY / UNVERIFIED151. Literal split substitution has kernel the
literal homogeneous hyperplane relation. The congruence is constructed by
polynomial induction, with no supplied kernel/quotient comparison. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open scoped BigOperators
universe u
variable {R : Type u} [CommRing R]

/-- The literal linear relation defining this same plane. -/
def planeHyperplaneRelation (t : Fin 3 → R) : MvPolynomial (Fin 4) R :=
  X 0 + ∑ i : Fin 3, C (t i) * X i.succ

theorem planeHyperplaneRelation_homogeneous (t : Fin 3 → R) :
    (planeHyperplaneRelation t).IsHomogeneous 1 := by
  unfold planeHyperplaneRelation
  apply (isHomogeneous_X _ _).add
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

/-- Literal inclusion of the three retained plane variables. -/
def planeRetainedInclusionHom : MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 4) R :=
  MvPolynomial.aeval (fun i : Fin 3 => X i.succ)

@[simp] theorem planeRetainedInclusionHom_X (i : Fin 3) :
    planeRetainedInclusionHom (R := R) (X i) = X i.succ := by
  simp [planeRetainedInclusionHom]

theorem planeRetainedInclusionHom_homogeneous
    (q : MvPolynomial (Fin 3) R) {d : ℕ} (hq : q.IsHomogeneous d) :
    (planeRetainedInclusionHom q).IsHomogeneous d := by
  simpa only [planeRetainedInclusionHom, one_mul] using
    hq.aeval (fun i : Fin 3 => X i.succ) (fun i => isHomogeneous_X R i.succ)

/-- Restricting the literal retained inclusion is exactly identity. -/
theorem planeHyperplaneRestrictionHom_comp_inclusion (t : Fin 3 → R) :
    (planeHyperplaneRestrictionHom t).comp (planeRetainedInclusionHom (R := R)) =
      AlgHom.id R (MvPolynomial (Fin 3) R) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, planeRetainedInclusionHom_X, AlgHom.id_apply]
  exact planeHyperplaneRestrictionHom_X_succ t i

theorem planeHyperplaneRestrictionHom_surjective (t : Fin 3 → R) :
    Function.Surjective (planeHyperplaneRestrictionHom t) := by
  intro q
  exact ⟨planeRetainedInclusionHom q,
    AlgHom.congr_fun (planeHyperplaneRestrictionHom_comp_inclusion t) q⟩

/-- The SAME displayed linear relation vanishes under actual restriction. -/
theorem planeHyperplaneRestrictionHom_relation (t : Fin 3 → R) :
    planeHyperplaneRestrictionHom t (planeHyperplaneRelation t) = 0 := by
  have hC (a : R) : planeHyperplaneRestrictionHom t (C a) = C a :=
    (planeHyperplaneRestrictionHom t).commutes a
  simp only [planeHyperplaneRelation, map_add, map_sum, map_mul, hC]
  rw [planeHyperplaneRestrictionHom_X_zero]
  have hs : (∑ i : Fin 3, C (t i) * planeHyperplaneRestrictionHom t (X i.succ)) =
      ∑ i : Fin 3, C (t i) * X i := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun q : MvPolynomial (Fin 3) R => C (t i) * q)
      (planeHyperplaneRestrictionHom_X_succ t i)
  rw [hs, neg_add_cancel]

/-- Every coordinate differs from its retained/restricted lift by the actual
hyperplane ideal. Structural Fin cases precede simplification. -/
theorem planeRestriction_coordinate_difference_mem (t : Fin 3 → R) (j : Fin 4) :
    X j - planeRetainedInclusionHom (planeHyperplaneRestrictionHom t (X j)) ∈
      Ideal.span ({planeHyperplaneRelation t} : Set (MvPolynomial (Fin 4) R)) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · have heq : X 0 - planeRetainedInclusionHom
        (planeHyperplaneRestrictionHom t (X 0)) = planeHyperplaneRelation t := by
      rw [planeHyperplaneRestrictionHom_X_zero]
      have hC (a : R) : planeRetainedInclusionHom (R := R) (C a) = C a :=
        (planeRetainedInclusionHom (R := R)).commutes a
      simp only [map_neg, map_sum, map_mul, hC, planeRetainedInclusionHom_X,
        sub_neg_eq_add, planeHyperplaneRelation]
    rw [heq]
    exact Ideal.subset_span (Set.mem_singleton _)
  · rw [planeHyperplaneRestrictionHom_X_succ, planeRetainedInclusionHom_X, sub_self]
    exact Ideal.zero_mem _

/-- The exact polynomial congruence constructs the entire substitution
kernel, rather than only its value on the cubic or on the variables. -/
theorem planeRestriction_polynomial_difference_mem
    (t : Fin 3 → R) (q : MvPolynomial (Fin 4) R) :
    q - planeRetainedInclusionHom (planeHyperplaneRestrictionHom t q) ∈
      Ideal.span ({planeHyperplaneRelation t} : Set (MvPolynomial (Fin 4) R)) := by
  classical
  let I : Ideal (MvPolynomial (Fin 4) R) := Ideal.span {planeHyperplaneRelation t}
  induction q using MvPolynomial.induction_on with
  | C a => simp [planeHyperplaneRestrictionHom, planeRetainedInclusionHom]
  | add q r hq hr =>
      have heq : q + r - planeRetainedInclusionHom (planeHyperplaneRestrictionHom t (q + r)) =
          (q - planeRetainedInclusionHom (planeHyperplaneRestrictionHom t q)) +
            (r - planeRetainedInclusionHom (planeHyperplaneRestrictionHom t r)) := by
        simp only [map_add]
        ring
      rw [heq]
      exact I.add_mem hq hr
  | mul_X q j hq =>
      have hx := planeRestriction_coordinate_difference_mem t j
      have heq : q * X j - planeRetainedInclusionHom (planeHyperplaneRestrictionHom t (q * X j)) =
          (q - planeRetainedInclusionHom (planeHyperplaneRestrictionHom t q)) * X j +
          planeRetainedInclusionHom (planeHyperplaneRestrictionHom t q) *
            (X j - planeRetainedInclusionHom (planeHyperplaneRestrictionHom t (X j))) := by
        simp only [map_mul]
        ring
      rw [heq]
      exact I.add_mem (I.mul_mem_right (X j) hq)
        (I.mul_mem_left (planeRetainedInclusionHom (planeHyperplaneRestrictionHom t q)) hx)

/-- The actual split substitution kernel is EXACTLY the SAME linear ideal. -/
theorem planeHyperplaneRestrictionHom_ker (t : Fin 3 → R) :
    RingHom.ker (planeHyperplaneRestrictionHom t).toRingHom =
      Ideal.span ({planeHyperplaneRelation t} : Set (MvPolynomial (Fin 4) R)) := by
  apply le_antisymm
  · intro q hq
    have hdiff := planeRestriction_polynomial_difference_mem t q
    change planeHyperplaneRestrictionHom t q = 0 at hq
    simpa only [hq, map_zero, sub_zero] using hdiff
  · apply Ideal.span_le.mpr
    rintro q hq
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact planeHyperplaneRestrictionHom_relation t

end PfaffianDescent.Coray
