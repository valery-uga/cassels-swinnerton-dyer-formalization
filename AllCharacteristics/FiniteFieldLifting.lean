import AllCharacteristics.SimpleFieldLifting
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Lifting arbitrary finite residue-field extensions

Finite extensions are built by adjoining finitely many elements. Each simple
step has an actual finite free complete local lift; composing the steps
preserves freeness, completeness, the residue map, and the full extension
degree. No primitive-element or separability assumption is made.
-/

open IsLocalRing IntermediateField
namespace AllCharacteristics
universe u v w w'

/-- Existence of an actual complete local finite free lift, with its prescribed
residue map, coefficient compatibility, exact rank, and extended maximal ideal. -/
def HasCompleteLocalLift
    {R : Type u} {k : Type v} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (L : Type w) [Field L] [Algebra k L] : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : IsLocalRing A)
    (_ : Module.Free R A) (_ : Module.Finite R A)
    (_ : IsAdicComplete (maximalIdeal A) A) (c : A →+* L),
    Function.Surjective c ∧
    (∀ r : R, c (algebraMap R A r) = algebraMap k L (b r)) ∧
    Module.finrank R A = Module.finrank k L ∧
    maximalIdeal A = (maximalIdeal R).map (algebraMap R A)

/-- The coefficient ring lifts its own presented residue field. -/
theorem hasCompleteLocalLift_self
    {R : Type u} {k : Type v} [CommRing R] [IsLocalRing R] [Field k]
    [IsAdicComplete (maximalIdeal R) R]
    (b : R →+* k) (hb : Function.Surjective b) : HasCompleteLocalLift b k := by
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, b, hb, ?_, ?_, ?_⟩
  · intro r
    rfl
  · rw [Module.finrank_self, Module.finrank_self]
  · simp

/-- An isomorphism of residue extensions transports a lift without changing
its coefficient algebra or rank. -/
theorem HasCompleteLocalLift.of_algEquiv
    {R : Type u} {k : Type v} {L : Type w} {L' : Type w'}
    [CommRing R] [IsLocalRing R] [Field k] [Field L] [Field L']
    [Algebra k L] [Algebra k L'] {b : R →+* k}
    (h : HasCompleteLocalLift b L) (e : L ≃ₐ[k] L') : HasCompleteLocalLift b L' := by
  obtain ⟨A, _, _, _, _, _, _, c, hc, hcomm, hrank, hmax⟩ := h
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, e.toRingEquiv.toRingHom.comp c, e.surjective.comp hc, ?_,
    hrank.trans e.toLinearEquiv.finrank_eq, hmax⟩
  intro r
  change e (c (algebraMap R A r)) = _
  rw [hcomm]
  exact e.commutes (b r)

/-- A simple extension of an already lifted residue field lifts by composing
the two finite free coefficient algebras. -/
theorem HasCompleteLocalLift.of_powerBasis_tower
    {R : Type u} {k : Type v} {K : Type w} {L : Type w'}
    [CommRing R] [IsLocalRing R] [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    {b : R →+* k} (h : HasCompleteLocalLift b K) (pb : PowerBasis K L) :
    HasCompleteLocalLift b L := by
  obtain ⟨A, _, _, _, _, _, _, c, hc, hcomm, hrank, hmax⟩ := h
  obtain ⟨B, _, _, _, _, _, _, d, hd, hdcomm, hdrank, hdmax⟩ :=
    exists_complete_local_lift_of_powerBasis c hc pb
  let : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Free R B := Module.Free.trans (R := R) (S := A) (M := B)
  let : Module.Finite R B := Module.Finite.trans A B
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, d, hd, ?_, ?_, ?_⟩
  · intro r
    change d (algebraMap A B (algebraMap R A r)) = _
    rw [hdcomm, hcomm]
    exact (IsScalarTower.algebraMap_apply k K L (b r)).symm
  · rw [← Module.finrank_mul_finrank R A B, hrank, hdrank]
    exact Module.finrank_mul_finrank k K L
  · rw [hdmax, hmax, Ideal.map_map]
    rfl

/-- Every finite extension of the residue field of a complete local ring has
an actual complete local finite free lift of exactly the same degree. -/
theorem hasCompleteLocalLift_of_finite_extension
    {R : Type u} {k : Type v} {L : Type w}
    [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (b : R →+* k) (hb : Function.Surjective b) : HasCompleteLocalLift b L := by
  have h : ∀ K : IntermediateField k L, HasCompleteLocalLift b K := by
    apply IntermediateField.induction_on_adjoin
    · exact (hasCompleteLocalLift_self b hb).of_algEquiv (IntermediateField.botEquiv k L).symm
    · intro K x hK
      have ht : HasCompleteLocalLift b K⟮x⟯ := hK.of_powerBasis_tower
        (IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (R := K) x))
      exact ht
  exact (h ⊤).of_algEquiv (IntermediateField.topEquiv : (⊤ : IntermediateField k L) ≃ₐ[k] L)

end AllCharacteristics
