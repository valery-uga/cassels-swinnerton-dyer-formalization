import PfaffianDescent.IntrinsicFiniteProjectiveQuadraticDimension

/-! A ground basis of the FULL intrinsic quadratic series generates its
WHOLE homogeneous base ideal. The basis is selected over the original
arbitrary field, after dimension three has been derived internally. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ideal_span_three_basis_eq_full_submodule
    (W : Submodule k (MvPolynomial (Fin 4) k)) (b : Basis (Fin 3) k W) :
    Ideal.span (Set.range (fun j : Fin 3 => (b j).val)) =
      Ideal.span (W : Set (MvPolynomial (Fin 4) k)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨j, rfl⟩
    exact Ideal.subset_span (b j).property
  · apply Ideal.span_le.mpr
    intro p hp
    let w : W := ⟨p, hp⟩
    have hpoly : p = ∑ j : Fin 3, C (b.repr w j) * (b j).val := by
      have h := congrArg W.subtype (b.sum_repr w)
      simpa only [map_sum, map_smul, MvPolynomial.smul_eq_C_mul,
        Submodule.subtype_apply, w] using h.symm
    rw [hpoly]
    apply Submodule.sum_mem
    intro j hj
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem range_fin_three_eq_triple {A : Type*} (q : Fin 3 → A) :
    Set.range q = {q 0, q 1, q 2} := by
  ext a
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp
  · intro ha
    rcases ha with h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩

/-- ANY ground basis of the actual full intrinsic series defines precisely
the full base scheme ideal, including nilpotents. -/
theorem intrinsicFullQuadraticTripleIdeal_eq_fullBase_of_basis
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    (b : Basis (Fin 3) k (intrinsicFullQuadraticSystem i)) :
    intrinsicFullQuadraticTripleIdeal i b = intrinsicFullQuadraticBaseIdeal i := by
  apply HomogeneousIdeal.ext
  unfold intrinsicFullQuadraticTripleIdeal
  rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
  change Ideal.span ({(b 0).val, (b 1).val, (b 2).val} : Set _) =
    Ideal.span (intrinsicFullQuadraticSystem i : Set _)
  rw [← range_fin_three_eq_triple (fun j : Fin 3 => (b j).val)]
  exact ideal_span_three_basis_eq_full_submodule (intrinsicFullQuadraticSystem i) b

def intrinsicGroundQuadraticBasis
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)]
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ ambientToBase) = 8)
    [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i))] :
    Basis (Fin 3) k (intrinsicFullQuadraticSystem i) := by
  letI : Module.Free k (intrinsicFullQuadraticSystem i) :=
    Module.Free.of_divisionRing k (intrinsicFullQuadraticSystem i)
  exact Module.finBasisOfFinrankEq k (intrinsicFullQuadraticSystem i)
    (intrinsicFullQuadraticSystem_finrank_three_of_finite_base_any_field i hZ)

theorem intrinsicGroundQuadraticBasis_triple_eq_fullBase
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)]
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ ambientToBase) = 8)
    [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i))] :
    intrinsicFullQuadraticTripleIdeal i (intrinsicGroundQuadraticBasis i hZ) =
      intrinsicFullQuadraticBaseIdeal i :=
  intrinsicFullQuadraticTripleIdeal_eq_fullBase_of_basis i (intrinsicGroundQuadraticBasis i hZ)

theorem intrinsicGroundQuadraticBasis_triple_isFinite
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)]
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ ambientToBase) = 8)
    [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i))] :
    IsFinite (toBase (intrinsicFullQuadraticTripleIdeal i (intrinsicGroundQuadraticBasis i hZ))) := by
  rw [intrinsicGroundQuadraticBasis_triple_eq_fullBase]
  infer_instance

end PfaffianDescent
