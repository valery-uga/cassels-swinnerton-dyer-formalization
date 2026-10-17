import PfaffianDescent.FieldHyperplanes
import PfaffianDescent.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-! SOURCE ONLY / UNVERIFIED. Genuine perfect-field coordinate construction
for the original noncoplanar degree-five point. No characteristic-zero,
cubic-tensor, rational-map, residual-factor, or point-descent premise. This
preserves the original field, scalar, and matrix of the source construction.
-/
noncomputable section
namespace PfaffianDescent.Coray
open Module
open scoped BigOperators
universe u

private theorem perfect_quintic_power_basis
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : finrank K L = 5) :
    ∃ a : L, ∃ b : Basis (Fin 5) K L,
      (∀ i, b i = a ^ (i : ℕ)) ∧ (minpoly K a).natDegree = 5 := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  have he : pb.dim = 5 := pb.finrank.symm.trans hdim
  refine ⟨pb.gen, pb.basis.reindex (finCongr he), ?_, pb.natDegree_minpoly.trans he⟩
  intro i
  rw [Basis.reindex_apply, pb.basis_eq_pow]
  rfl

private theorem perfect_quintic_hyperplane_normal_form
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : finrank K L = 5)
    (W : Submodule K L) (hW : finrank K W = 4) :
    ∃ a : L, ∃ b : Basis (Fin 5) K L, (∀ i, b i = a ^ (i : ℕ)) ∧
      (minpoly K a).natDegree = 5 ∧ ∃ v : L, v ≠ 0 ∧
        Submodule.span K (Set.range (fun i : Fin 4 => v * a ^ (i : ℕ))) = W := by
  obtain ⟨a, b, hb, ha⟩ := perfect_quintic_power_basis hdim
  let q : Fin 4 → L := fun i => a ^ (i : ℕ)
  have hq : LinearIndependent K q := by
    have h := b.linearIndependent.comp Fin.castSucc (Fin.castSucc_injective 4)
    simpa only [Function.comp_def, hb, Fin.val_castSucc] using h
  let H := Submodule.span K (Set.range q)
  have hH : finrank K H = 4 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hq
  obtain ⟨v, hv, hmem⟩ := field_hyperplanes_multiplicative W H (by omega) (by omega)
  refine ⟨a, b, hb, ha, v, hv, ?_⟩
  let U := Submodule.span K (Set.range (fun i : Fin 4 => v * q i))
  have hle : U ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (hmem (q i)).mpr (Submodule.subset_span (Set.mem_range_self i))
  have hi : LinearIndependent K (fun i : Fin 4 => v * q i) := by
    exact hq.map' (LinearMap.mulLeft K v) (by
      rw [LinearMap.ker_eq_bot]
      intro x y h
      exact mul_left_cancel₀ hv h)
  have hU : finrank K U = 4 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hi
  exact Submodule.eq_of_le_of_finrank_eq hle (hU.trans hW.symm)

/-- Noncoplanar quintic coordinates over a PERFECT original ground field
construct a literal original-K invertible matrix, common nonzero scalar,
and primitive element of actual minimal-polynomial degree5. The coordinate
tuple is the actual power tuple, without a cubic-tensor representation. -/
theorem perfectField_independentQuinticCoordinates
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : finrank K L = 5)
    (p : Vec L 4) (hp : LinearIndependent K p) :
    ∃ a : L, (minpoly K a).natDegree = 5 ∧
      ∃ v : L, v ≠ 0 ∧ ∃ M : Mat K 4, Function.Injective M.mulVec ∧
        p = v • (M.map (algebraMap K L)).mulVec (fun i : Fin 4 => a ^ (i : ℕ)) := by
  let W := Submodule.span K (Set.range p)
  have hW : finrank K W = 4 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hp
  obtain ⟨a, b, hb, ha, v, hv, hspan⟩ := perfect_quintic_hyperplane_normal_form hdim W hW
  have hmem : ∀ i, p i ∈ Submodule.span K (Set.range (fun j : Fin 4 => v * a ^ (j : ℕ))) := by
    intro i
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  choose M hM using fun i => (Submodule.mem_span_range_iff_exists_fun K).mp (hmem i)
  let phi : Vec K 4 →ₗ[K] L :=
    { toFun := fun d => ∑ j : Fin 4, d j • (v * a ^ (j : ℕ))
      map_add' := by intro x y; simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro s x; simp only [Pi.smul_apply, smul_eq_mul, smul_smul,
        Finset.smul_sum, RingHom.id_apply] }
  have hcomp : phi ∘ M = p := funext hM
  have hrows : LinearIndependent K M := LinearIndependent.of_comp phi (by rw [hcomp]; exact hp)
  have hinj : Function.Injective (Matrix.mulVec (M : Mat K 4)) :=
    Matrix.mulVec_injective_iff.mpr (Matrix.Nonsingular.of_linearIndependent_row hrows).linearIndependent_col
  refine ⟨a, ha, v, hv, M, hinj, ?_⟩
  funext i
  rw [← hM i]
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum,
    Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro j _
  change algebraMap K L (M i j) * (v * a ^ (j : ℕ)) =
    v * (algebraMap K L (M i j) * a ^ (j : ℕ))
  ring

end PfaffianDescent.Coray
