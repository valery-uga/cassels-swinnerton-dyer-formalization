import PfaffianDescent.QuadraticSecant
import PfaffianDescent.QuadraticConjugateDescent
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Basis.Prod

/-! SOURCE ONLY / UNVERIFIED. Descend the actual span of x and sigma(x)
using the basis 1,alpha, including characteristic two. No descended-space,
ground-frame, or linear-independence certificate is supplied by the caller. -/
noncomputable section
namespace PfaffianDescent
open Module
open scoped BigOperators
universe u
variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- Complementary exchanged projectors force the chosen vector and its
conjugate to be independent. This is the vector form of skewness, derived
from the literal line equations in the geometric caller. -/
theorem exchangedProjector_conjugate_vector_independent
    (P : Matrix (Fin 4) (Fin 4) E) (sigma : E ≃ₐ[k] E)
    (hExchange : P.map sigma.toRingHom = 1 - P)
    (x : Fin 4 → E) (hx : x ≠ 0) (hPx : P.mulVec x = x) :
    LinearIndependent E ![x, fun m => sigma (x m)] := by
  let y := fun m => sigma (x m)
  have hy : y ≠ 0 := by
    intro hy
    apply hx
    funext m
    apply sigma.injective
    exact (congrFun hy m).trans (map_zero sigma).symm
  have hPy : P.mulVec y = 0 := by
    have h := congrArg (fun z : Fin 4 → E => fun m => sigma (z m)) hPx
    have hMap : (P.map sigma.toRingHom).mulVec y = y := by
      funext m
      exact (RingHom.map_mulVec sigma.toRingHom P x m).symm.trans (congrFun h m)
    rw [hExchange, Matrix.sub_mulVec, Matrix.one_mulVec] at hMap
    exact (sub_eq_self.mp hMap)
  apply linearIndependent_fin2.mpr
  refine ⟨hy, ?_⟩
  intro c hc
  change c • y = x at hc
  have h := congrArg P.mulVec hc
  rw [Matrix.mulVec_smul, hPy, smul_zero, hPx] at h
  exact hx h.symm

/-- Extend an independent ground pair to a Fin4 frame without changing either
of its first two vectors. The complement is chosen internally. -/
theorem independentGroundPair_extends_frame
    (u v : Fin 4 → k) (hLI : LinearIndependent k ![u, v]) :
    ∃ C : Basis (Fin 4) k (Fin 4 → k), C 0 = u ∧ C 1 = v := by
  classical
  let V := Submodule.span k (Set.range ![u, v])
  let b : Basis (Fin 2) k V := Basis.span hLI
  have hV : finrank k V = 2 := by
    simpa only [Fintype.card_fin] using (finrank_span_eq_card hLI)
  obtain ⟨W, hW⟩ := V.exists_isCompl
  have hDim := Submodule.finrank_add_eq_of_isCompl hW
  have hWD : finrank k W = 2 := by
    rw [hV, Module.finrank_pi, Fintype.card_fin] at hDim
    omega
  let c := Module.finBasisOfFinrankEq k W hWD
  let C : Basis (Fin 4) k (Fin 4 → k) :=
    ((b.prod c).map (Submodule.prodEquivOfIsCompl V W hW)).reindex finSumFinEquiv
  have hleft (i : Fin 2) : C (Fin.castAdd 2 i) = ![u, v] i := by
    dsimp only [C]
    rw [Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd (n := 2) i]
    simp [Basis.map_apply, Basis.prod_apply, b,
      Submodule.coe_prodEquivOfIsCompl']
    exact Basis.coe_span_apply hLI i
  exact ⟨C, hleft 0, hleft 1⟩

/-- The SAME chosen coordinate vector has a ground pair decomposition, and
that pair spans exactly its two-conjugate E-space. Both ground vectors remain
literal first columns of the resulting ground frame. -/
theorem quadraticConjugateVector_groundFrame [FiniteDimensional k E]
    (hdeg : finrank k E = 2) (sigma : E ≃ₐ[k] E) (hNe : sigma ≠ 1)
    (x : Fin 4 → E)
    (hLI : LinearIndependent E ![x, fun m => sigma (x m)]) :
    ∃ alpha : E, alpha ≠ sigma alpha ∧
      ∃ u v : Fin 4 → k,
        x = (fun m => algebraMap k E (u m)) + alpha • (fun m => algebraMap k E (v m)) ∧
        LinearIndependent k ![u, v] ∧
        LinearIndependent E ![(fun m => algebraMap k E (u m)),
          (fun m => algebraMap k E (v m))] ∧
        Submodule.span E (Set.range ![x, fun m => sigma (x m)]) =
          Submodule.span E (Set.range ![(fun m => algebraMap k E (u m)),
            (fun m => algebraMap k E (v m))]) ∧
        ∃ C : Basis (Fin 4) k (Fin 4 → k), C 0 = u ∧ C 1 = v := by
  classical
  obtain ⟨alpha, hspan, hind⟩ := quadratic_generator hdeg
  have hAlpha : alpha ≠ sigma alpha := by
    intro h
    apply hNe
    ext z
    obtain ⟨a, b, rfl⟩ := hspan z
    simp only [map_add, map_mul, sigma.commutes, ← h, AlgEquiv.one_apply]
  choose u v huv using fun m => hspan (x m)
  let U := fun m => algebraMap k E (u m)
  let V := fun m => algebraMap k E (v m)
  let y := fun m => sigma (x m)
  have hx : x = U + alpha • V := by
    funext m
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using huv m
  have hy : y = U + sigma alpha • V := by
    funext m
    dsimp only [y]
    rw [huv m, map_add, map_mul, sigma.commutes, sigma.commutes]
    simp only [U, V, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hUV : LinearIndependent E ![U, V] := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hc' : c 0 • U + c 1 • V = 0 := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using hc
    let r := -sigma alpha * c 0 + c 1
    let s := alpha * c 0 - c 1
    have hxy : r • x + s • y = 0 := by
      funext m
      have hm := congrFun hc' m
      rw [hx, hy]
      change r * (U m + alpha * V m) + s * (U m + sigma alpha * V m) = 0
      dsimp only [r, s]
      change c 0 * U m + c 1 * V m = 0 at hm
      linear_combination (alpha - sigma alpha) * hm
    have hsums : ∑ j : Fin 2, ![r, s] j • ![x, y] j = 0 := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using hxy
    have hzero := Fintype.linearIndependent_iff.mp hLI ![r, s] hsums
    have hr : r = 0 := hzero 0
    have hs : s = 0 := hzero 1
    have hc0 : c 0 = 0 := by
      apply (mul_eq_zero.mp (show (alpha - sigma alpha) * c 0 = 0 by
        dsimp only [r, s] at hr hs
        linear_combination hr + hs)).resolve_left (sub_ne_zero.mpr hAlpha)
    have hc1 : c 1 = 0 := by
      dsimp only [s] at hs
      simpa only [hc0, mul_zero, zero_sub, neg_eq_zero] using hs
    fin_cases i
    · exact hc0
    · exact hc1
  have hGround : LinearIndependent k ![u, v] := by
    apply (linearIndependent_algebraMap_comp_iff (R := k) (S := E)).mp
    have hFamily : (fun i m => algebraMap k E (![u, v] i m)) = ![U, V] := by
      funext i
      fin_cases i <;> rfl
    change LinearIndependent E (fun i m => algebraMap k E (![u, v] i m))
    rw [hFamily]
    exact hUV
  let W := Submodule.span E (Set.range ![U, V])
  let S := Submodule.span E (Set.range ![x, y])
  have hUx : U ∈ W := Submodule.subset_span ⟨0, rfl⟩
  have hVx : V ∈ W := Submodule.subset_span ⟨1, rfl⟩
  have hxs : x ∈ S := Submodule.subset_span ⟨0, rfl⟩
  have hys : y ∈ S := Submodule.subset_span ⟨1, rfl⟩
  have hSpan : S = W := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro z ⟨i, rfl⟩
      fin_cases i
      · rw [hx]
        exact W.add_mem hUx (W.smul_mem alpha hVx)
      · rw [hy]
        exact W.add_mem hUx (W.smul_mem (sigma alpha) hVx)
    · have hVS : V ∈ S := by
        have he : (alpha - sigma alpha)⁻¹ • (x - y) = V := by
          funext m
          rw [hx, hy]
          change (alpha - sigma alpha)⁻¹ *
            ((U m + alpha * V m) - (U m + sigma alpha * V m)) = V m
          field_simp [sub_ne_zero.mpr hAlpha]
          ring
        rw [← he]
        exact S.smul_mem _ (S.sub_mem hxs hys)
      have hUS : U ∈ S := by
        have he : U = x - alpha • V := by rw [hx]; abel
        rw [he]
        exact S.sub_mem hxs (S.smul_mem alpha hVS)
      apply Submodule.span_le.mpr
      rintro z ⟨i, rfl⟩
      fin_cases i
      · exact hUS
      · exact hVS
  obtain ⟨C, hC0, hC1⟩ := independentGroundPair_extends_frame u v hGround
  exact ⟨alpha, hAlpha, u, v, hx, hGround, hUV, hSpan, C, hC0, hC1⟩

end PfaffianDescent
