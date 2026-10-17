import PfaffianDescent.VoisinP3SerreResiduePairing
import Mathlib.GroupTheory.Perm.Sign

/-!
# Detection of top Cech cocycles by the identity chart tuple

For the four-chart cover, a full-support degree-three Cech cocycle is
determined by its value on the identity ordered tuple.  Adjacent
transpositions change that value by a sign; for detection it suffices that
zero remains zero.  Since adjacent transpositions generate `Perm (Fin 4)`,
vanishing at the identity forces vanishing on every surjective tuple, while
the support condition kills every nonsurjective tuple.
-/

noncomputable section

namespace PfaffianDescent
namespace LaurentCechCore

universe u

variable {A : Type u} [AddCommGroup A]

/-- Tuple-indexed degree-three Cech differential. -/
def tupleD3 (w : (Fin 4 → Vertex) → A)
    (f : Fin 5 → Vertex) : A :=
  w ![f 1, f 2, f 3, f 4] - w ![f 0, f 2, f 3, f 4] +
    w ![f 0, f 1, f 3, f 4] - w ![f 0, f 1, f 2, f 4] +
      w ![f 0, f 1, f 2, f 3]

/-- Degree-three cochains supported on ordered quadruples containing `N`. -/
def Supported3 (N : Set Vertex)
    (w : Vertex → Vertex → Vertex → Vertex → A) : Prop :=
  ∀ a b c d, ¬ N ⊆ ({a, b, c, d} : Set Vertex) → w a b c d = 0

/-- The Cech differential from degree three to degree four. -/
def d3 (w : Vertex → Vertex → Vertex → Vertex → A)
    (a b c d e : Vertex) : A :=
  w b c d e - w a c d e + w a b d e - w a b c e + w a b c d

/-- A missing vertex contracts a supported degree-three cocycle. -/
theorem exact_three_of_missing_vertex
    (N : Set Vertex) (p : Vertex) (hp : p ∉ N)
    (w : Vertex → Vertex → Vertex → Vertex → A)
    (hw : Supported3 N w)
    (hdw : ∀ a b c d e, d3 w a b c d e = 0) :
    ∃ z : Vertex → Vertex → Vertex → A, Supported2 N z ∧
      ∀ a b c d, d2 z a b c d = w a b c d := by
  let z : Vertex → Vertex → Vertex → A := fun a b c => w p a b c
  refine ⟨z, ?_, ?_⟩
  · intro a b c habc
    exact hw p a b c (not_subset_insert_of_not_mem hp habc)
  · intro a b c d
    have h := hdw p a b c d
    dsimp [d2, d3, z] at h ⊢
    rw [← sub_eq_zero]
    have hn := congrArg Neg.neg h
    abel_nf at hn ⊢
    exact hn

/-- Every degree-three cocycle with proper negative support is a boundary. -/
theorem exact_three_of_ne_univ
    (N : Set Vertex) (hN : N ≠ Set.univ)
    (w : Vertex → Vertex → Vertex → Vertex → A)
    (hw : Supported3 N w)
    (hdw : ∀ a b c d e, d3 w a b c d e = 0) :
    ∃ z : Vertex → Vertex → Vertex → A, Supported2 N z ∧
      ∀ a b c d, d2 z a b c d = w a b c d := by
  obtain ⟨p, hp⟩ := exists_missing_vertex hN
  exact exact_three_of_missing_vertex N p hp w hw hdw

/-- Tuple-indexed form of top-degree exactness for proper support. -/
theorem tuple_exact_three_of_ne_univ
    (N : Set Vertex) (hN : N ≠ Set.univ)
    (w : (Fin 4 → Vertex) → A) (hw : TupleSupported N w)
    (hdw : ∀ f, tupleD3 w f = 0) :
    ∃ z : (Fin 3 → Vertex) → A, TupleSupported N z ∧
      ∀ f, tupleD2 z f = w f := by
  let w' : Vertex → Vertex → Vertex → Vertex → A :=
    fun a b c d => w ![a, b, c, d]
  have hw' : Supported3 N w' := by
    intro a b c d habcd
    apply hw
    intro hcover
    apply habcd
    rw [← range_vec_four]
    exact hcover
  have hdw' : ∀ a b c d e, d3 w' a b c d e = 0 := by
    intro a b c d e
    simpa [d3, tupleD3, w'] using hdw ![a, b, c, d, e]
  obtain ⟨z', hz', hzw'⟩ := exact_three_of_ne_univ N hN w' hw' hdw'
  let z : (Fin 3 → Vertex) → A := fun f => z' (f 0) (f 1) (f 2)
  refine ⟨z, ?_, ?_⟩
  · intro f hf
    apply hz'
    intro hcover
    apply hf
    rw [range_fin_three]
    exact hcover
  · intro f
    simpa [tupleD2, d2, z, w'] using
      hzw' (f 0) (f 1) (f 2) (f 3)

private lemma univ_not_subset_range_four_of_range_le_three
    (f : Fin 4 → Vertex) (a b c : Vertex)
    (h : Set.range f ⊆ ({a, b, c} : Set Vertex)) :
    ¬ (Set.univ : Set Vertex) ⊆ Set.range f := by
  intro hall
  exact not_univ_subset_triple a b c (hall.trans h)

/-- Multiplication on the right by an adjacent transposition preserves
vanishing of a full-support top Cech cocycle. -/
lemma tupleSupported_univ_cocycle_zero_mul_adjacentSwap
    (w : (Fin 4 → Vertex) → A)
    (hw : TupleSupported Set.univ w)
    (hdw : ∀ f, tupleD3 w f = 0)
    (sigma : Equiv.Perm (Fin 4)) (hsigma : w sigma = 0)
    (k : Fin 3) :
    w ((sigma * Equiv.swap k.castSucc k.succ) : Equiv.Perm (Fin 4)) = 0 := by
  fin_cases k
  · let f : Fin 5 → Vertex :=
      ![sigma 0, sigma 1, sigma 0, sigma 2, sigma 3]
    have h1 : w ![sigma 0, sigma 0, sigma 2, sigma 3] = 0 := by
      apply hw
      apply univ_not_subset_range_four_of_range_le_three
        _ (sigma 0) (sigma 2) (sigma 3)
      rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
    have h2 : w ![sigma 0, sigma 1, sigma 0, sigma 3] = 0 := by
      apply hw
      apply univ_not_subset_range_four_of_range_le_three
        _ (sigma 0) (sigma 1) (sigma 3)
      rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
    have h3 : w ![sigma 0, sigma 1, sigma 0, sigma 2] = 0 := by
      apply hw
      apply univ_not_subset_range_four_of_range_le_three
        _ (sigma 0) (sigma 1) (sigma 2)
      rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
    have hc := hdw f
    have hsigma' : w ![sigma 0, sigma 1, sigma 2, sigma 3] = 0 := by
      simpa using hsigma
    have hswap :
        ((sigma * Equiv.swap (0 : Fin 4) 1 : Equiv.Perm (Fin 4)) :
          Fin 4 → Fin 4) = ![sigma 1, sigma 0, sigma 2, sigma 3] := by
      funext i
      fin_cases i <;> change sigma ((Equiv.swap (0 : Fin 4) 1) _) = _ <;>
        congr 1
    change w (((sigma * Equiv.swap (0 : Fin 4) 1 : Equiv.Perm (Fin 4)) :
      Fin 4 → Fin 4)) = 0
    rw [hswap]
    dsimp [tupleD3, f] at hc
    rw [h1, h2, h3, hsigma'] at hc
    simpa using hc
  · let f : Fin 5 → Vertex :=
      ![sigma 0, sigma 1, sigma 2, sigma 1, sigma 3]
    have h0 : w ![sigma 1, sigma 2, sigma 1, sigma 3] = 0 := by
      apply hw
      apply univ_not_subset_range_four_of_range_le_three
        _ (sigma 1) (sigma 2) (sigma 3)
      rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
    have h2 : w ![sigma 0, sigma 1, sigma 1, sigma 3] = 0 := by
      apply hw
      apply univ_not_subset_range_four_of_range_le_three
        _ (sigma 0) (sigma 1) (sigma 3)
      rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
    have h4 : w ![sigma 0, sigma 1, sigma 2, sigma 1] = 0 := by
      apply hw
      apply univ_not_subset_range_four_of_range_le_three
        _ (sigma 0) (sigma 1) (sigma 2)
      rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
    have hc := hdw f
    have hsigma' : w ![sigma 0, sigma 1, sigma 2, sigma 3] = 0 := by
      simpa using hsigma
    have hswap :
        ((sigma * Equiv.swap (1 : Fin 4) 2 : Equiv.Perm (Fin 4)) :
          Fin 4 → Fin 4) = ![sigma 0, sigma 2, sigma 1, sigma 3] := by
      funext i
      fin_cases i <;> change sigma ((Equiv.swap (1 : Fin 4) 2) _) = _ <;>
        congr 1
    change w (((sigma * Equiv.swap (1 : Fin 4) 2 : Equiv.Perm (Fin 4)) :
      Fin 4 → Fin 4)) = 0
    rw [hswap]
    dsimp [tupleD3, f] at hc
    rw [h0, h2, h4, hsigma'] at hc
    simpa using hc
  · let f : Fin 5 → Vertex :=
      ![sigma 0, sigma 1, sigma 2, sigma 3, sigma 2]
    have h0 : w ![sigma 1, sigma 2, sigma 3, sigma 2] = 0 := by
      apply hw
      apply univ_not_subset_range_four_of_range_le_three
        _ (sigma 1) (sigma 2) (sigma 3)
      rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
    have h1 : w ![sigma 0, sigma 2, sigma 3, sigma 2] = 0 := by
      apply hw
      apply univ_not_subset_range_four_of_range_le_three
        _ (sigma 0) (sigma 2) (sigma 3)
      rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
    have h3 : w ![sigma 0, sigma 1, sigma 2, sigma 2] = 0 := by
      apply hw
      apply univ_not_subset_range_four_of_range_le_three
        _ (sigma 0) (sigma 1) (sigma 2)
      rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
    have hc := hdw f
    have hsigma' : w ![sigma 0, sigma 1, sigma 2, sigma 3] = 0 := by
      simpa using hsigma
    have hswap :
        ((sigma * Equiv.swap (2 : Fin 4) 3 : Equiv.Perm (Fin 4)) :
          Fin 4 → Fin 4) = ![sigma 0, sigma 1, sigma 3, sigma 2] := by
      funext i
      fin_cases i <;> change sigma ((Equiv.swap (2 : Fin 4) 3) _) = _ <;>
        congr 1
    change w (((sigma * Equiv.swap (2 : Fin 4) 3 : Equiv.Perm (Fin 4)) :
      Fin 4 → Fin 4)) = 0
    rw [hswap]
    dsimp [tupleD3, f] at hc
    rw [h0, h1, h3, hsigma'] at hc
    simpa using hc

/-- A full-support top Cech cocycle is detected by its identity-tuple value.
In particular, if that value is zero, the entire cochain is zero. -/
theorem tupleSupported_univ_cocycle_eq_zero_of_id_eq_zero
    (w : (Fin 4 → Vertex) → A)
    (hw : TupleSupported Set.univ w)
    (hdw : ∀ f, tupleD3 w f = 0)
    (hid : w id = 0) :
    w = 0 := by
  let S : Set (Equiv.Perm (Fin 4)) :=
    Set.range (fun k : Fin 3 => Equiv.swap k.castSucc k.succ)
  have hgen (tau : Equiv.Perm (Fin 4)) (htau : tau ∈ S) :
      ∀ sigma : Equiv.Perm (Fin 4), w sigma = 0 →
        w ((sigma * tau) : Equiv.Perm (Fin 4)) = 0 := by
    obtain ⟨k, rfl⟩ := htau
    intro sigma hsigma
    exact tupleSupported_univ_cocycle_zero_mul_adjacentSwap
      w hw hdw sigma hsigma k
  have hone : ∀ sigma : Equiv.Perm (Fin 4), w sigma = 0 →
      w ((sigma * 1) : Equiv.Perm (Fin 4)) = 0 := by
    intro sigma hsigma
    simpa using hsigma
  have hmul : ∀ (x y : Equiv.Perm (Fin 4))
      (_hx : x ∈ Submonoid.closure S) (_hy : y ∈ Submonoid.closure S),
      (∀ sigma : Equiv.Perm (Fin 4), w sigma = 0 →
        w ((sigma * x) : Equiv.Perm (Fin 4)) = 0) →
      (∀ sigma : Equiv.Perm (Fin 4), w sigma = 0 →
        w ((sigma * y) : Equiv.Perm (Fin 4)) = 0) →
      ∀ sigma : Equiv.Perm (Fin 4), w sigma = 0 →
        w ((sigma * (x * y)) : Equiv.Perm (Fin 4)) = 0 := by
    intro x y hx hy hX hY sigma hsigma
    have hxzero := hX sigma hsigma
    have hyzero := hY (sigma * x) hxzero
    simpa [mul_assoc] using hyzero
  have hall (tau : Equiv.Perm (Fin 4)) (htau : tau ∈ Submonoid.closure S) :
      ∀ sigma : Equiv.Perm (Fin 4), w sigma = 0 →
        w ((sigma * tau) : Equiv.Perm (Fin 4)) = 0 := by
    exact Submonoid.closure_induction hgen hone hmul htau
  have hperm (tau : Equiv.Perm (Fin 4)) : w tau = 0 := by
    have hclosure : Submonoid.closure S = ⊤ := by
      exact Equiv.Perm.mclosure_swap_castSucc_succ 3
    have htau : tau ∈ Submonoid.closure S := by
      rw [hclosure]
      exact Submonoid.mem_top tau
    have hid' : w (1 : Equiv.Perm (Fin 4)) = 0 := by
      simpa using hid
    have h := hall tau htau (1 : Equiv.Perm (Fin 4)) hid'
    simpa using h
  funext f
  by_cases hf : Function.Surjective f
  · let sigma : Equiv.Perm (Fin 4) :=
      Equiv.ofBijective f
        ((Fintype.bijective_iff_surjective_and_card f).2 ⟨hf, rfl⟩)
    have h := hperm sigma
    simpa [sigma] using h
  · apply hw f
    intro hsub
    apply hf
    rw [← Set.range_eq_univ]
    exact Set.eq_univ_of_univ_subset hsub

end LaurentCechCore
end PfaffianDescent
