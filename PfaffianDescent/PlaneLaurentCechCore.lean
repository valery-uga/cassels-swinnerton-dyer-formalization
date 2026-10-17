import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
/-! SOURCE ONLY / UNCHECKED. Actual three-vertex Laurent simplex contractions.
Degree1 exactness holds for all negative supports; degree2 exactness holds
for proper support. Full three-coordinate support is deliberately NOT
contracted in degree2: it carries O_P2(-3) top cohomology. -/
namespace PfaffianDescent
namespace PlaneLaurentCechCore

abbrev Vertex := Fin 3

variable {A : Type*} [AddCommGroup A]

/-- Degree-zero cochains supported on one-tuples which contain `N`. -/
def Supported0 (N : Set Vertex) (x : Vertex → A) : Prop :=
  ∀ a, ¬ N ⊆ ({a} : Set Vertex) → x a = 0

/-- Degree-one cochains supported on ordered pairs which contain `N`. -/
def Supported1 (N : Set Vertex) (y : Vertex → Vertex → A) : Prop :=
  ∀ a b, ¬ N ⊆ ({a, b} : Set Vertex) → y a b = 0

/-- Degree-two cochains supported on ordered triples which contain `N`. -/
def Supported2 (N : Set Vertex) (z : Vertex → Vertex → Vertex → A) : Prop :=
  ∀ a b c, ¬ N ⊆ ({a, b, c} : Set Vertex) → z a b c = 0

/-- The Cech differential from degree zero to degree one. -/
def d0 (x : Vertex → A) (a b : Vertex) : A :=
  x b - x a

/-- The Cech differential from degree one to degree two. -/
def d1 (y : Vertex → Vertex → A) (a b c : Vertex) : A :=
  y b c - y a c + y a b

/-- The Cech differential from degree two to degree three. -/
def d2 (z : Vertex → Vertex → Vertex → A) (a b c d : Vertex) : A :=
  z b c d - z a c d + z a b d - z a b c

lemma d1_d0 (x : Vertex → A) (a b c : Vertex) :
    d1 (d0 x) a b c = 0 := by
  simp [d0, d1]

lemma d2_d1 (y : Vertex → Vertex → A) (a b c d : Vertex) :
    d2 (d1 y) a b c d = 0 := by
  dsimp [d1, d2]
  abel

/-- Prepending a vertex outside `N` preserves failure to contain `N`. -/
lemma not_subset_insert_of_not_mem
    {N : Set Vertex} {p : Vertex} (hp : p ∉ N) {s : Set Vertex}
    (hs : ¬ N ⊆ s) : ¬ N ⊆ insert p s := by
  intro h
  apply hs
  intro i hi
  have hii := h hi
  rcases hii with hip | his
  · exact (hp (hip ▸ hi)).elim
  · exact his

/-- Contract a degree-one cocycle by prepending a vertex outside its negative support. -/
theorem exact_one_of_missing_vertex
    (N : Set Vertex) (p : Vertex) (hp : p ∉ N)
    (y : Vertex → Vertex → A) (hy : Supported1 N y)
    (hdy : ∀ a b c, d1 y a b c = 0) :
    ∃ x : Vertex → A, Supported0 N x ∧ ∀ a b, d0 x a b = y a b := by
  let x : Vertex → A := fun a => y p a
  refine ⟨x, ?_, ?_⟩
  · intro a ha
    exact hy p a (not_subset_insert_of_not_mem hp ha)
  · intro a b
    have h := hdy p a b
    dsimp [d0, d1, x] at h ⊢
    rw [← sub_eq_zero]
    have hn := congrArg Neg.neg h
    abel_nf at hn ⊢
    exact hn

/-- Contract a degree-two cocycle by prepending a vertex outside its negative support. -/
theorem exact_two_of_missing_vertex
    (N : Set Vertex) (p : Vertex) (hp : p ∉ N)
    (z : Vertex → Vertex → Vertex → A) (hz : Supported2 N z)
    (hdz : ∀ a b c d, d2 z a b c d = 0) :
    ∃ y : Vertex → Vertex → A, Supported1 N y ∧
      ∀ a b c, d1 y a b c = z a b c := by
  let y : Vertex → Vertex → A := fun a b => z p a b
  refine ⟨y, ?_, ?_⟩
  · intro a b hab
    exact hz p a b (not_subset_insert_of_not_mem hp hab)
  · intro a b c
    have h := hdz p a b c
    dsimp [d1, d2, y] at h ⊢
    rw [← sub_eq_zero]
    have hn := congrArg Neg.neg h
    abel_nf at hn ⊢
    exact hn

/-- A proper negative support has a coordinate outside it. -/
lemma exists_missing_vertex {N : Set Vertex} (hN : N ≠ Set.univ) :
    ∃ p : Vertex, p ∉ N := by
  classical
  by_contra h
  apply hN
  exact Set.eq_univ_iff_forall.mpr fun p => by
    by_contra hp
    exact h ⟨p, hp⟩

/-- Exactness in degree one for every proper negative support. -/
theorem exact_one_of_ne_univ
    (N : Set Vertex) (hN : N ≠ Set.univ)
    (y : Vertex → Vertex → A) (hy : Supported1 N y)
    (hdy : ∀ a b c, d1 y a b c = 0) :
    ∃ x : Vertex → A, Supported0 N x ∧ ∀ a b, d0 x a b = y a b := by
  obtain ⟨p, hp⟩ := exists_missing_vertex hN
  exact exact_one_of_missing_vertex N p hp y hy hdy

/-- Exactness in degree two for every proper negative support. -/
theorem exact_two_of_ne_univ
    (N : Set Vertex) (hN : N ≠ Set.univ)
    (z : Vertex → Vertex → Vertex → A) (hz : Supported2 N z)
    (hdz : ∀ a b c d, d2 z a b c d = 0) :
    ∃ y : Vertex → Vertex → A, Supported1 N y ∧
      ∀ a b c, d1 y a b c = z a b c := by
  obtain ⟨p, hp⟩ := exists_missing_vertex hN
  exact exact_two_of_missing_vertex N p hp z hz hdz


lemma not_univ_subset_pair (a b : Vertex) :
    ¬ (Set.univ : Set Vertex) ⊆ ({a, b} : Set Vertex) := by
  intro h
  let f : Fin 2 → Vertex := ![a, b]
  have hf : Function.Surjective f := by
    intro x
    have hx := h (Set.mem_univ x)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, by simp [f]⟩
    · exact ⟨1, by simp [f]⟩
  have hc := Fintype.card_le_of_surjective f hf
  norm_num at hc

lemma supported1_univ_eq_zero (y : Vertex → Vertex → A)
    (hy : Supported1 Set.univ y) : y = 0 := by
  funext a b
  exact hy a b (not_univ_subset_pair a b)

/-- Every Laurent-monomial summand of the three-open ordered Cech complex is
exact in degree one.  Proper negative support is contracted by a missing
coordinate; full negative support has zero degree-one term. -/
theorem exact_one
    (N : Set Vertex) (y : Vertex → Vertex → A) (hy : Supported1 N y)
    (hdy : ∀ a b c, d1 y a b c = 0) :
    ∃ x : Vertex → A, Supported0 N x ∧ ∀ a b, d0 x a b = y a b := by
  by_cases hN : N = Set.univ
  · subst N
    have hy0 : y = 0 := supported1_univ_eq_zero y hy
    refine ⟨0, ?_, ?_⟩
    · intro a ha
      rfl
    · intro a b
      rw [hy0]
      simp [d0]
  · exact exact_one_of_ne_univ N hN y hy hdy

lemma range_vec_one (a : Vertex) :
    Set.range ![a] = ({a} : Set Vertex) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    simp
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨0, by simp⟩

lemma range_vec_two (a b : Vertex) :
    Set.range ![a, b] = ({a, b} : Set Vertex) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

lemma range_vec_three (a b c : Vertex) :
    Set.range ![a, b, c] = ({a, b, c} : Set Vertex) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩

lemma range_vec_four (a b c d : Vertex) :
    Set.range ![a, b, c, d] = ({a, b, c, d} : Set Vertex) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨3, by simp⟩

@[simp]
lemma vec_one_eta (f : Fin 1 → Vertex) : ![f 0] = f := by
  funext i
  fin_cases i
  simp

@[simp]
lemma vec_two_eta (f : Fin 2 → Vertex) : ![f 0, f 1] = f := by
  funext i
  fin_cases i <;> simp

@[simp]
lemma vec_three_eta (f : Fin 3 → Vertex) : ![f 0, f 1, f 2] = f := by
  funext i
  fin_cases i <;> simp

@[simp]
lemma vec_four_eta (f : Fin 4 → Vertex) : ![f 0, f 1, f 2, f 3] = f := by
  funext i
  fin_cases i <;> simp

lemma range_fin_one (f : Fin 1 → Vertex) :
    Set.range f = ({f 0} : Set Vertex) := by
  have hf : f = ![f 0] := by
    funext j
    fin_cases j
    rfl
  calc
    Set.range f = Set.range ![f 0] := congrArg Set.range hf
    _ = ({f 0} : Set Vertex) := range_vec_one _

lemma range_fin_two (f : Fin 2 → Vertex) :
    Set.range f = ({f 0, f 1} : Set Vertex) := by
  have hf : f = ![f 0, f 1] := by
    funext j
    fin_cases j <;> rfl
  calc
    Set.range f = Set.range ![f 0, f 1] := congrArg Set.range hf
    _ = ({f 0, f 1} : Set Vertex) := range_vec_two _ _

lemma range_fin_three (f : Fin 3 → Vertex) :
    Set.range f = ({f 0, f 1, f 2} : Set Vertex) := by
  have hf : f = ![f 0, f 1, f 2] := by
    funext j
    fin_cases j <;> rfl
  calc
    Set.range f = Set.range ![f 0, f 1, f 2] := congrArg Set.range hf
    _ = ({f 0, f 1, f 2} : Set Vertex) := range_vec_three _ _ _

lemma range_fin_four (f : Fin 4 → Vertex) :
    Set.range f = ({f 0, f 1, f 2, f 3} : Set Vertex) := by
  have hf : f = ![f 0, f 1, f 2, f 3] := by
    funext j
    fin_cases j <;> rfl
  calc
    Set.range f = Set.range ![f 0, f 1, f 2, f 3] := congrArg Set.range hf
    _ = ({f 0, f 1, f 2, f 3} : Set Vertex) := range_vec_four _ _ _ _

/-- Tuple-indexed support condition, matching the ordered tuples in
`cechComplexFunctor`. -/
def TupleSupported (N : Set Vertex) {q : ℕ}
    (x : (Fin (q + 1) → Vertex) → A) : Prop :=
  ∀ f, ¬ N ⊆ Set.range f → x f = 0

/-- Tuple-indexed degree-zero Cech differential. -/
def tupleD0 (x : (Fin 1 → Vertex) → A)
    (f : Fin 2 → Vertex) : A :=
  x ![f 1] - x ![f 0]

/-- Tuple-indexed degree-one Cech differential. -/
def tupleD1 (y : (Fin 2 → Vertex) → A)
    (f : Fin 3 → Vertex) : A :=
  y ![f 1, f 2] - y ![f 0, f 2] + y ![f 0, f 1]

/-- Tuple-indexed degree-two Cech differential. -/
def tupleD2 (z : (Fin 3 → Vertex) → A)
    (f : Fin 4 → Vertex) : A :=
  z ![f 1, f 2, f 3] - z ![f 0, f 2, f 3] +
    z ![f 0, f 1, f 3] - z ![f 0, f 1, f 2]

lemma tupleD1_tupleD0 (x : (Fin 1 → Vertex) → A) (f : Fin 3 → Vertex) :
    tupleD1 (tupleD0 x) f = 0 := by
  dsimp [tupleD0, tupleD1]
  abel

lemma tupleD2_tupleD1 (y : (Fin 2 → Vertex) → A) (f : Fin 4 → Vertex) :
    tupleD2 (tupleD1 y) f = 0 := by
  dsimp [tupleD1, tupleD2]
  abel

/-- Exactness in degree one in the tuple-indexed form used by the raw Cech
complex. -/
theorem tuple_exact_one
    (N : Set Vertex) (y : (Fin 2 → Vertex) → A) (hy : TupleSupported N y)
    (hdy : ∀ f, tupleD1 y f = 0) :
    ∃ x : (Fin 1 → Vertex) → A, TupleSupported N x ∧
      ∀ f, tupleD0 x f = y f := by
  let y' : Vertex → Vertex → A := fun a b => y ![a, b]
  have hy' : Supported1 N y' := by
    intro a b hab
    apply hy
    intro hcover
    apply hab
    rw [← range_vec_two]
    exact hcover
  have hdy' : ∀ a b c, d1 y' a b c = 0 := by
    intro a b c
    simpa [d1, tupleD1, y'] using hdy ![a, b, c]
  obtain ⟨x', hx', hxy'⟩ := exact_one N y' hy' hdy'
  let x : (Fin 1 → Vertex) → A := fun f => x' (f 0)
  refine ⟨x, ?_, ?_⟩
  · intro f hf
    apply hx'
    intro hcover
    apply hf
    rw [range_fin_one]
    exact hcover
  · intro f
    simpa [tupleD0, d0, x, y'] using hxy' (f 0) (f 1)

/-- Exactness in degree two in the tuple-indexed form used by the raw Cech
complex. -/
theorem tuple_exact_two
    (N : Set Vertex) (hN : N ≠ Set.univ) (z : (Fin 3 → Vertex) → A) (hz : TupleSupported N z)
    (hdz : ∀ f, tupleD2 z f = 0) :
    ∃ y : (Fin 2 → Vertex) → A, TupleSupported N y ∧
      ∀ f, tupleD1 y f = z f := by
  let z' : Vertex → Vertex → Vertex → A := fun a b c => z ![a, b, c]
  have hz' : Supported2 N z' := by
    intro a b c habc
    apply hz
    intro hcover
    apply habc
    rw [← range_vec_three]
    exact hcover
  have hdz' : ∀ a b c d, d2 z' a b c d = 0 := by
    intro a b c d
    simpa [d2, tupleD2, z'] using hdz ![a, b, c, d]
  obtain ⟨y', hy', hyz'⟩ := exact_two_of_ne_univ N hN z' hz' hdz'
  let y : (Fin 2 → Vertex) → A := fun f => y' (f 0) (f 1)
  refine ⟨y, ?_, ?_⟩
  · intro f hf
    apply hy'
    intro hcover
    apply hf
    rw [range_fin_two]
    exact hcover
  · intro f
    simpa [tupleD1, d1, y, z'] using hyz' (f 0) (f 1) (f 2)

end PlaneLaurentCechCore
end PfaffianDescent
