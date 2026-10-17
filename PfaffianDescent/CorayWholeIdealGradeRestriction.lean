import PfaffianDescent.CorayHomogeneousIdealLinearKernelProjection
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Degreewise maps for an ideal inside its ambient graded algebra.
These generic cuts retain explicit map/regularity hypotheses. Original
geometric callers must construct those hypotheses separately. SOURCE ONLY. -/
noncomputable section
namespace PfaffianDescent.Coray
open Module
universe u v w
variable {K : Type u} [Field K]
variable {A : Type v} {B : Type w} [CommRing A] [CommRing B]
variable [Algebra K A] [Algebra K B]

/-- The degree-d part of the whole ideal in the same ambient ring. -/
def wholeIdealGrade (G : ℕ → Submodule K A) (J : Ideal A) (d : ℕ) :
    Submodule K A := J.restrictScalars K ⊓ G d

/-- The actual algebra map restricted to the same degree and whole ideals. -/
def wholeIdealGradeRestriction
    (G : ℕ → Submodule K A) (T : ℕ → Submodule K B)
    (J : Ideal A) (Q : Ideal B) (f : A →ₐ[K] B)
    (hf : ∀ d x, x ∈ G d → f x ∈ T d)
    (hJ : ∀ x, x ∈ J → f x ∈ Q) (d : ℕ) :
    wholeIdealGrade G J d →ₗ[K] wholeIdealGrade T Q d where
  toFun x := ⟨f x.val, hJ x.val x.property.1, hf d x.val x.property.2⟩
  map_add' x y := Subtype.ext (map_add f x.val y.val)
  map_smul' c x := Subtype.ext (f.toLinearMap.map_smul c x.val)

/-- Multiplication by the actual degree-one class, retaining whole-ideal membership. -/
def wholeIdealGradeLinearMultiplication
    (G : ℕ → Submodule K A) [GradedRing G] (J : Ideal A)
    (H : A) (hH : H ∈ G 1) (d : ℕ) :
    wholeIdealGrade G J d →ₗ[K] wholeIdealGrade G J (d + 1) where
  toFun x := ⟨H * x.val, J.mul_mem_left H x.property.1,
    by
      change H * x.val ∈ G (d + 1)
      simpa only [Nat.add_comm 1 d] using SetLike.mul_mem_graded hH x.property.2⟩
  map_add' x y := Subtype.ext (mul_add H x.val y.val)
  map_smul' c x := Subtype.ext (mul_smul_comm c H x.val)

/-- An actual ungraded kernel witness projects to an exact consecutive-degree
sequence. Homogeneity, rather than a supplied degreewise witness, is used. -/
theorem wholeIdealGradeRestriction_ker_eq_range
    (G : ℕ → Submodule K A) [GradedRing G]
    (T : ℕ → Submodule K B) (J : Ideal A) (Q : Ideal B)
    (hJhom : J.IsHomogeneous G) (f : A →ₐ[K] B)
    (hf : ∀ d x, x ∈ G d → f x ∈ T d)
    (hJ : ∀ x, x ∈ J → f x ∈ Q)
    (H : A) (hH : H ∈ G 1) (hfH : f H = 0)
    (hkernel : ∀ y, y ∈ J → f y = 0 → ∃ z, z ∈ J ∧ H * z = y)
    (d : ℕ) :
    LinearMap.ker (wholeIdealGradeRestriction G T J Q f hf hJ (d + 1)) =
      LinearMap.range (wholeIdealGradeLinearMultiplication G J H hH d) := by
  apply le_antisymm
  · intro y hy
    have hyzero : f y.val = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hy)
    obtain ⟨z, hz, hzy⟩ := hkernel y.val y.property.1 hyzero
    obtain ⟨a, haJ, had, hay⟩ :=
      homogeneousIdeal_linearFactor_exists_complementaryDegree
        G J hJhom H hH (d + 1) (Nat.le_add_left 1 d)
        y.val y.property.2 z hz hzy
    have had' : a ∈ G d := by simpa only [Nat.add_sub_cancel] using had
    exact ⟨⟨a, haJ, had'⟩, Subtype.ext hay⟩
  · rintro y ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change f (H * x.val) = 0
    rw [map_mul, hfH, zero_mul]

/-- Rank-nullity gives the needed upper bound; neither surjectivity of
restriction nor injectivity of multiplication is needed for this inequality. -/
theorem wholeIdealGradeRestriction_finrank_le
    (G : ℕ → Submodule K A) [GradedRing G]
    (T : ℕ → Submodule K B) (J : Ideal A) (Q : Ideal B)
    (hJhom : J.IsHomogeneous G) (f : A →ₐ[K] B)
    (hf : ∀ d x, x ∈ G d → f x ∈ T d)
    (hJ : ∀ x, x ∈ J → f x ∈ Q)
    (H : A) (hH : H ∈ G 1) (hfH : f H = 0)
    (hkernel : ∀ y, y ∈ J → f y = 0 → ∃ z, z ∈ J ∧ H * z = y)
    (d : ℕ)
    [Module.Finite K (wholeIdealGrade G J d)]
    [Module.Finite K (wholeIdealGrade G J (d + 1))]
    [Module.Finite K (wholeIdealGrade T Q (d + 1))] :
    finrank K (wholeIdealGrade G J (d + 1)) ≤
      finrank K (wholeIdealGrade G J d) + finrank K (wholeIdealGrade T Q (d + 1)) := by
  let r := wholeIdealGradeRestriction G T J Q f hf hJ (d + 1)
  let m := wholeIdealGradeLinearMultiplication G J H hH d
  have hk : r.ker = m.range :=
    wholeIdealGradeRestriction_ker_eq_range G T J Q hJhom f hf hJ H hH hfH hkernel d
  have heq := r.finrank_range_add_finrank_ker
  rw [hk] at heq
  have hm := m.finrank_range_le
  have hr := Submodule.finrank_le r.range
  omega

end PfaffianDescent.Coray
