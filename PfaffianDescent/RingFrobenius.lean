import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace PfaffianDescent
open Module
open scoped BigOperators
section
variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype ι] [DecidableEq ι]

/-- The multiplication pairing over an arbitrary commutative base ring. -/
def ringMultiplicationDual (ell : Module.Dual R A) : A →ₗ[R] Module.Dual R A where
  toFun a :=
    { toFun := fun b => ell (a*b)
      map_add' := by intro x y; rw [mul_add, map_add]
      map_smul' := by intro r x; simp only [mul_smul_comm, map_smul, RingHom.id_apply] }
  map_add' := by
    intro a b
    ext x
    change ell ((a+b)*x) = ell (a*x) + ell (b*x)
    rw [add_mul, map_add]
  map_smul' := by
    intro r a
    ext x
    change ell ((r • a)*x) = r • ell (a*x)
    rw [smul_mul_assoc, map_smul]

/-- The matrix of the multiplication pairing in a finite free basis. -/
noncomputable def multiplicationGram (b : Basis ι R A) (ell : Module.Dual R A) : Matrix ι ι R :=
  fun i j => ell (b j * b i)

lemma multiplicationGram_mulVec (b : Basis ι R A) (ell : Module.Dual R A) (a : A) (i : ι) :
    (multiplicationGram b ell).mulVec (b.equivFun a) i = ell (a * b i) := by
  have ha := b.sum_repr a
  calc
    _ = ∑ j, b.repr a j * ell (b j * b i) := by
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    _ = ell ((∑ j, b.repr a j • b j) * b i) := by
      simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul]
    _ = _ := by rw [ha]

/-- An invertible Gram matrix proves that the multiplication pairing is perfect
over the base ring; no field or finite-dimensional surjectivity argument is used. -/
theorem ringMultiplicationDual_bijective (b : Basis ι R A) (ell : Module.Dual R A)
    (h : IsUnit (multiplicationGram b ell).det) : Function.Bijective (ringMultiplicationDual ell) := by
  have hu : IsUnit (multiplicationGram b ell) :=
    (multiplicationGram b ell).isUnit_iff_isUnit_det.mpr h
  constructor
  · intro a a' he
    apply b.equivFun.injective
    apply Matrix.mulVec_injective_of_isUnit hu
    funext i
    rw [multiplicationGram_mulVec, multiplicationGram_mulVec]
    exact LinearMap.congr_fun he (b i)
  · intro psi
    obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hu (fun i => psi (b i))
    refine ⟨b.equivFun.symm v, b.ext (fun i => ?_)⟩
    change ell (b.equivFun.symm v * b i) = psi (b i)
    rw [← multiplicationGram_mulVec, LinearEquiv.apply_symm_apply]
    exact congrFun hv i

/-- The perfect multiplication pairing as a linear equivalence. -/
noncomputable def ringFrobeniusEquiv (b : Basis ι R A) (ell : Module.Dual R A)
    (h : IsUnit (multiplicationGram b ell).det) : A ≃ₗ[R] Module.Dual R A :=
  LinearEquiv.ofBijective (ringMultiplicationDual ell) (ringMultiplicationDual_bijective b ell h)

end
end PfaffianDescent
