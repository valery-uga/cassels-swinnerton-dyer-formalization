import PfaffianDescent.KernelVector
import PfaffianDescent.GoodTriple
import PfaffianDescent.StablePoint
import PfaffianDescent.Specialization

/-! An explicit polynomial deformation removes the stable-kernel hypothesis. -/
namespace PfaffianDescent
open Polynomial

section Ring
variable {R S : Type*} [CommRing R] [CommRing S]

theorem isAlternating_add (A B : Mat R 6) (hA : IsAlternating A)
    (hB : IsAlternating B) : IsAlternating (A + B) := by
  constructor
  · intro i
    change A i i + B i i = 0
    rw [hA.1, hB.1, add_zero]
  · intro i j
    change A j i + B j i = -(A i j + B i j)
    rw [hA.2, hB.2, neg_add]

theorem isAlternating_smul (c : R) (A : Mat R 6) (hA : IsAlternating A) :
    IsAlternating (c • A) := by
  constructor
  · intro i
    change c * A i i = 0
    rw [hA.1, mul_zero]
  · intro i j
    change c * A j i = -(c * A i j)
    rw [hA.2, mul_neg]

theorem deform_alternating (A : Fin 4 → Mat R 6) (B : Fin 3 → Mat R 6)
    (hA : ∀ i, IsAlternating (A i)) (hB : ∀ i, IsAlternating (B i)) (t : R) :
    ∀ i, IsAlternating (deform A B t i) := by
  intro i
  fin_cases i
  · exact isAlternating_add _ _ (isAlternating_smul _ _ (hA 0)) (isAlternating_smul _ _ (hB 0))
  · exact isAlternating_add _ _ (isAlternating_smul _ _ (hA 1)) (isAlternating_smul _ _ (hB 1))
  · exact isAlternating_add _ _ (isAlternating_smul _ _ (hA 2)) (isAlternating_smul _ _ (hB 2))
  · exact hA 3

private theorem matrix_map_interpolate (f : R →+* S) (A B : Mat R 6) (t : R) :
    ((1 - t) • A + t • B).map f = (1 - f t) • A.map f + f t • B.map f := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    map_add, map_mul, map_sub, map_one]

theorem deform_map (f : R →+* S) (A : Fin 4 → Mat R 6) (B : Fin 3 → Mat R 6) (t : R) :
    (fun i => (deform A B t i).map f) =
      deform (fun i => (A i).map f) (fun i => (B i).map f) (f t) := by
  funext i
  fin_cases i
  · exact matrix_map_interpolate f (A 0) (B 0) t
  · exact matrix_map_interpolate f (A 1) (B 1) t
  · exact matrix_map_interpolate f (A 2) (B 2) t
  · rfl

end Ring

section Field
variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- Move the first three matrices to the fixed good triple at parameter one. -/
noncomputable def polynomialDeformation (A : Fin 4 → Mat K 6) : Fin 4 → Mat K[X] 6 :=
  deform (fun i => (A i).map C) goodTriple X

omit [NeZero (2 : K)] in
private theorem matrix_eval_constant (A : Mat K 6) (t : K) :
    (A.map C).map (evalRingHom t) = A := by
  ext i j
  exact eval_C

omit [NeZero (2 : K)] in
theorem polynomialDeformation_zero (A : Fin 4 → Mat K 6) :
    (fun i => (polynomialDeformation A i).map (evalRingHom 0)) = A := by
  rw [polynomialDeformation, deform_map]
  simp only [show (evalRingHom (0 : K)) X = 0 from eval_X, matrix_eval_constant, goodTriple_map, deform_zero]

omit [NeZero (2 : K)] in
theorem polynomialDeformation_one (A : Fin 4 → Mat K 6) :
    (fun i : Fin 3 => (polynomialDeformation A i.castSucc).map (evalRingHom 1)) = goodTriple := by
  have h := deform_map (evalRingHom (1 : K)) (fun i => (A i).map C) goodTriple X
  simp only [show (evalRingHom (1 : K)) X = 1 from eval_X, matrix_eval_constant, goodTriple_map, deform_one] at h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2

omit [NeZero (2 : K)] in
theorem polynomialDeformation_alternating (A : Fin 4 → Mat K 6)
    (hA : ∀ i, IsAlternating (A i)) : ∀ i, IsAlternating (polynomialDeformation A i) :=
  deform_alternating _ _ (fun i => isAlternating_map C (A i) (hA i)) goodTriple_alternating X

theorem deformation_kernel_discriminant_ne_zero (A : Fin 4 → Mat K 6) :
    trivectorDiscriminant (kernelVector (fun i : Fin 3 => polynomialDeformation A i.castSucc)) ≠ 0 := by
  let B : Fin 3 → Mat K[X] 6 := fun i => polynomialDeformation A i.castSucc
  have hp := kernelVector_map (evalRingHom (1 : K)) B
  rw [show (fun i => (B i).map (evalRingHom (1 : K))) = goodTriple from
    polynomialDeformation_one A] at hp
  have hd := trivectorDiscriminant_map (evalRingHom (1 : K)) (kernelVector B)
  rw [hp] at hd
  intro hz
  change trivectorDiscriminant (kernelVector B) = 0 at hz
  rw [hz, map_zero] at hd
  exact kernelVector_good_discriminant_ne_zero hd

/-- Every four-dimensional alternating six-by-six matrix pencil over a
field of characteristic different from two has a nonzero vector on which its Pfaffian vanishes.
No smoothness, genericity, or nonzero-polynomial hypothesis is required. -/
theorem pfaffian_to_point (A : Fin 4 → Mat K 6)
    (hA : ∀ i, IsAlternating (A i)) : HasPfaffianPoint A := by
  let L := FractionRing K[X]
  let f := algebraMap K[X] L
  let : NeZero (2 : L) := ⟨by
    intro h
    have htwo : (2 : K[X]) ≠ 0 := by
      intro htwo
      apply (NeZero.ne (2 : K))
      have hcoeff := congrArg (fun q : K[X] => q.coeff 0) htwo
      simpa using hcoeff
    apply htwo
    apply IsFractionRing.injective K[X] L
    change f (2 : K[X]) = f 0
    rw [← map_ofNat f 2] at h
    simpa using h
  ⟩
  let D := polynomialDeformation A
  let B : Fin 3 → Mat K[X] 6 := fun i => D i.castSucc
  let p := kernelVector B
  have hc : ∀ i : Fin 3, contract3 ((D i.castSucc).map f) (fun j => f (p j)) = 0 := by
    intro i
    rw [contract3_map]
    have hh := kernelVector_contraction B i
    change contract3 (D i.castSucc) p = 0 at hh
    rw [hh]
    funext j
    exact map_zero f
  have hp : trivectorDiscriminant (fun j => f (p j)) ≠ 0 := by
    rw [trivectorDiscriminant_map]
    exact (map_ne_zero_iff f (IsFractionRing.injective K[X] L)).mpr (deformation_kernel_discriminant_ne_zero A)
  have hpoint := pfaffian_point_of_stable_kernel (fun i => (D i).map f)
    (fun i => isAlternating_map f (D i) (polynomialDeformation_alternating A hA i))
    (fun j => f (p j)) hc hp
  have hspecial := specialize_fraction_pfaffian D hpoint
  rw [show (fun i => (D i).map (evalRingHom 0)) = A from polynomialDeformation_zero A] at hspecial
  exact hspecial

end Field
end PfaffianDescent
