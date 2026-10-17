import PfaffianDescent.QuarticTwistedCubicResidual
import PfaffianDescent.PolynomialLinearChange
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial
open Matrix
open scoped MatrixGroups

universe u v
variable {K : Type u} [Field K]

noncomputable def symmetricCubeMatrix (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 4) (Fin 4) K :=
  let a := A 0 0
  let b := A 0 1
  let c := A 1 0
  let d := A 1 1
  ![![a^3, 3*a^2*b, 3*a*b^2, b^3],
    ![a^2*c, a^2*d + 2*a*b*c, 2*a*b*d + b^2*c, b^2*d],
    ![a*c^2, 2*a*c*d + b*c^2, a*d^2 + 2*b*c*d, b*d^2],
    ![c^3, 3*c^2*d, 3*c*d^2, d^3]]

theorem cubicVeronese_symmetricCubeMatrix_mulVec
    (A : Matrix (Fin 2) (Fin 2) K) (s t : K) :
    (symmetricCubeMatrix A).mulVec (cubicVeronese s t) =
      cubicVeronese ((A.mulVec ![s, t]) 0) ((A.mulVec ![s, t]) 1) := by
  ext i
  fin_cases i <;> simp [symmetricCubeMatrix, cubicVeronese,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

lemma standardTwistedCubicParam_linearCoordinate
    (M : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    standardTwistedCubicParam K (linearCoordinate M i) =
      (M.map C).mulVec (fun j => standardTwistedCubicParam K (X j)) i := by
  simp [linearCoordinate, Matrix.mulVec, dotProduct, standardTwistedCubicParam, Matrix.map]

 theorem standardTwistedCubicParam_linearSubstitution_symmetricCube
    (A : Matrix (Fin 2) (Fin 2) K) :
    (standardTwistedCubicParam K).comp (linearSubstitution (symmetricCubeMatrix A)) =
      (linearSubstitution A).comp (standardTwistedCubicParam K) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, linearSubstitution_X,
    standardTwistedCubicParam_linearCoordinate, AlgHom.comp_apply]
  have hC2 : (C (2 : K) : MvPolynomial (Fin 2) K) = 2 := by
    rw [show (2 : K) = 1 + 1 by norm_num, C_add, C_1]
    norm_num
  have hC3 : (C (3 : K) : MvPolynomial (Fin 2) K) = 3 := by
    rw [show (3 : K) = 1 + 1 + 1 by norm_num, C_add, C_add, C_1]
    norm_num
  fin_cases i <;> simp [standardTwistedCubicParam, linearSubstitution,
    linearCoordinate, symmetricCubeMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.map, hC2, hC3] <;> ring


/-- The cubic symmetric-power action preserves the standard twisted-cubic
ideal. -/
theorem standardTwistedCubicIdeal_map_symmetricCube_le
    (A : Matrix (Fin 2) (Fin 2) K) :
    (standardTwistedCubicIdeal K).map
      (linearSubstitution (symmetricCubeMatrix A)).toRingHom ≤
        standardTwistedCubicIdeal K := by
  rw [Ideal.map_le_iff_le_comap]
  intro p hp
  rw [standardTwistedCubicIdeal_eq_ker] at hp ⊢
  change standardTwistedCubicParam K (linearSubstitution (symmetricCubeMatrix A) p) = 0
  have h := DFunLike.congr_fun
    (standardTwistedCubicParam_linearSubstitution_symmetricCube A) p
  change standardTwistedCubicParam K (linearSubstitution (symmetricCubeMatrix A) p) =
    linearSubstitution A (standardTwistedCubicParam K p) at h
  change standardTwistedCubicParam K p = 0 at hp
  rw [h, hp]
  exact map_zero _


/-- Taking the cubic symmetric power respects composition. -/
theorem symmetricCubeMatrix_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    symmetricCubeMatrix (A * B) = symmetricCubeMatrix A * symmetricCubeMatrix B := by
  ext i j
  change symmetricCubeMatrix (A * B) i j =
    ∑ x, symmetricCubeMatrix A i x * symmetricCubeMatrix B x j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricCubeMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring


/-- The cubic symmetric power of the identity is the identity. -/
theorem symmetricCubeMatrix_one :
    symmetricCubeMatrix (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricCubeMatrix]


/-- An invertible binary change has an invertible cubic symmetric power. -/
theorem symmetricCubeMatrix_isUnit (A : Matrix (Fin 2) (Fin 2) K)
    (hA : IsUnit A.det) : IsUnit (symmetricCubeMatrix A) := by
  rw [isUnit_iff_exists_inv]
  refine ⟨symmetricCubeMatrix A⁻¹, ?_⟩
  rw [← symmetricCubeMatrix_mul, Matrix.mul_nonsing_inv A hA,
    symmetricCubeMatrix_one]

/-- An invertible binary change preserves the standard twisted-cubic ideal
exactly. -/
theorem standardTwistedCubicIdeal_map_symmetricCube
    (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    (standardTwistedCubicIdeal K).map
      (linearSubstitution (symmetricCubeMatrix A)).toRingHom =
        standardTwistedCubicIdeal K := by
  apply le_antisymm
  · exact standardTwistedCubicIdeal_map_symmetricCube_le A
  · have hP : IsUnit (symmetricCubeMatrix A).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (symmetricCubeMatrix_isUnit A hA)
    have hsurj : Function.Surjective
        (linearSubstitution (symmetricCubeMatrix A)).toRingHom :=
      (linearSubstitutionEquiv (symmetricCubeMatrix A) hP).surjective
    intro p hp
    rw [Ideal.mem_map_iff_of_surjective _ hsurj]
    refine ⟨linearSubstitution (symmetricCubeMatrix A⁻¹) p, ?_, ?_⟩
    · exact standardTwistedCubicIdeal_map_symmetricCube_le A⁻¹
        (Ideal.mem_map_of_mem _ hp)
    · change linearSubstitution (symmetricCubeMatrix A)
        (linearSubstitution (symmetricCubeMatrix A⁻¹) p) = p
      rw [← AlgHom.comp_apply, linearSubstitution_comp,
        ← symmetricCubeMatrix_mul, Matrix.nonsing_inv_mul A hA,
        symmetricCubeMatrix_one, linearSubstitution_one]
      rfl


/-- Rescaling a binary matrix rescales its cubic symmetric power by the
third power.  Thus the construction is compatible with projective linear
coordinates. -/
theorem symmetricCubeMatrix_smul (r : K) (A : Matrix (Fin 2) (Fin 2) K) :
    symmetricCubeMatrix (r • A) = r ^ 3 • symmetricCubeMatrix A := by
  ext i j
  change symmetricCubeMatrix (r • A) i j = r ^ 3 * symmetricCubeMatrix A i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricCubeMatrix] <;> ring


/-- The cubic symmetric-power construction as a homomorphism of general
linear groups. -/
noncomputable def symmetricCubeMatrixMonoidHom :
    Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 4) (Fin 4) K where
  toFun := symmetricCubeMatrix
  map_one' := symmetricCubeMatrix_one
  map_mul' := symmetricCubeMatrix_mul

noncomputable def symmetricCubeGL : GL (Fin 2) K →* GL (Fin 4) K :=
  Units.map symmetricCubeMatrixMonoidHom

/-- On scalar binary matrices, the cubic symmetric-power action is scalar
with the scalar cubed. -/
theorem symmetricCubeGL_scalar (u : Kˣ) :
    symmetricCubeGL (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 4) (u ^ 3) := by
  apply Units.ext
  change symmetricCubeMatrix (Matrix.scalar (Fin 2) (u : K)) =
    Matrix.scalar (Fin 4) ((u ^ 3 : Kˣ) : K)
  rw [show Matrix.scalar (Fin 2) (u : K) = (u : K) • 1 by
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]]
  rw [symmetricCubeMatrix_smul, symmetricCubeMatrix_one]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

/-- The cubic symmetric-power action descends to projective linear groups. -/
noncomputable def symmetricCubePGL : PGL(Fin 2, K) →* PGL(Fin 4, K) :=
  Matrix.ProjGenLinGroup.lift
    (Matrix.ProjGenLinGroup.mk.comp symmetricCubeGL) (by
      ext u
      change Matrix.ProjGenLinGroup.mk (symmetricCubeGL
        (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) = 1
      rw [symmetricCubeGL_scalar, Matrix.ProjGenLinGroup.mk_scalar])

lemma symmetricCubePGL_mk (g : GL (Fin 2) K) :
    symmetricCubePGL (Matrix.ProjGenLinGroup.mk g) =
      Matrix.ProjGenLinGroup.mk (symmetricCubeGL g) := by
  rfl


/-- Cubic symmetric powers commute with every field homomorphism. -/
theorem symmetricCubeMatrix_map {L : Type v} [Field L]
    (f : K →+* L) (A : Matrix (Fin 2) (Fin 2) K) :
    (symmetricCubeMatrix A).map f = symmetricCubeMatrix (A.map f) := by
  have h2 : f 2 = 2 := map_ofNat f 2
  have h3 : f 3 = 3 := map_ofNat f 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricCubeMatrix, Matrix.map, h2, h3]


/-- The symmetric-cube action on general linear groups commutes with a field
homomorphism. -/
theorem symmetricCubeGL_map {L : Type v} [Field L]
    (f : K →+* L) (g : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.map f (symmetricCubeGL g) =
      symmetricCubeGL (Matrix.GeneralLinearGroup.map f g) := by
  apply Units.ext
  change (symmetricCubeMatrix g).map f =
    symmetricCubeMatrix ((g : Matrix (Fin 2) (Fin 2) K).map f)
  exact symmetricCubeMatrix_map f g

/-- The projective symmetric-cube action commutes with a field homomorphism.
This is the compatibility required to apply it to a Galois descent datum. -/
theorem symmetricCubePGL_map {L : Type v} [Field L]
    (f : K →+* L) (g : PGL(Fin 2, K)) :
    Matrix.ProjGenLinGroup.map f (symmetricCubePGL g) =
      symmetricCubePGL (Matrix.ProjGenLinGroup.map f g) := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk g =>
      simp only [symmetricCubePGL_mk, Matrix.ProjGenLinGroup.map_mk]
      rw [symmetricCubeGL_map]


/-- The cubic symmetric-power representation has no projective kernel. -/
theorem symmetricCubeMatrix_eq_scalar_imp
    (A : Matrix (Fin 2) (Fin 2) K) (r : K)
    (h : symmetricCubeMatrix A = Matrix.scalar (Fin 4) r) :
    ∃ a : K, A = Matrix.scalar (Fin 2) a := by
  have hb3 : A 0 1 ^ 3 = 0 := by
    have h03 := congrFun (congrFun h 0) 3
    simpa [symmetricCubeMatrix, Matrix.scalar_apply, Matrix.diagonal_apply] using h03
  have hc3 : A 1 0 ^ 3 = 0 := by
    have h30 := congrFun (congrFun h 3) 0
    simpa [symmetricCubeMatrix, Matrix.scalar_apply, Matrix.diagonal_apply] using h30
  have hb : A 0 1 = 0 := (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp hb3
  have hc : A 1 0 = 0 := (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp hc3
  have ha3 : A 0 0 ^ 3 = r := by
    have h00 := congrFun (congrFun h 0) 0
    simpa [symmetricCubeMatrix, Matrix.scalar_apply, Matrix.diagonal_apply] using h00
  have h11 : A 0 0 ^ 2 * A 1 1 = r := by
    have h11 := congrFun (congrFun h 1) 1
    simpa [symmetricCubeMatrix, Matrix.scalar_apply, Matrix.diagonal_apply, hb, hc] using h11
  have hd3 : A 1 1 ^ 3 = r := by
    have h33 := congrFun (congrFun h 3) 3
    simpa [symmetricCubeMatrix, Matrix.scalar_apply, Matrix.diagonal_apply] using h33
  by_cases ha : A 0 0 = 0
  · have hr : r = 0 := by
      simpa [ha] using ha3.symm
    have hd : A 1 1 = 0 := by
      apply (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp
      rw [hd3, hr]
    refine ⟨0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, ha, hb, hc, hd]
  · have ha2 : A 0 0 ^ 2 ≠ 0 := pow_ne_zero 2 ha
    have had : A 0 0 ^ 2 * A 0 0 = A 0 0 ^ 2 * A 1 1 := by
      calc
        A 0 0 ^ 2 * A 0 0 = A 0 0 ^ 3 := by ring
        _ = r := ha3
        _ = A 0 0 ^ 2 * A 1 1 := h11.symm
    have had' : A 0 0 = A 1 1 := mul_left_cancel₀ ha2 had
    refine ⟨A 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, hb, hc, had']


/-- The induced homomorphism from projective binary changes to projective
changes of the twisted cubic is injective. -/
theorem symmetricCubePGL_injective : Function.Injective (symmetricCubePGL (K := K)) := by
  intro x y hxy
  induction x using Matrix.ProjGenLinGroup.induction_on with
  | mk x =>
    induction y using Matrix.ProjGenLinGroup.induction_on with
    | mk y =>
      rw [symmetricCubePGL_mk, symmetricCubePGL_mk] at hxy
      obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hxy
      let P : GL (Fin 4) K := symmetricCubeGL x
      let Q : GL (Fin 4) K := symmetricCubeGL y
      let c : GL (Fin 4) K := Matrix.GeneralLinearGroup.scalar (Fin 4) u
      have hc : c ∈ Subgroup.center (GL (Fin 4) K) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨u, rfl⟩
      have hPQ : P * c = Q := hu
      have hcent : P * Q⁻¹ ∈ Subgroup.center (GL (Fin 4) K) := by
        have hcalc : P * Q⁻¹ = c⁻¹ := by
          rw [← hPQ, _root_.mul_inv_rev]
          calc
            P * (c⁻¹ * P⁻¹) = (P * c⁻¹) * P⁻¹ := by rw [mul_assoc]
            _ = (c⁻¹ * P) * P⁻¹ := by
              rw [(Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) P).symm]
            _ = c⁻¹ * (P * P⁻¹) := by rw [mul_assoc]
            _ = c⁻¹ := by simp
        rw [hcalc]
        exact Subgroup.inv_mem _ hc
      have hphi : symmetricCubeGL (x * y⁻¹) = P * Q⁻¹ := by
        simp only [P, Q, map_mul, map_inv]
      have hcent' : symmetricCubeGL (x * y⁻¹) ∈ Subgroup.center (GL (Fin 4) K) := by
        rw [hphi]
        exact hcent
      obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hcent'
      have hA : symmetricCubeMatrix ((x * y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          Matrix.scalar (Fin 4) a := by
        change (symmetricCubeGL (x * y⁻¹) : Matrix (Fin 4) (Fin 4) K) = _
        exact ha.symm
      obtain ⟨a, hA'⟩ := symmetricCubeMatrix_eq_scalar_imp _ _ hA
      have ha0 : a ≠ 0 := by
        intro ha0
        let z : GL (Fin 2) K := x * y⁻¹
        have hz0 : (z : Matrix (Fin 2) (Fin 2) K) = 0 := by
          simpa [z, ha0] using hA'
        have hinv : (z : Matrix (Fin 2) (Fin 2) K) *
            ((z⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
          simpa only [Matrix.GeneralLinearGroup.coe_mul,
            Matrix.GeneralLinearGroup.coe_one] using congrArg Units.val (mul_inv_cancel z)
        rw [hz0] at hinv
        apply (zero_ne_one : (0 : Matrix (Fin 2) (Fin 2) K) ≠ 1)
        simp only [zero_mul] at hinv
        exact hinv
      let v : Kˣ := Units.mk0 a ha0
      have hz : x * y⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) v := by
        apply Units.ext
        simpa [v] using hA'
      apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
      refine ⟨v⁻¹, ?_⟩
      have hxy' : x = Matrix.GeneralLinearGroup.scalar (Fin 2) v * y := by
        have := congrArg (fun z : GL (Fin 2) K => z * y) hz
        simpa [mul_assoc] using this
      rw [hxy']
      have hcomm := Subgroup.mem_center_iff.mp (show
          Matrix.GeneralLinearGroup.scalar (Fin 2) v⁻¹ ∈
            Subgroup.center (GL (Fin 2) K) by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨v⁻¹, rfl⟩) y
      calc
        (Matrix.GeneralLinearGroup.scalar (Fin 2) v * y) *
            Matrix.GeneralLinearGroup.scalar (Fin 2) v⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 2) v *
            (y * Matrix.GeneralLinearGroup.scalar (Fin 2) v⁻¹) := by rw [mul_assoc]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 2) v *
            (Matrix.GeneralLinearGroup.scalar (Fin 2) v⁻¹ * y) := by rw [hcomm.symm]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) v *
            Matrix.GeneralLinearGroup.scalar (Fin 2) v⁻¹) * y := by rw [mul_assoc]
        _ = y := by simp

end QuarticNet
end PfaffianDescent
