import PfaffianDescent.QuarticTwistedCubicSymmetricCube

/-!
# Projective scalar invariance of the standard twisted-cubic ideal

A projective coordinate change is represented by a matrix only up to a
nonzero scalar.  This file records that such scalars do not change the
homogeneous ideal of the standard twisted cubic.
-/

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open scoped MatrixGroups

universe u

variable {K : Type u} [Field K]

noncomputable section

lemma linearSubstitution_scalar_standardTwistedCubicGenerator
    (r : K) (i : Fin 3) :
    linearSubstitution (Matrix.scalar (Fin 4) r)
      (standardTwistedCubicGenerators K i) =
        C (r ^ 2) * standardTwistedCubicGenerators K i := by
  fin_cases i <;>
    simp [standardTwistedCubicGenerators, linearSubstitution, linearCoordinate,
      Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply,
      Fin.sum_univ_succ] <;> ring

theorem standardTwistedCubicIdeal_map_scalar
    (r : K) (hr : r ≠ 0) :
    (standardTwistedCubicIdeal K).map
      (linearSubstitution (Matrix.scalar (Fin 4) r)).toRingHom =
        standardTwistedCubicIdeal K := by
  let f := (linearSubstitution (Matrix.scalar (Fin 4) r)).toRingHom
  rw [standardTwistedCubicIdeal, Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨q, ⟨i, rfl⟩, rfl⟩
    rw [show f (standardTwistedCubicGenerators K i) =
      C (r ^ 2) * standardTwistedCubicGenerators K i by
        exact linearSubstitution_scalar_standardTwistedCubicGenerator r i]
    exact Ideal.mul_mem_left (Ideal.span (Set.range (standardTwistedCubicGenerators K))) _
      (Ideal.subset_span (Set.mem_range_self i))
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    have himage : f (standardTwistedCubicGenerators K i) ∈ Ideal.span
        (f '' Set.range (standardTwistedCubicGenerators K)) := by
      rw [← Ideal.map_span]
      exact Ideal.mem_map_of_mem f (Ideal.subset_span (Set.mem_range_self i))
    rw [show f (standardTwistedCubicGenerators K i) =
      C (r ^ 2) * standardTwistedCubicGenerators K i by
        exact linearSubstitution_scalar_standardTwistedCubicGenerator r i] at himage
    have hrewrite : standardTwistedCubicGenerators K i =
        C ((r ^ 2)⁻¹) * (C (r ^ 2) * standardTwistedCubicGenerators K i) := by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero 2 hr), C_1, one_mul]
    rw [hrewrite]
    exact Ideal.mul_mem_left _ _ himage

/-- The action on the standard twisted-cubic ideal depends only on the
projective class of an invertible coordinate matrix. -/
theorem ideal_map_standardTwistedCubic_of_projectively_eq
    (I : Ideal (MvPolynomial (Fin 4) K)) (M N : GL (Fin 4) K)
    (hMN : Matrix.ProjGenLinGroup.mk M = Matrix.ProjGenLinGroup.mk N)
    (hM : I.map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K) :
    I.map
      (linearSubstitution (N : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hMN
  have hmat : (N : Matrix (Fin 4) (Fin 4) K) =
      (M : Matrix (Fin 4) (Fin 4) K) * Matrix.scalar (Fin 4) (u : K) := by
    have h := congrArg (fun X : GL (Fin 4) K =>
      (X : Matrix (Fin 4) (Fin 4) K)) hu
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using h.symm
  have hlin : linearSubstitution (N : Matrix (Fin 4) (Fin 4) K) =
      (linearSubstitution (Matrix.scalar (Fin 4) (u : K))).comp
        (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)) := by
    rw [hmat]
    exact (linearSubstitution_comp (Matrix.scalar (Fin 4) (u : K))
      (M : Matrix (Fin 4) (Fin 4) K)).symm
  calc
    I.map
        (linearSubstitution (N : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        I.map
          (((linearSubstitution (Matrix.scalar (Fin 4) (u : K))).comp
            (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K))).toRingHom) := by
          rw [hlin]
    _ = (I.map
          (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)).toRingHom).map
            ((linearSubstitution (Matrix.scalar (Fin 4) (u : K))).toRingHom) := by
          let s := linearSubstitution (Matrix.scalar (Fin 4) (u : K))
          let m := linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)
          have hcomp : (s.comp m).toRingHom = s.toRingHom.comp m.toRingHom := rfl
          change I.map (s.comp m).toRingHom =
            (I.map m.toRingHom).map s.toRingHom
          rw [hcomp]
          exact (Ideal.map_map m.toRingHom s.toRingHom).symm
    _ = standardTwistedCubicIdeal K := by
          rw [hM, standardTwistedCubicIdeal_map_scalar]
          exact Units.ne_zero u

/-- Every projective binary reparametrization, through the cubic symmetric
power representation, preserves the standard twisted-cubic ideal. -/
theorem standardTwistedCubicIdeal_map_symmetricCubePGL
    (g : PGL(Fin 2, K)) (B : GL (Fin 4) K)
    (hB : Matrix.ProjGenLinGroup.mk B = symmetricCubePGL g) :
    (standardTwistedCubicIdeal K).map
      (linearSubstitution (B : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K := by
  let A : GL (Fin 2) K := Quotient.out g
  have hA : Matrix.ProjGenLinGroup.mk A = g := Quotient.out_eq g
  have hstandard : (standardTwistedCubicIdeal K).map
      (linearSubstitution (symmetricCubeMatrix (A : Matrix (Fin 2) (Fin 2) K))).toRingHom =
        standardTwistedCubicIdeal K :=
    standardTwistedCubicIdeal_map_symmetricCube (A : Matrix (Fin 2) (Fin 2) K)
      ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A))
  have hstandard' : (standardTwistedCubicIdeal K).map
      (linearSubstitution ((symmetricCubeGL A : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K)).toRingHom = standardTwistedCubicIdeal K := by
    exact hstandard
  have hproj : Matrix.ProjGenLinGroup.mk (symmetricCubeGL A) =
      Matrix.ProjGenLinGroup.mk B := by
    calc
      Matrix.ProjGenLinGroup.mk (symmetricCubeGL A) =
          symmetricCubePGL (Matrix.ProjGenLinGroup.mk A) :=
        (symmetricCubePGL_mk A).symm
      _ = symmetricCubePGL g := by rw [hA]
      _ = Matrix.ProjGenLinGroup.mk B := hB.symm
  exact ideal_map_standardTwistedCubic_of_projectively_eq (standardTwistedCubicIdeal K)
    (symmetricCubeGL A) B hproj hstandard'

/-- A projective factorization by a cubic symmetric-power reparametrization
transports any ideal already carried to the standard twisted cubic to the
same standard ideal. -/
theorem ideal_map_standardTwistedCubic_of_pgl_coordinate_factor
    (I : Ideal (MvPolynomial (Fin 4) K))
    (M Y : GL (Fin 4) K) (r : PGL(Fin 2, K))
    (hY : Matrix.ProjGenLinGroup.mk Y =
      Matrix.ProjGenLinGroup.mk M *
        ((symmetricCubePGL r : PGL(Fin 4, K))⁻¹))
    (hM : I.map (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)).toRingHom =
      standardTwistedCubicIdeal K) :
    I.map (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom =
      standardTwistedCubicIdeal K := by
  obtain ⟨R, hR⟩ := Matrix.ProjGenLinGroup.mk_surjective
    (symmetricCubePGL r⁻¹)
  have hRstandard : (standardTwistedCubicIdeal K).map
      (linearSubstitution (R : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K := by
    apply standardTwistedCubicIdeal_map_symmetricCubePGL r⁻¹ R
    exact hR
  have hMR : I.map
      (linearSubstitution ((M * R : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K := by
    let s := linearSubstitution (R : Matrix (Fin 4) (Fin 4) K)
    let m := linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)
    have hlin : linearSubstitution ((M * R : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = s.comp m := by
      change linearSubstitution ((M : Matrix (Fin 4) (Fin 4) K) *
        (R : Matrix (Fin 4) (Fin 4) K)) = s.comp m
      exact (linearSubstitution_comp (R : Matrix (Fin 4) (Fin 4) K)
        (M : Matrix (Fin 4) (Fin 4) K)).symm
    rw [hlin]
    have hcomp : (s.comp m).toRingHom = s.toRingHom.comp m.toRingHom := rfl
    rw [hcomp, ← Ideal.map_map, hM]
    exact hRstandard
  have hproj : Matrix.ProjGenLinGroup.mk (M * R) = Matrix.ProjGenLinGroup.mk Y := by
    calc
      Matrix.ProjGenLinGroup.mk (M * R) =
          Matrix.ProjGenLinGroup.mk M * Matrix.ProjGenLinGroup.mk R := by
            rw [Matrix.ProjGenLinGroup.mk.map_mul]
      _ = Matrix.ProjGenLinGroup.mk M * symmetricCubePGL r⁻¹ := by rw [hR]
      _ = Matrix.ProjGenLinGroup.mk M * (symmetricCubePGL r)⁻¹ := by rw [map_inv]
      _ = Matrix.ProjGenLinGroup.mk Y := hY.symm
  exact ideal_map_standardTwistedCubic_of_projectively_eq I (M * R) Y hproj hMR

end

end PfaffianDescent.QuarticNet
