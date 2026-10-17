import PfaffianDescent.QuarticTwistedCubicProjectiveFixed

/-!
# Descent of a symmetric-cube projective coordinate datum

This is the linear-algebraic conclusion of twisted-cubic descent.  Once a
geometric parametrization supplies the binary cocycle and identifies its
ambient discrepancy with the cubic symmetric power, the ambient projective
coordinate change can be replaced by one over the ground field.
-/

namespace PfaffianDescent.QuarticNet.ProjectiveCocycle

open Matrix
open scoped MatrixGroups

universe u v

theorem pgl4_coordinate_descends_of_symmetricCube
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (c : ProjectiveCocycle (L := L) (G := Gal(L/K)) 2 (galFieldAction K L))
    (M : PGL(Fin 4, L))
    (hM : ∀ σ : Gal(L/K),
      symmetricCube c σ = M⁻¹ *
        Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom M) :
    ∃ Y : PGL(Fin 4, K), ∃ r : PGL(Fin 2, L),
      Matrix.ProjGenLinGroup.map (algebraMap K L) Y =
        M * (symmetricCubePGL r)⁻¹ := by
  obtain ⟨r, hr⟩ :=
    isCoboundary_of_symmetricCube_isCoboundary_galois K L c ⟨M, hM⟩
  let Z : PGL(Fin 4, L) := M * (symmetricCubePGL r)⁻¹
  have hMmap (σ : Gal(L/K)) :
      Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom M =
        M * symmetricCube c σ := by
    calc
      Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom M =
          1 * Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom M := by
            rw [one_mul]
      _ = (M * M⁻¹) *
          Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom M := by
            rw [mul_inv_cancel]
      _ = M * (M⁻¹ *
          Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom M) := by
            rw [mul_assoc]
      _ = M * symmetricCube c σ := by rw [← hM σ]
  have hZ (σ : Gal(L/K)) :
      Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom Z = Z := by
    dsimp only [Z]
    rw [map_mul, map_inv, hMmap σ, symmetricCubePGL_map]
    calc
      (M * symmetricCube c σ) *
          (symmetricCubePGL
            (Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom r))⁻¹ =
          M * (symmetricCube c σ *
            (symmetricCubePGL
              (Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom r))⁻¹) := by
            rw [mul_assoc]
      _ = M * (symmetricCubePGL
            (r⁻¹ * Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom r) *
            (symmetricCubePGL
              (Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom r))⁻¹) := by
            congr 2
            change symmetricCubePGL (c σ) = symmetricCubePGL
              (r⁻¹ * Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom r)
            rw [hr σ]
            rfl
      _ = M * ((symmetricCubePGL r)⁻¹ *
            symmetricCubePGL
              (Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom r) *
            (symmetricCubePGL
              (Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom r))⁻¹) := by
            rw [map_mul, map_inv]
      _ = M * (symmetricCubePGL r)⁻¹ := by
            simp only [mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨Y, hY⟩ := pgl_fixed_descends K L (by omega) Z hZ
  exact ⟨Y, r, hY⟩

end PfaffianDescent.QuarticNet.ProjectiveCocycle
