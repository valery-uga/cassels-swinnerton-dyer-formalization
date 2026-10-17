import PfaffianDescent.QuarticTwistedCubicIdealDescent
import PfaffianDescent.QuarticTwistedCubicCoordinateDescent

namespace PfaffianDescent.QuarticNet

open Matrix MvPolynomial ProjectiveCocycle
open scoped MatrixGroups

universe u v

/-- A projective coordinate factorization over an extension has compatible
matrix representatives over the ground field and the extension. -/
theorem pgl_coordinate_factor_has_matrix_lift
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (Ypgl : PGL(Fin 4, K)) (M : GL (Fin 4) L) (r : PGL(Fin 2, L))
    (h : Matrix.ProjGenLinGroup.map (algebraMap K L) Ypgl =
      Matrix.ProjGenLinGroup.mk M * (symmetricCubePGL r)⁻¹) :
    ∃ Y : GL (Fin 4) K,
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (algebraMap K L) Y) =
        Matrix.ProjGenLinGroup.mk M * (symmetricCubePGL r)⁻¹ := by
  obtain ⟨Y, hY⟩ := Matrix.ProjGenLinGroup.mk_surjective Ypgl
  refine ⟨Y, ?_⟩
  calc
    Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (algebraMap K L) Y) =
        Matrix.ProjGenLinGroup.map (algebraMap K L)
          (Matrix.ProjGenLinGroup.mk Y) :=
      (Matrix.ProjGenLinGroup.map_mk (algebraMap K L) Y).symm
    _ = Matrix.ProjGenLinGroup.map (algebraMap K L) Ypgl := by rw [hY]
    _ = Matrix.ProjGenLinGroup.mk M * (symmetricCubePGL r)⁻¹ := h

/-- Mapping a three-generator ideal by a linear substitution maps its stated
finite presentation generatorwise. -/
theorem span_map_linearSubstitution
    {K : Type u} [Field K]
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (M : Matrix (Fin 4) (Fin 4) K) :
    (Ideal.span (Set.range Q)).map (linearSubstitution M).toRingHom =
      Ideal.span (Set.range (fun i => linearSubstitution M (Q i))) := by
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Q i, ⟨i, rfl⟩, rfl⟩

end PfaffianDescent.QuarticNet


namespace PfaffianDescent.QuarticNet

open Matrix MvPolynomial ProjectiveCocycle
open scoped MatrixGroups

universe u v

/-- The cohomological coordinate descent, with an actual ground-field matrix
representative selected for its projective output. -/
theorem finiteGalois_pgl_coordinate_descends_with_matrix
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (c : ProjectiveCocycle (L := L) (G := Gal(L/K)) 2 (galFieldAction K L))
    (M : GL (Fin 4) L)
    (hM : ∀ σ : Gal(L/K),
      symmetricCube c σ = (Matrix.ProjGenLinGroup.mk M)⁻¹ *
        Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom
          (Matrix.ProjGenLinGroup.mk M)) :
    ∃ (Y : GL (Fin 4) K) (r : PGL(Fin 2, L)),
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (algebraMap K L) Y) =
        Matrix.ProjGenLinGroup.mk M * (symmetricCubePGL r)⁻¹ := by
  obtain ⟨Ypgl, r, hcoord⟩ :=
    pgl4_coordinate_descends_of_symmetricCube K L c
      (Matrix.ProjGenLinGroup.mk M) hM
  obtain ⟨Y, hfactor⟩ :=
    pgl_coordinate_factor_has_matrix_lift K L Ypgl M r hcoord
  exact ⟨Y, r, hfactor⟩

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

open Matrix MvPolynomial
open scoped MatrixGroups

universe u v

/-- A symmetric-cube projective factorization carries a three-generator
extension ideal to the standard ideal in the descended ground coordinates. -/
theorem span_ideal_coordinate_descends_of_pgl_factor
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (M : GL (Fin 4) L) (Y : GL (Fin 4) K) (r : PGL(Fin 2, L))
    (hfactor : Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map (algebraMap K L) Y) =
        Matrix.ProjGenLinGroup.mk M * (symmetricCubePGL r)⁻¹)
    (hIdealM : (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K L) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L) :
    Ideal.span (Set.range (fun i =>
      linearSubstitution ((Y : Matrix (Fin 4) (Fin 4) K).map (algebraMap K L))
        (MvPolynomial.map (algebraMap K L) (Q i)))) = standardTwistedCubicIdeal L := by
  have hIdealYL : (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K L)
      (Q i)))).map (linearSubstitution
        ((Matrix.GeneralLinearGroup.map (algebraMap K L) Y : GL (Fin 4) L) :
          Matrix (Fin 4) (Fin 4) L)).toRingHom = standardTwistedCubicIdeal L :=
    ideal_map_standardTwistedCubic_of_pgl_coordinate_factor _ M
      (Matrix.GeneralLinearGroup.map (algebraMap K L) Y) r hfactor hIdealM
  calc
    Ideal.span (Set.range (fun i =>
        linearSubstitution ((Y : Matrix (Fin 4) (Fin 4) K).map (algebraMap K L))
          (MvPolynomial.map (algebraMap K L) (Q i)))) =
        (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K L)
          (Q i)))).map (linearSubstitution
            ((Matrix.GeneralLinearGroup.map (algebraMap K L) Y : GL (Fin 4) L) :
              Matrix (Fin 4) (Fin 4) L)).toRingHom :=
      (span_map_linearSubstitution
        (fun i => MvPolynomial.map (algebraMap K L) (Q i))
        ((Matrix.GeneralLinearGroup.map (algebraMap K L) Y : GL (Fin 4) L) :
          Matrix (Fin 4) (Fin 4) L)).symm
    _ = standardTwistedCubicIdeal L := hIdealYL

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

open Matrix MvPolynomial ProjectiveCocycle
open scoped MatrixGroups

universe u v

/-- The finite-Galois algebraic descent endpoint for a three-quadric
presentation of a geometrically standard twisted cubic. -/
theorem finiteGalois_twistedCubic_ideal_descends_of_symmetricCube
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (c : ProjectiveCocycle (L := L) (G := Gal(L/K)) 2 (galFieldAction K L))
    (M : GL (Fin 4) L)
    (hM : ∀ σ : Gal(L/K),
      symmetricCube c σ = (Matrix.ProjGenLinGroup.mk M)⁻¹ *
        Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom
          (Matrix.ProjGenLinGroup.mk M))
    (hIdealM : (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K L) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L) :
    ∃ Y : GL (Fin 4) K,
      (Ideal.span (Set.range Q)).map
        (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom =
          standardTwistedCubicIdeal K := by
  obtain ⟨Y, r, hfactor⟩ :=
    finiteGalois_pgl_coordinate_descends_with_matrix K L c M hM
  have hYL := span_ideal_coordinate_descends_of_pgl_factor K L Q M Y r hfactor hIdealM
  refine ⟨Y, ?_⟩
  exact ideal_map_coordinate_descends_to_standardTwistedCubic (k := K) (L := L)
    (Ideal.span (Set.range Q)) Q rfl (Y : Matrix (Fin 4) (Fin 4) K) hYL

end PfaffianDescent.QuarticNet
