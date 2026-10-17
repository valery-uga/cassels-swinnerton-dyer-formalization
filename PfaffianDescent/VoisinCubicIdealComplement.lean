import PfaffianDescent.VoisinCubicGrassmannianSpread
import PfaffianDescent.CubicSurfacePointEvaluation
import Mathlib.LinearAlgebra.Projection

/-!
# Removing the defining cubic from a varying cubic system

The defining cubic vanishes on every configuration, so a variable system
used in generic incidence must first be separated from that relation.
This file constructs a complementary homogeneous subspace without losing
any sections of the corresponding cubic-surface coordinate-ring system.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every homogeneous cubic subspace has a complementary subspace
independent modulo the defining cubic and with the same image in the
cubic-surface coordinate ring. -/
theorem exists_cubicSubmodule_separated_complement
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (I : Submodule F (homogeneousSubmodule (Fin 4) F 3)) :
    ∃ W : Submodule F (homogeneousSubmodule (Fin 4) F 3),
      W ≤ I ∧
      (∀ q ∈ W,
        q.1 ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) F)) → q = 0) ∧
      LinearMap.range
          ((cubicSurfaceHomogeneousCoordinateProjection p hp 3).comp W.subtype) =
      LinearMap.range
          ((cubicSurfaceHomogeneousCoordinateProjection p hp 3).comp I.subtype) := by
  letI : AddCommGroup I := inferInstance
  let projection := cubicSurfaceHomogeneousCoordinateProjection p hp 3
  let f : I →ₗ[F] grading (equationIdeal p hp) 3 :=
    projection.comp I.subtype
  obtain ⟨Q, hQ⟩ := (LinearMap.ker f).exists_isCompl
  let W : Submodule F (homogeneousSubmodule (Fin 4) F 3) :=
    Q.map I.subtype
  refine ⟨W, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hq
    exact v.property
  · intro q hq hrel
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hq
    have hfzero : f v = 0 := by
      apply Subtype.ext
      change Ideal.Quotient.mk (equationIdeal p hp).toIdeal v.1.1 = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hrel
    have hvker : v ∈ LinearMap.ker f := LinearMap.mem_ker.mpr hfzero
    have hvzero : v = 0 := by
      have hb : v ∈ (⊥ : Submodule F I) :=
        hQ.disjoint.le_bot ⟨hvker, hv⟩
      simpa only [Submodule.mem_bot] using hb
    simpa [hvzero]
  · apply le_antisymm
    · rintro y ⟨w, rfl⟩
      obtain ⟨v, hv, hval⟩ := Submodule.mem_map.mp w.property
      refine ⟨v, ?_⟩
      change projection v.1 = projection w.1
      exact congrArg projection hval
    · rintro y ⟨v, rfl⟩
      obtain ⟨u, w, hu, _⟩ := Submodule.existsUnique_add_of_isCompl hQ v
      have hw : (w.1 : homogeneousSubmodule (Fin 4) F 3) ∈ W :=
        ⟨w.1, w.property, rfl⟩
      refine ⟨⟨w.1, hw⟩, ?_⟩
      have hfu : f u.1 = 0 := LinearMap.mem_ker.mp u.property
      have hfv : f v = f w.1 := by
        rw [← hu, map_add, hfu, zero_add]
      exact hfv.symm

/-- A nonzero coordinate-ring section represented by a cubic in the
original system has a nonzero representative in the separated complement.
Thus choosing the complement does not lose a member needed for incidence. -/
theorem exists_cubicSubmodule_separated_complement_lift_member
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (I : Submodule F (homogeneousSubmodule (Fin 4) F 3))
    (q : homogeneousSubmodule (Fin 4) F 3) (hqI : q ∈ I)
    (hqnonzero :
      cubicSurfaceHomogeneousCoordinateProjection p hp 3 q ≠ 0) :
    ∃ (W : Submodule F (homogeneousSubmodule (Fin 4) F 3))
      (q' : homogeneousSubmodule (Fin 4) F 3),
      W ≤ I ∧
      (∀ z ∈ W,
        z.1 ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) F)) → z = 0) ∧
      q' ∈ W ∧ q' ≠ 0 ∧
      cubicSurfaceHomogeneousCoordinateProjection p hp 3 q' =
        cubicSurfaceHomogeneousCoordinateProjection p hp 3 q := by
  let projection := cubicSurfaceHomogeneousCoordinateProjection p hp 3
  obtain ⟨W, hWI, hsep, hrange⟩ :=
    exists_cubicSubmodule_separated_complement p hp I
  have hqrange : projection q ∈ LinearMap.range
      (projection.comp I.subtype) := ⟨⟨q, hqI⟩, rfl⟩
  rw [← hrange] at hqrange
  obtain ⟨q', hq'eval⟩ := hqrange
  have hq'0 : (q' : homogeneousSubmodule (Fin 4) F 3) ≠ 0 := by
    intro hzero
    apply hqnonzero
    have heq : projection q'.1 = projection q := hq'eval
    simpa [hzero] using heq.symm
  exact ⟨W, q'.1, hWI, hsep, q'.property, hq'0, hq'eval⟩

end PfaffianDescent
