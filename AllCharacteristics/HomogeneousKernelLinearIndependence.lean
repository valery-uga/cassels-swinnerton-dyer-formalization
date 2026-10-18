import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Linear independence of actual coordinates with a cubic kernel

An evaluation whose only polynomial relation is a nonzero cubic has no
nontrivial linear relation among its coordinate values.  This supplies the
coordinate independence used to exclude ground-field lines through a generic
cubic point.
-/

namespace AllCharacteristics

open MvPolynomial

universe u

/-- Exact cubic coordinate relations imply linear independence of all four
actual homogeneous coordinate values over the ground field. -/
theorem linearIndependent_coordinates_of_cubic_kernel
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (E : MvPolynomial (Fin 4) K →+* L)
    (hbase : E.comp MvPolynomial.C = algebraMap K L)
    (hker : RingHom.ker E = Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))) :
    LinearIndependent K (fun i => E (MvPolynomial.X i)) := by
  classical
  let e : MvPolynomial (Fin 4) K →ₐ[K] L :=
    { toRingHom := E
      commutes' := fun r => DFunLike.congr_fun hbase r }
  have hEsmul (r : K) (p : MvPolynomial (Fin 4) K) : E (r • p) = r • E p := by
    change e (r • p) = r • e p
    exact map_smul e r p
  rw [Fintype.linearIndependent_iff]
  intro a ha
  let G : MvPolynomial (Fin 4) K := ∑ i, a i • MvPolynomial.X i
  have hGhom : G.IsHomogeneous 1 := by
    change (∑ i, a i • MvPolynomial.X i) ∈ homogeneousSubmodule (Fin 4) K 1
    apply Submodule.sum_mem
    intro i hi
    exact (homogeneousSubmodule (Fin 4) K 1).smul_mem
      (a i) (MvPolynomial.isHomogeneous_X K i)
  have hEG : E G = 0 := by
    simpa only [G, map_sum, hEsmul] using ha
  have hGzero : G = 0 := by
    by_contra hG0
    have hmem : G ∈ RingHom.ker E := hEG
    rw [hker] at hmem
    have hdvd : F ∣ G := Ideal.mem_span_singleton.mp hmem
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd hG0
    rw [hF.totalDegree hF0] at hle
    have hGdegree : G.totalDegree ≤ 1 := hGhom.totalDegree_le
    omega
  exact Fintype.linearIndependent_iff.mp
    (MvPolynomial.linearIndependent_X (R := K) (σ := Fin 4)) a hGzero

end AllCharacteristics
