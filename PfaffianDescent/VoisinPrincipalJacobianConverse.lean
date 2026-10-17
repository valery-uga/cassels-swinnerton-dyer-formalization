import PfaffianDescent.VoisinSquareZeroSectionRelation
import Mathlib.RingTheory.Smooth.Basic

/-!
# Conormal cancellation for a principal polynomial relation

A section of the square-zero thickening of a polynomial presentation
forces a first-order equation. For a principal nonzero presentation
ideal, cancelling its generator turns that equation into a Bézout
identity for its partial derivatives. This is the algebraic core of the
converse Jacobian criterion; the actual projective chart has one
additional normalization equation.
-/

namespace PfaffianDescent

open MvPolynomial

universe u
variable {K : Type u} [Field K]

private theorem principal_cancel_mod_square
    (F z : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (h : F * z ∈ (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))) ^ 2) :
    z ∈ Ideal.span ({F} : Set (MvPolynomial (Fin 4) K)) := by
  rw [Ideal.span_singleton_pow] at h
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp h
  apply Ideal.mem_span_singleton.mpr
  refine ⟨w, ?_⟩
  apply mul_left_cancel₀ hF
  calc
    F * z = F ^ 2 * w := hw
    _ = F * (F * w) := by ring

/-- A formally smooth quotient of a polynomial ring by one nonzero equation
has a Jacobian unit-ideal certificate. This is the complete square-zero
section and conormal-cancellation argument in the principal case. -/
theorem formallySmooth_principalPresentation_jacobian_top
    {A : Type u} [CommRing A] [Algebra K A]
    (f : MvPolynomial (Fin 4) K →ₐ[K] A)
    (hf : Function.Surjective f)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hker : RingHom.ker f.toRingHom =
      Ideal.span ({F} : Set (MvPolynomial (Fin 4) K)))
    [Algebra.FormallySmooth K A] :
    Ideal.span (Set.range (fun i : Fin 4 => f (pderiv i F))) = ⊤ := by
  classical
  let I : Ideal (MvPolynomial (Fin 4) K) := RingHom.ker f.toRingHom
  let Q : MvPolynomial (Fin 4) K →+*
      MvPolynomial (Fin 4) K ⧸ I ^ 2 := Ideal.Quotient.mk (I ^ 2)
  obtain ⟨g, hg⟩ := (Algebra.FormallySmooth.iff_split_surjection f hf).mp
    (inferInstance : Algebra.FormallySmooth K A)
  have hsec (a : A) : f.kerSquareLift (g a) = a := by
    have h := DFunLike.congr_fun hg a
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using h
  have hrep (i : Fin 4) :
      ∃ c : MvPolynomial (Fin 4) K,
        g (f (X i)) - Q (X i) = Q (F * c) := by
    have hy : g (f (X i)) - Q (X i) ∈
        RingHom.ker f.kerSquareLift.toRingHom := by
      apply RingHom.mem_ker.mpr
      change f.kerSquareLift (g (f (X i)) - Q (X i)) = 0
      rw [map_sub, hsec]
      have hQ : f.kerSquareLift (Q (X i)) = f (X i) :=
        f.kerSquareLift_mk (X i)
      rw [hQ, sub_self]
    have hy' : g (f (X i)) - Q (X i) ∈ I.cotangentIdeal := by
      simpa only [I, AlgHom.ker_kerSquareLift] using hy
    obtain ⟨a, ha, hae⟩ := hy'
    change a ∈ I at ha
    have haF : a ∈ Ideal.span ({F} : Set (MvPolynomial (Fin 4) K)) := by
      simpa only [I, hker] using ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp haF
    refine ⟨c, ?_⟩
    change Q a = g (f (X i)) - Q (X i) at hae
    rw [hc] at hae
    exact hae.symm
  choose c hc using hrep
  have hFker : F ∈ RingHom.ker f.toRingHom :=
    hker.symm ▸ Ideal.mem_span_singleton_self F
  have hrel := mvPolynomial_kerSquareLift_section_relation_of_mem
    f g hg F hFker
  have hrel' : Q F + ∑ i : Fin 4,
      Q (F * c i) * Q (pderiv i F) = 0 := by
    change Q F + ∑ i : Fin 4,
      (g (f (X i)) - Q (X i)) * Q (pderiv i F) = 0 at hrel
    simpa only [hc] using hrel
  let z : MvPolynomial (Fin 4) K :=
    1 + ∑ i : Fin 4, c i * pderiv i F
  have hQ : Q (F * z) = 0 := by
    calc
      Q (F * z) = Q F + ∑ i : Fin 4,
          Q (F * c i) * Q (pderiv i F) := by
        simp only [z, map_mul, map_add, map_sum,
          mul_add, mul_one, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := hrel'
  have hsq : F * z ∈
      (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))) ^ 2 := by
    have hmem : F * z ∈ I ^ 2 := Ideal.Quotient.eq_zero_iff_mem.mp hQ
    simpa only [I, hker] using hmem
  have hz : z ∈ Ideal.span ({F} : Set (MvPolynomial (Fin 4) K)) :=
    principal_cancel_mod_square F z hF hsq
  have hfz : f z = 0 := RingHom.mem_ker.mp (hker.symm ▸ hz)
  let L : Ideal A := Ideal.span (Set.range (fun i : Fin 4 => f (pderiv i F)))
  have hsum_mem : (∑ i : Fin 4, f (c i) * f (pderiv i F)) ∈ L := by
    apply Submodule.sum_mem
    intro i _
    exact L.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩)
  have hzero : (1 : A) + ∑ i : Fin 4, f (c i) * f (pderiv i F) = 0 := by
    simpa only [z, map_add, map_one, map_sum, map_mul] using hfz
  have h1 : (1 : A) ∈ L := by
    have heq : (1 : A) = -∑ i : Fin 4, f (c i) * f (pderiv i F) := by
      exact eq_neg_of_add_eq_zero_left hzero
    rw [heq]
    exact L.neg_mem hsum_mem
  exact (Ideal.eq_top_iff_one L).mpr h1

end PfaffianDescent
