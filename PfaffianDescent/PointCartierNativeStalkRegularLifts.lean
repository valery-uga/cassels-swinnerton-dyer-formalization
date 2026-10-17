import PfaffianDescent.PointCartierYonedaLocalComparison
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Regular ambient lifts of the actual surface residue parameters

The Cartier equation is the first ambient parameter. Thus lifting an existing
regular pair on the surface requires no choice of a Jacobian unit.
-/

noncomputable section

namespace PfaffianDescent

open scoped nonZeroDivisors

variable {A B : Type*} [CommRing A] [CommRing B]

theorem pointCartierNativeStalkRegularLift_first
    (t g : A) (e : (A ⧸ Ideal.span {t}) ≃+* B)
    (hg : e (Ideal.Quotient.mk (Ideal.span {t}) g) ∈ B⁰) :
    Ideal.Quotient.mk (Ideal.span {t}) g ∈ (A ⧸ Ideal.span {t})⁰ :=
  mem_nonZeroDivisors_of_injective e.injective hg

theorem pointCartierNativeStalkRegularLift_second
    (t g h : A) (e : (A ⧸ Ideal.span {t}) ≃+* B)
    (hh : Ideal.Quotient.mk
      (Ideal.span {e (Ideal.Quotient.mk (Ideal.span {t}) g)})
      (e (Ideal.Quotient.mk (Ideal.span {t}) h)) ∈
        (B ⧸ Ideal.span {e (Ideal.Quotient.mk (Ideal.span {t}) g)})⁰) :
    Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) g})
      (Ideal.Quotient.mk (Ideal.span {t}) h) ∈
        ((A ⧸ Ideal.span {t}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) g})⁰ := by
  let e' := Ideal.quotientEquiv (Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) g})
    (Ideal.span {e (Ideal.Quotient.mk (Ideal.span {t}) g)}) e (by
      simp only [Ideal.map_span, Set.image_singleton]
      rfl)
  apply mem_nonZeroDivisors_of_injective e'.injective
  simpa only [e', Ideal.quotientEquiv_mk] using hh

theorem pointCartierNativeStalkRegularLift_third
    (t g h : A)
    (hh : Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) g})
      (Ideal.Quotient.mk (Ideal.span {t}) h) ∈
        ((A ⧸ Ideal.span {t}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) g})⁰) :
    ∀ x : A, h * x ∈ Ideal.span ({t, g} : Set A) → x ∈ Ideal.span ({t, g} : Set A) := by
  let q := Ideal.Quotient.mk (Ideal.span {t})
  let q' := Ideal.Quotient.mk (Ideal.span {q g})
  have hqt : q t = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton t))
  intro x hx
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hx
  have hqx : q h * q x ∈ Ideal.span {q g} := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨q b, ?_⟩
    have heq := congrArg q hab
    simpa only [map_add, map_mul, hqt, mul_zero, zero_mul, zero_add, mul_comm] using heq.symm
  have hz : q' (q x) = 0 := by
    apply mem_nonZeroDivisors_iff_left.mp hh
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hqx
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  obtain ⟨bA, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hzero : q (x - g * bA) = 0 := by
    rw [map_sub, map_mul]
    exact sub_eq_zero.mpr hb
  obtain ⟨aA, ha⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  apply Ideal.mem_span_pair.mpr
  refine ⟨aA, bA, ?_⟩
  linear_combination -ha

end PfaffianDescent
