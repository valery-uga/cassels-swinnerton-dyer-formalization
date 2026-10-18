import AllCharacteristics.HomogeneousSpecialization
import Mathlib.RingTheory.Ideal.Maps

/-!
# Homogeneous relation detection from a polynomial specialization

This is the algebraic dominance step for the universal raw secant vector.
A homogeneous relation at the generic polynomial vector is a polynomial
identity, because its coefficient embedding is injective.  Specialize that
identity at a constructed preimage of a generic target vector.  A nonzero
projective scaling cancels, so the relation belongs to the target ideal.
-/

namespace AllCharacteristics

universe u

/-- If a polynomial coordinate family specializes to a nonzero scalar times
a target vector with precisely the defining homogeneous relations, every
homogeneous relation at the generic family belongs to the defining ideal. -/
theorem homogeneous_relations_of_polynomial_specialization
    {k A L M : Type u} [CommRing k] [CommRing A] [CommRing L] [Field M]
    {σ : Type}
    (f : k →+* A) (ι : A →+* L) (hι : Function.Injective ι)
    (ψ : A →+* M) (κ : k →+* M) (hbase : ψ.comp f = κ)
    (r : σ → A) (z : σ → M) (s : M) (hs : s ≠ 0)
    (hr : (fun i => ψ (r i)) = s • z)
    (I : Ideal (MvPolynomial σ k))
    (hrelations : ∀ (p : MvPolynomial σ k) (e : ℕ),
      p.IsHomogeneous e → p.eval₂ κ z = 0 → p ∈ I)
    (G : MvPolynomial σ k) (d : ℕ) (hG : G.IsHomogeneous d)
    (hzero : G.eval₂ (ι.comp f) (fun i => ι (r i)) = 0) : G ∈ I := by
  have hpoly : G.eval₂ f r = 0 := by
    apply hι
    rw [map_zero, MvPolynomial.hom_eval₂]
    exact hzero
  have hspecial : G.eval₂ (ψ.comp f) (fun i => ψ (r i)) = 0 := by
    rw [← MvPolynomial.hom_eval₂, hpoly, map_zero]
  rw [hbase, hr, eval₂_homogeneous_smul G hG] at hspecial
  have htarget : G.eval₂ κ z = 0 :=
    (mul_eq_zero.mp hspecial).resolve_left (pow_ne_zero d hs)
  exact hrelations G d hG htarget

/-- The same geometric specialization supplies nonvanishing of the generic
raw coordinate vector.  It is enough that the specialized target is nonzero. -/
theorem polynomial_coordinate_vector_ne_zero_of_nonzero_specialization
    {A L M : Type u} [CommRing A] [CommRing L] [Field M] {σ : Type}
    (ι : A →+* L) (hι : Function.Injective ι) (ψ : A →+* M)
    (r : σ → A) (z : σ → M) (hz : z ≠ 0) (s : M) (hs : s ≠ 0)
    (hr : (fun i => ψ (r i)) = s • z) :
    (fun i => ι (r i)) ≠ 0 := by
  intro hzero
  have hrzero : r = 0 := by
    funext i
    apply hι
    simpa only [Pi.zero_apply, map_zero] using congrFun hzero i
  have hscaled : s • z = 0 := by
    rw [← hr, hrzero]
    funext i
    exact map_zero ψ
  apply hz
  funext i
  have hi := congrFun hscaled i
  change s * z i = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_left hs

end AllCharacteristics
