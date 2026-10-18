import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Polynomial ideal contraction through a field extension

The generic target may be constructed after an algebraic closure of the
quadratic coefficient field.  Membership in an original polynomial ideal
descends from that extension, since polynomial coefficient extension is a
faithfully flat base change of the ground-field extension.
-/

namespace AllCharacteristics

universe u

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Extension and contraction of a polynomial ideal through any field
coefficient map recovers the original ideal. -/
theorem polynomialIdeal_comap_map_of_field_extension
    {k K : Type u} [Field k] [Field K] {σ : Type}
    (f : k →+* K) (I : Ideal (MvPolynomial σ k)) :
    (I.map (MvPolynomial.map f)).comap (MvPolynomial.map f) = I := by
  letI : Algebra k K := f.toAlgebra
  have hf : (algebraMap k K).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hpoly : (algebraMap (MvPolynomial σ k) (MvPolynomial σ K)).FaithfullyFlat :=
    RingHom.FaithfullyFlat.isStableUnderBaseChange k K
      (MvPolynomial σ k) (MvPolynomial σ K) hf
  letI : Module.FaithfullyFlat (MvPolynomial σ k) (MvPolynomial σ K) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hpoly
  have hmap : algebraMap (MvPolynomial σ k) (MvPolynomial σ K) =
      MvPolynomial.map f := by
    calc
      _ = MvPolynomial.map (algebraMap k K) := MvPolynomial.algebraMap_def
      _ = MvPolynomial.map f :=
        congrArg (fun g : k →+* K => MvPolynomial.map (σ := σ) g)
          (RingHom.algebraMap_toAlgebra f)
  have hcontract := I.comap_map_eq_self_of_faithfullyFlat (B := MvPolynomial σ K)
  rw [hmap] at hcontract
  exact hcontract

/-- A polynomial belongs to the original defining ideal whenever its
coefficient extension belongs to the extended ideal. -/
theorem polynomial_mem_ideal_of_map_mem_field_extension
    {k K : Type u} [Field k] [Field K] {σ : Type}
    (f : k →+* K) (I : Ideal (MvPolynomial σ k)) (G : MvPolynomial σ k)
    (hG : G.map f ∈ I.map (MvPolynomial.map f)) : G ∈ I := by
  have hmem : G ∈ (I.map (MvPolynomial.map f)).comap (MvPolynomial.map f) := hG
  rw [polynomialIdeal_comap_map_of_field_extension f I] at hmem
  exact hmem

/-- In particular, divisibility by a cubic equation descends from any larger
coefficient field, with no perfectness or characteristic restriction. -/
theorem polynomial_mem_principal_of_map_mem_field_extension
    {k K : Type u} [Field k] [Field K] {σ : Type}
    (f : k →+* K) (F G : MvPolynomial σ k)
    (hG : G.map f ∈ Ideal.span ({F.map f} : Set (MvPolynomial σ K))) :
    G ∈ Ideal.span ({F} : Set (MvPolynomial σ k)) := by
  apply polynomial_mem_ideal_of_map_mem_field_extension f (Ideal.span {F}) G
  simpa only [Ideal.map_span, Set.image_singleton] using hG

end AllCharacteristics
