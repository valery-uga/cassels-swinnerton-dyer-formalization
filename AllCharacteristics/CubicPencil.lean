import AllCharacteristics.UniversalFieldParameters
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Pencils of cubic surfaces

The smoothing argument uses the family `(1-t)F + tG`.  This file first
records the family as an actual polynomial over `k[t]`, with its degree and
endpoint specializations proved exactly.
-/

namespace AllCharacteristics

universe u
variable {k : Type u} [Field k]

namespace UniversalHomogeneous

/-- The raw universal coefficient evaluation commutes with a further map of
coefficient rings.  Unlike the field-valued classifying-map wrapper, this
version also applies to the polynomial ring `k[t]`. -/
theorem coefficientEvaluation_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {σ : Type} [Finite σ] {d : ℕ}
    (b : R →+* S) (p : MvPolynomial σ S) (c : S →+* T) :
    c.comp (MvPolynomial.eval₂Hom b
      (fun m : Monomials σ d => p.coeff m.1)) =
      MvPolynomial.eval₂Hom (c.comp b)
        (fun m : Monomials σ d => (p.map c).coeff m.1) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro m
    simp [MvPolynomial.coeff_map]

end UniversalHomogeneous

/-- The homogeneous pencil `(1-t)p + tq` over the polynomial ring `k[t]`. -/
noncomputable def cubicPencil (p q : MvPolynomial (Fin 4) k) :
    MvPolynomial (Fin 4) (Polynomial k) :=
  MvPolynomial.C (1 - Polynomial.X) * p.map Polynomial.C +
    MvPolynomial.C Polynomial.X * q.map Polynomial.C

/-- A pencil between homogeneous cubics is a homogeneous cubic over `k[t]`. -/
theorem cubicPencil_isHomogeneous
    {p q : MvPolynomial (Fin 4) k}
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) :
    (cubicPencil p q).IsHomogeneous 3 := by
  exact (hp.map Polynomial.C).C_mul (1 - Polynomial.X) |>.add
    ((hq.map Polynomial.C).C_mul Polynomial.X)

/-- Specializing the pencil parameter gives the expected linear combination. -/
theorem cubicPencil_map_eval (p q : MvPolynomial (Fin 4) k) (a : k) :
    (cubicPencil p q).map (Polynomial.evalRingHom a) =
      MvPolynomial.C (1 - a) * p + MvPolynomial.C a * q := by
  have hcomp : (Polynomial.evalRingHom a).comp Polynomial.C = RingHom.id k := by
    ext r
    simp
  simp [cubicPencil, MvPolynomial.map_map, hcomp]
  rw [MvPolynomial.map_id, MvPolynomial.map_id]

@[simp] theorem cubicPencil_map_eval_zero (p q : MvPolynomial (Fin 4) k) :
    (cubicPencil p q).map (Polynomial.evalRingHom 0) = p := by
  simpa using cubicPencil_map_eval p q 0

@[simp] theorem cubicPencil_map_eval_one (p q : MvPolynomial (Fin 4) k) :
    (cubicPencil p q).map (Polynomial.evalRingHom 1) = q := by
  simpa using cubicPencil_map_eval p q 1

/-- If the endpoint equation is nonzero, then so is the entire pencil. -/
theorem cubicPencil_ne_zero_of_right {p q : MvPolynomial (Fin 4) k}
    (hq : q ≠ 0) : cubicPencil p q ≠ 0 := by
  intro h
  have hm := congrArg (MvPolynomial.map (Polynomial.evalRingHom 1)) h
  apply hq
  simpa using hm

/-- The generic equation remains nonzero in the fraction field of `k[t]`. -/
theorem cubicPencil_generic_ne_zero {p q : MvPolynomial (Fin 4) k}
    (hq : q ≠ 0) :
    (cubicPencil p q).map
      (algebraMap (Polynomial k) (FractionRing (Polynomial k))) ≠ 0 := by
  intro hmap
  apply cubicPencil_ne_zero_of_right hq
  apply MvPolynomial.map_injective
    (f := algebraMap (Polynomial k) (FractionRing (Polynomial k)))
    (FaithfulSMul.algebraMap_injective (Polynomial k) (FractionRing (Polynomial k)))
  simpa using hmap

end AllCharacteristics
