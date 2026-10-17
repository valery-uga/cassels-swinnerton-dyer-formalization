import AllCharacteristics.GradedCoefficientMap
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Homogeneous quotient pieces under surjective coefficient change

A surjective coefficient map lifts homogeneous representatives degree by
degree. In particular, the actual graded-piece map of a projective
coordinate quotient is surjective onto its residue-field fibre.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Taking a homogeneous component commutes with changing coefficients. -/
theorem homogeneousComponent_map
    {R S : Type u} {σ : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (p : MvPolynomial σ R) :
    (homogeneousComponent n p).map f = homogeneousComponent n (p.map f) := by
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

/-- A surjective map of coefficient rings induces a surjection on every
actual homogeneous component of the quotient coordinate algebra. -/
theorem coordinateCoefficientMap_grade_surjective_of_surjective
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hJC : J.toIdeal.map (MvPolynomial.map f) = C.toIdeal)
    (n : ℕ) :
    Function.Surjective
      (fun x : grading J n =>
        (⟨coordinateCoefficientMap f J C hJC (x : CoordinateRing J),
          coordinateCoefficientMap_mem f J C hJC x.2⟩ : grading C n)) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := y.2
  obtain ⟨q, hq⟩ := MvPolynomial.map_surjective f hf p
  let qn := homogeneousComponent n q
  have hqn : qn.IsHomogeneous n := homogeneousComponent_isHomogeneous n q
  let x : grading J n :=
    ⟨Ideal.Quotient.mk J.toIdeal qn, ⟨qn, hqn, rfl⟩⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change coordinateCoefficientMap f J C hJC (Ideal.Quotient.mk J.toIdeal qn) = y.1
  rw [coordinateCoefficientMap_mk]
  have hmap : qn.map f = p := by
    dsimp only [qn]
    rw [homogeneousComponent_map, hq, homogeneousComponent_eq_self hp]
  rw [hmap]
  exact hpy

/-- In particular, every homogeneous equation in the residue-field
fibre of a local coordinate model lifts to a homogeneous equation over
the local coefficient ring. -/
theorem coordinateCoefficientMap_grade_surjective_residueField
    {R : Type u} [CommRing R] [IsLocalRing R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (C : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (IsLocalRing.ResidueField R)))
    (hJC : J.toIdeal.map
      (MvPolynomial.map (algebraMap R (IsLocalRing.ResidueField R))) = C.toIdeal)
    (n : ℕ) :
    Function.Surjective
      (fun x : grading J n =>
        (⟨coordinateCoefficientMap
            (algebraMap R (IsLocalRing.ResidueField R)) J C hJC
              (x : CoordinateRing J),
          coordinateCoefficientMap_mem
            (algebraMap R (IsLocalRing.ResidueField R)) J C hJC x.2⟩ :
          grading C n)) :=
  coordinateCoefficientMap_grade_surjective_of_surjective
    (algebraMap R (IsLocalRing.ResidueField R))
    IsLocalRing.residue_surjective J C hJC n

end PfaffianDescent
