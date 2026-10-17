import PfaffianDescent.VoisinStandardFourLineWitness
import PfaffianDescent.VoisinQuadraticUniversalIntersectionFamily
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Generic finiteness for the unrestricted quadratic system

The explicit regular split pair provides a finite witness in the full space
of quadratic equations. Proper generic transfer then gives finiteness near
the generic parameter of that complete linear system.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial Module AllCharacteristics.HomogeneousProjective

universe u

variable {L : Type u} [Field L] [CharZero L]

private noncomputable def fullQuadraticBasis :
    Basis (Fin (Module.finrank L (homogeneousSubmodule (Fin 4) L 2))) L
      (homogeneousSubmodule (Fin 4) L 2) :=
  Module.finBasis L (homogeneousSubmodule (Fin 4) L 2)

private noncomputable def fullQuadraticFrame :
    Fin (Module.finrank L (homogeneousSubmodule (Fin 4) L 2)) →
      homogeneousSubmodule (Fin 4) L 2 :=
  fullQuadraticBasis

private theorem fullQuadraticFrame_specializes_to
    (r : MvPolynomial (Fin 4) L) (hr : r.IsHomogeneous 2) :
    let t := (fullQuadraticBasis (L := L)).repr
      (⟨r, hr⟩ : homogeneousSubmodule (Fin 4) L 2)
    (cubicTwoQuadricUniversalQuadric (fullQuadraticFrame (L := L))).map
      (MvPolynomial.eval₂Hom (RingHom.id L) t) = r := by
  dsimp only
  rw [cubicTwoQuadricUniversalQuadric_map]
  simp only [MvPolynomial.map_id]
  have hrepr := (fullQuadraticBasis (L := L)).sum_repr
    (⟨r, hr⟩ : homogeneousSubmodule (Fin 4) L 2)
  have hval := congrArg Subtype.val hrepr
  simp only [Submodule.coe_sum, Submodule.coe_smul,
    MvPolynomial.smul_eq_C_mul] at hval
  exact hval

/-- For a smooth cubic, some first quadric makes the full unrestricted
moving-quadric family finite near its generic parameter. -/
theorem exists_first_quadric_fullQuadraticFamily_genericFiniteNeighborhood
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (q : MvPolynomial (Fin 4) L) (hq : q.IsHomogeneous 2),
      q ≠ 0 ∧ IsRelPrime p q ∧
      ∃ V : (Spec (.of (MvPolynomial
          (Fin (Module.finrank L (homogeneousSubmodule (Fin 4) L 2))) L))).Opens,
        genericPoint (Spec (.of (MvPolynomial
          (Fin (Module.finrank L (homogeneousSubmodule (Fin 4) L 2))) L))) ∈ V ∧
        IsFinite ((cubicTwoQuadricUniversalIntersectionToCone p q hp hq
          (fullQuadraticFrame (L := L))) ∣_ V) := by
  obtain ⟨q, r, hq, hr, hq0, _, hrel, hregular⟩ :=
    exists_split_quadric_pair_regular_relprime_over_charZero_of_smooth p hp hp0
  refine ⟨q, hq, hq0, hrel, ?_⟩
  let t := (fullQuadraticBasis (L := L)).repr
    (⟨r, hr⟩ : homogeneousSubmodule (Fin 4) L 2)
  have hspec :
      (cubicTwoQuadricUniversalQuadric (fullQuadraticFrame (L := L))).map
        (MvPolynomial.eval₂Hom (RingHom.id L) t) = r :=
    fullQuadraticFrame_specializes_to r hr
  apply cubicTwoQuadricUniversalIntersection_exists_genericFiniteNeighborhood_of_regularSpecialization
    (RingHom.id L) p q hp hq (fullQuadraticFrame (L := L)) t
  · simpa only [MvPolynomial.map_id] using hp0
  · simpa only [MvPolynomial.map_id] using hq0
  · simpa only [MvPolynomial.map_id] using hrel
  · intro F hF
    rw [hspec] at hF
    simpa only [MvPolynomial.map_id] using
      (hregular F (by simpa only [MvPolynomial.map_id] using hF))

end PfaffianDescent
