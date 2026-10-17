import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Detecting an irrelevant socle by a quotient-module Hom group

The degree-zero end of the complete-intersection Ext calculation is an
ordinary module Hom group.  These lemmas make explicit how its vanishing
rules out elements annihilated by an ideal, and then by a set of generators
of that ideal.
-/

namespace PfaffianDescent

open CategoryTheory

section

variable {R : Type*} [CommRing R]

/-- If every map from `R/J` to `R/I` is zero, no nonzero class of `R/I` is
annihilated by all elements of `J`. -/
lemma quotient_no_common_annihilator_of_hom_subsingleton {I J : Ideal R}
    (hHom : Subsingleton
      (ModuleCat.of R (R ⧸ J) ⟶ ModuleCat.of R (R ⧸ I)))
    (x : R ⧸ I)
    (hx : ∀ r ∈ J, Ideal.Quotient.mk I r * x = 0) :
    x = 0 := by
  let φ : R →ₗ[R] R ⧸ I := {
    toFun r := Ideal.Quotient.mk I r * x
    map_add' r s := by
      rw [map_add, add_mul]
    map_smul' r s := by
      change Ideal.Quotient.mk I (r * s) * x = r * (Ideal.Quotient.mk I s * x)
      rw [map_mul]
      ring
  }
  have hφ : J ≤ LinearMap.ker φ := by
    intro r hr
    change Ideal.Quotient.mk I r * x = 0
    exact hx r hr
  let ψ := J.liftQ φ hφ
  have hzero : ModuleCat.ofHom ψ = 0 := Subsingleton.elim _ _
  have hone := congrArg (fun e => e (Submodule.Quotient.mk (1 : R))) hzero
  change ψ (Submodule.Quotient.mk (1 : R)) = 0 at hone
  rw [Submodule.liftQ_apply] at hone
  change Ideal.Quotient.mk I 1 * x = 0 at hone
  simpa using hone

/-- The generator form of `quotient_no_common_annihilator_of_hom_subsingleton`.
It is the form used for the four homogeneous coordinates of projective
three-space. -/
lemma quotient_no_common_annihilator_of_span_hom_subsingleton
    {I : Ideal R} (s : Set R)
    (hHom : Subsingleton
      (ModuleCat.of R (R ⧸ Ideal.span s) ⟶ ModuleCat.of R (R ⧸ I)))
    (x : R ⧸ I)
    (hx : ∀ r ∈ s, Ideal.Quotient.mk I r * x = 0) :
    x = 0 := by
  apply quotient_no_common_annihilator_of_hom_subsingleton
    (I := I) (J := Ideal.span s) hHom x
  let φ : R →ₗ[R] R ⧸ I := {
    toFun r := Ideal.Quotient.mk I r * x
    map_add' r t := by
      rw [map_add, add_mul]
    map_smul' r t := by
      change Ideal.Quotient.mk I (r * t) * x = r * (Ideal.Quotient.mk I t * x)
      rw [map_mul]
      ring
  }
  let A : Ideal R := LinearMap.ker φ
  have hsA : s ⊆ A := by
    intro r hr
    change Ideal.Quotient.mk I r * x = 0
    exact hx r hr
  have hspan : Ideal.span s ≤ A := Ideal.span_le.mpr hsA
  intro r hr
  exact hspan hr

end

end PfaffianDescent
