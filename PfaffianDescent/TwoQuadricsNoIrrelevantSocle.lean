import PfaffianDescent.TwoGeneratorKoszulShortExact
import PfaffianDescent.CoordinateRegularExt

/-!
# Saturation input for a regular pair of homogeneous quadrics

The quotient by a relatively prime pair of quadrics has no class killed by
all four homogeneous coordinates.  This is the two-equation analogue of the
complete-intersection socle calculation and supplies the saturation input for
passing from chartwise regularity back to a homogeneous ideal statement.
-/

namespace PfaffianDescent

open CategoryTheory Abelian MvPolynomial

section

variable {K : Type*} [Field K]

/-- A relatively prime pair of quadrics has no irrelevant coordinate socle. -/
theorem two_quadrics_no_irrelevant_annihilator
    (f g : MvPolynomial (Fin 4) K)
    (hf0 : f ≠ 0) (hrel : IsRelPrime f g)
    (x : MvPolynomial (Fin 4) K ⧸ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    (hx : ∀ r : Fin 4,
      Ideal.Quotient.mk (Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
        (MvPolynomial.X r) * x = 0) :
    x = 0 := by
  let R := MvPolynomial (Fin 4) K
  let J : Ideal R := MvPolynomial.idealOfVars (Fin 4) K
  let X := ModuleCat.of R (R ⧸ J)
  letI : Subsingleton (Ext X (ModuleCat.of R R) 2) :=
    coordinate_ext_subsingleton 2 (by omega)
  letI : Subsingleton (Ext X (ModuleCat.of R (R × R)) 1) :=
    coordinate_ext_subsingleton_pair 1 (by omega)
  letI : Subsingleton (Ext X (ModuleCat.of R R) 0) :=
    coordinate_ext_subsingleton 0 (by omega)
  apply twoGenerator_quotient_no_common_annihilator_of_ext_vanishing
    (J := J) hf0 hrel x
  intro z hz
  let φ : R →ₗ[R] R ⧸ Ideal.span ({f, g} : Set R) := {
    toFun := fun a => Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) a * x
    map_add' := by intro a b; rw [map_add, add_mul]
    map_smul' := by
      intro a b
      change Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) (a * b) * x =
        a * (Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) b * x)
      rw [map_mul]
      ring }
  have hφ : J ≤ LinearMap.ker φ := by
    change Ideal.span (Set.range (MvPolynomial.X : Fin 4 → R)) ≤ LinearMap.ker φ
    apply Ideal.span_le.mpr
    rintro _ ⟨r, rfl⟩
    exact hx r
  exact hφ hz

end

end PfaffianDescent
