import PfaffianDescent.TripleQuadricsCubicFactor

/-!
A regular sequence of three polynomials in four variables has no element
of its quotient annihilated by every coordinate. The proof does not depend
on the degrees of the polynomials. This supplies saturation for the cubic
grid intersection as well as for the existing net of quadrics.
-/

namespace PfaffianDescent

open CategoryTheory Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective

variable {K : Type*} [Field K]

/-- Coordinate socle vanishing for a regular three-polynomial quotient. -/
theorem triple_polynomials_no_irrelevant_annihilator
    (f g h : MvPolynomial (Fin 4) K)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ a : MvPolynomial (Fin 4) K,
      h * a ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        a ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    (x : MvPolynomial (Fin 4) K ⧸
      Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)))
    (hx : ∀ r : Fin 4,
      Ideal.Quotient.mk (Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)))
        (MvPolynomial.X r) * x = 0) :
    x = 0 := by
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K)) 3) :=
    coordinate_ext_subsingleton 3 (by omega)
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K × MvPolynomial (Fin 4) K × MvPolynomial (Fin 4) K)) 2) :=
    coordinate_ext_subsingleton_triple 2 (by omega)
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K × MvPolynomial (Fin 4) K × MvPolynomial (Fin 4) K)) 1) :=
    coordinate_ext_subsingleton_triple 1 (by omega)
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K)) 0) :=
    coordinate_ext_subsingleton 0 (by omega)
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)))) 0) :=
    threeGenerator_quotient_ext_subsingleton hf0 hg0 hrel hregular
  have hHom : Subsingleton
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))) ⟶
        ModuleCat.of (MvPolynomial (Fin 4) K)
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)))) :=
    Ext.homEquiv₀.symm.injective.subsingleton
  apply quotient_no_common_annihilator_of_span_hom_subsingleton
    (I := Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)))
    (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K)) hHom x
  rintro r ⟨j, rfl⟩
  exact hx j

/-- The native homogeneous-coordinate form, with arbitrary degrees. -/
theorem triple_homogeneous_no_irrelevant_annihilator
    (f g h : MvPolynomial (Fin 4) K) {a b c : ℕ}
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ z : MvPolynomial (Fin 4) K,
      h * z ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        z ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    (x : CoordinateRing (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    (hx : ∀ r : Fin 4,
      coordinate (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) r * x = 0) :
    x = 0 := by
  exact triple_polynomials_no_irrelevant_annihilator f g h hf0 hg0 hrel hregular x hx

/-- Vanishing in every coordinate localization gives literal ideal membership
for any regular three-polynomial intersection. -/
theorem triple_polynomials_mem_of_coordinate_localization_eq_zero
    (F f g h : MvPolynomial (Fin 4) K)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ z : MvPolynomial (Fin 4) K,
      h * z ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        z ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    (hzero : ∀ r : Fin 4,
      algebraMap
        (MvPolynomial (Fin 4) K ⧸ Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)))
        (Localization (Submonoid.powers
          (Ideal.Quotient.mk (Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)))
            (MvPolynomial.X r))))
        (Ideal.Quotient.mk (Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K))) F) = 0) :
    F ∈ Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)) := by
  apply mem_of_coordinate_localization_eq_zero_of_no_irrelevant_annihilator
    (Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)))
    (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3) F
  · intro x hx0 hx1 hx2 hx3
    apply triple_polynomials_no_irrelevant_annihilator f g h hf0 hg0 hrel hregular x
    intro r
    fin_cases r
    · exact hx0
    · exact hx1
    · exact hx2
    · exact hx3
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hzero 0
    · exact hzero 1
    · exact hzero 2
    · exact hzero 3

end PfaffianDescent
