import PfaffianDescent.VoisinFourLineFiniteWithoutSeparability
import PfaffianDescent.VoisinQuadraticUniversalIntersectionFamily

/-!
# From a split four-line witness to generic finiteness

This combines the four-line regularity argument with the actual universal
projective intersection family. The four cubic restrictions need only be
nonzero; repeated roots are permitted.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]

/-- If one member of the quadratic linear system splits into four genuine
line sections not contained in the cubic, the full cubic--quadric--
quadric family is finite near its generic quadratic parameter. -/
theorem cubicTwoQuadricUniversalIntersection_exists_genericFiniteNeighborhood_of_fourNonzeroLineSections
    {n : ℕ}
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (v₀ : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (t : Fin n → K)
    (hrspec : (cubicTwoQuadricUniversalQuadric v₀).map
      (MvPolynomial.eval₂Hom (RingHom.id K) t) = r)
    (hr : r.IsHomogeneous 2)
    (c : Cubic L 4) (hc : c.toMvPolynomial = p.map (algebraMap K L))
    (l m : Fin 2 → MvPolynomial (Fin 4) L)
    (hl : ∀ i, (l i).IsHomogeneous 1)
    (hm : ∀ i, (m i).IsHomogeneous 1)
    (hqfactor : q.map (algebraMap K L) = l 0 * l 1)
    (hrfactor : r.map (algebraMap K L) = m 0 * m 1)
    (u w : Fin 2 → Fin 2 → Vec L 4)
    (hu : ∀ i j, c.eval (u i j) ≠ 0)
    (huw : ∀ i j (t : L), t • u i j + w i j ≠ 0)
    (hlroots : ∀ i j, (l i).eval (u i j) = 0 ∧
      (l i).eval (w i j) = 0)
    (hmroots : ∀ i j, (m j).eval (u i j) = 0 ∧
      (m j).eval (w i j) = 0)
    (hparam : ∀ i j (y : Fin 4 → L),
      (l i).eval y = 0 → (m j).eval y = 0 →
      ∃ s a : L, y = s • u i j + a • w i j) :
    ∃ V : (Spec (.of (MvPolynomial (Fin n) K))).Opens,
      genericPoint (Spec (.of (MvPolynomial (Fin n) K))) ∈ V ∧
      IsFinite ((cubicTwoQuadricUniversalIntersectionToCone p q hp hq v₀) ∣_ V) := by
  have hregular :=
    cubic_two_quadric_regular_descends_from_four_nonzero_line_sections
      p q r hp hq hr c hc l m hl hm
      hqfactor hrfactor u w hu huw hlroots hmroots hparam
  apply cubicTwoQuadricUniversalIntersection_exists_genericFiniteNeighborhood_of_regularSpecialization
    (RingHom.id K) p q hp hq v₀ t
  · simpa only [MvPolynomial.map_id] using hp0
  · simpa only [MvPolynomial.map_id] using hq0
  · simpa only [MvPolynomial.map_id] using hrel
  · intro x hx
    rw [hrspec] at hx
    simpa only [MvPolynomial.map_id] using
      (hregular x (by simpa only [MvPolynomial.map_id] using hx))

end PfaffianDescent
