import AllCharacteristics.HomogeneousProjective

/-!
# Universal homogeneous equations and their projective families

A coefficient variable is assigned to each monomial of the prescribed degree.
Specializing those coefficient variables to the coefficients of any homogeneous
polynomial recovers that polynomial exactly, over every commutative ring.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace UniversalHomogeneous
universe u v
variable (σ : Type) (d : ℕ)

/-- The monomials of the prescribed degree in the chosen variables. -/
abbrev Monomials := {m : σ →₀ ℕ // m.degree = d}

/-- There are finitely many monomials of a fixed degree in finitely many
variables. -/
noncomputable instance monomialsFintype [Finite σ] : Fintype (Monomials σ d) :=
  (Finsupp.finite_of_degree_eq (σ := σ) d).fintype

/-- The coefficient ring of the universal homogeneous equation. -/
abbrev Coefficients (R : Type u) [CommRing R] := MvPolynomial (Monomials σ d) R

/-- The universal form, with one independent coefficient for each monomial. -/
noncomputable def form (R : Type u) [CommRing R] [Finite σ] :
    MvPolynomial σ (Coefficients σ d R) :=
  ∑ m : Monomials σ d, MvPolynomial.monomial m.1 (MvPolynomial.X m)

/-- The universal equation is homogeneous of its specified degree. -/
theorem form_isHomogeneous (R : Type u) [CommRing R] [Finite σ] :
    (form σ d R).IsHomogeneous d := by
  apply MvPolynomial.IsHomogeneous.sum
  intro m _
  exact MvPolynomial.isHomogeneous_monomial (MvPolynomial.X m) m.2

variable {σ d}

/-- A homogeneous form is recovered by assigning its coefficients to the
universal coefficient variables. -/
theorem map_form_eq {B : Type v} {R : Type u} [CommRing B] [CommRing R] [Finite σ]
    (f : B →+* R) (p : MvPolynomial σ R) (hp : p.IsHomogeneous d) :
    MvPolynomial.map (MvPolynomial.eval₂Hom f (fun m : Monomials σ d ↦ p.coeff m.1))
      (form σ d B) = p := by
  classical
  ext m
  simp only [form, map_sum, MvPolynomial.map_monomial, MvPolynomial.eval₂Hom_X',
    MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hm : m.degree = d
  · let j : Monomials σ d := ⟨m, hm⟩
    have hj : j.1 = m := rfl
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i _ hij
      have him : m ≠ i.1 := by
        intro h
        exact hij (Subtype.ext (h.symm.trans hj.symm))
      simp [Ne.symm him]
    · intro h
      exact (h (Finset.mem_univ j)).elim
  · rw [hp.coeff_eq_zero hm]
    apply Finset.sum_eq_zero
    intro i _
    have hmi : m ≠ i.1 := by
      intro h
      exact hm (h ▸ i.2)
    simp [Ne.symm hmi]

/-- A homogeneous form is the sum of its monomials of the prescribed degree. -/
theorem sum_monomial_coeff_eq {R : Type u} [CommRing R] [Finite σ]
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d) :
    (∑ m : Monomials σ d, MvPolynomial.monomial m.1 (p.coeff m.1)) = p := by
  simpa only [form, map_sum, MvPolynomial.map_monomial, MvPolynomial.eval₂Hom_X'] using
    map_form_eq (RingHom.id R) p hp

/-- Homogeneous equations lift through any surjective map of coefficient rings,
with their degree preserved. This is the equation-lifting step for a cubic over
a residue field, independently of the subsequent flatness and smoothness proofs. -/
theorem exists_homogeneous_lift {B : Type v} {R : Type u} [CommRing B] [CommRing R] [Finite σ]
    (f : B →+* R) (hf : Function.Surjective f)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d) :
    ∃ q : MvPolynomial σ B, q.IsHomogeneous d ∧ MvPolynomial.map f q = p := by
  classical
  choose c hc using fun m : Monomials σ d ↦ hf (p.coeff m.1)
  refine ⟨∑ m : Monomials σ d, MvPolynomial.monomial m.1 (c m), ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro m _
    exact MvPolynomial.isHomogeneous_monomial (c m) m.2
  · simp only [map_sum, MvPolynomial.map_monomial, hc]
    exact sum_monomial_coeff_eq p hp

/-- The actual projective family of all homogeneous equations with the chosen
degree and number of variables. -/
noncomputable def family (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ) :
    Scheme.{u} :=
  HomogeneousProjective.hypersurface (form σ d R) (form_isHomogeneous σ d R)

/-- The universal family maps to its affine coefficient scheme. -/
noncomputable def familyToCoefficients (R : Type u) [CommRing R]
    (σ : Type) [Finite σ] (d : ℕ) :
    family R σ d ⟶ Spec (.of (Coefficients σ d R)) :=
  HomogeneousProjective.hypersurfaceToBase (form σ d R) (form_isHomogeneous σ d R)

/-- The universal projective family is proper over its coefficient scheme. -/
instance isProper_familyToCoefficients (R : Type u) [CommRing R]
    (σ : Type) [Finite σ] (d : ℕ) : IsProper (familyToCoefficients R σ d) :=
  HomogeneousProjective.isProper_hypersurfaceToBase _ _

end UniversalHomogeneous
end AllCharacteristics
