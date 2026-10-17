import PfaffianDescent.VoisinDegreeTenResidualEnd

/-!
# Homogeneous witnesses for the degree-eight fixed-curve obstruction

This separates the associated-prime extraction from the residual-cycle
construction.  The resulting homogeneous prime ideal is the algebraic form
of the prospective fixed curve in Voisin's argument.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Negating the no-fixed-curve assertion yields the literal associated-prime
witness: every admissible first quadric has an associated component containing
the entire quadratic vanishing system. -/
theorem degreeEight_exists_associatedPrime_commonCurveWitness_of_not_noCommonCurveComponent
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (h : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
      Function.Surjective
        (MvPolynomial.eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      ∀ (q : MvPolynomial (Fin 4) K) (_hq : q.IsHomogeneous 2),
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
        q ≠ 0 → IsRelPrime p q →
        let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
        let W := homogeneousVanishingPolynomialSubmodule
          (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2
        ∃ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
            (MvPolynomial (Fin 4) K ⧸ I),
          ∀ r ∈ W, Ideal.Quotient.mk I r ∈ P := by
  classical
  unfold DegreeEightQuadraticSystemHasNoCommonCurveComponent at h
  dsimp only at h
  push Not at h
  exact h

/-- Pulling an associated prime back along the quotient map produces an
ambient prime ideal containing the cubic--quadric ideal. -/
theorem associatedPrimeComap_isPrime_and_contains_span
    (p q : MvPolynomial (Fin 4) K)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸
      Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hP : P ∈ associatedPrimes
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤
      P.comap (Ideal.Quotient.mk
        (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))) ∧
    (P.comap (Ideal.Quotient.mk
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))))).IsPrime := by
  constructor
  · apply Ideal.le_comap_of_map_le
    rw [Ideal.map_quotient_self]
    exact bot_le
  · letI : P.IsPrime := hP.1
    exact Ideal.comap_isPrime _ P

omit [Infinite K] in
/-- A regular pair already proves that the quadratic system avoids every
associated component of the selected cubic--quadric curve. -/
theorem DegreeEightQuadraticSystemHasNoCommonCurveComponent.ofRegularPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hpair : DegreeEightRegularQuadricPairExists p hp D₈) :
    DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx
  obtain ⟨q, hq, hqvan, hq0, hrel, r, hr, hrvan, hregular⟩ := hpair x hx
  refine ⟨q, hq, hqvan, hq0, hrel, ?_⟩
  let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  let W := homogeneousVanishingPolynomialSubmodule
    (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2
  dsimp only
  intro P hP
  refine ⟨r, ?_, ?_⟩
  · exact (mem_homogeneousVanishingPolynomialSubmodule_iff
      (K := K) (A := Γ(D₈.val.subscheme, ⊤))
      (sigma := Fin 4) x 2 r).mpr ⟨hr, hrvan⟩
  · have hreg : Ideal.Quotient.mk I r ∈
        nonZeroDivisors (MvPolynomial (Fin 4) K ⧸ I) :=
      quotient_mk_mem_nonZeroDivisors_of_regular_mod_ideal I r hregular
    intro hrP
    have hunion : Ideal.Quotient.mk I r ∈
        ⋃ Q ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
          (MvPolynomial (Fin 4) K ⧸ I),
            (Q : Set (MvPolynomial (Fin 4) K ⧸ I)) :=
      Set.mem_iUnion₂.mpr ⟨P, hP, hrP⟩
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors] at hunion
    exact hunion hreg

/-- For the degree-eight quadratic system, Voisin's no-fixed-curve condition
is equivalent to the literal existence of a regular cubic--quadric--quadric
pair through the datum. -/
theorem degreeEightQuadraticSystem_hasNoCommonCurveComponent_iff_regularPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) :
    DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈ ↔
      DegreeEightRegularQuadricPairExists p hp D₈ := by
  constructor
  · exact DegreeEightQuadraticSystemHasNoCommonCurveComponent.regularPair p hp D₈
  · exact DegreeEightQuadraticSystemHasNoCommonCurveComponent.ofRegularPair p hp D₈

/-- The ambient associated-prime obstruction has a homogeneous prime
refinement that contains the cubic, the first quadric, and every homogeneous
quadric through the datum. -/
theorem degreeEight_exists_homogeneousPrimeCurveIdealWitness_of_not_noCommonCurveComponent
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (h : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
      Function.Surjective
        (MvPolynomial.eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      ∀ (q : MvPolynomial (Fin 4) K) (_hq : q.IsHomogeneous 2),
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
        q ≠ 0 → IsRelPrime p q →
        ∃ C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K),
          C.toIdeal.IsPrime ∧
          Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal ∧
          homogeneousVanishingPolynomialSubmodule
              (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
            Submodule.restrictScalars K C.toIdeal := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hx, hcommon⟩ :=
    degreeEight_exists_associatedPrime_commonCurveWitness_of_not_noCommonCurveComponent
      p hp D₈ h
  refine ⟨x, hx, ?_⟩
  intro q hq hqvan hq0 hrel
  obtain ⟨P, hP, hcontains⟩ := hcommon q hq hqvan hq0 hrel
  obtain ⟨hspan, hprime⟩ := associatedPrimeComap_isPrime_and_contains_span p q P hP
  let I := P.comap (Ideal.Quotient.mk
    (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))))
  let C := I.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  refine ⟨C, hprime.homogeneousCore, ?_, ?_⟩
  · have hpI : p ∈ I := hspan (Ideal.subset_span (by simp))
    have hqI : q ∈ I := hspan (Ideal.subset_span (by simp))
    have hpC : p ∈ C.toIdeal :=
      Ideal.mem_homogeneousCore_of_homogeneous_of_mem
        (SetLike.isHomogeneousElem_coe ⟨p, hp⟩) hpI
    have hqC : q ∈ C.toIdeal :=
      Ideal.mem_homogeneousCore_of_homogeneous_of_mem
        (SetLike.isHomogeneousElem_coe ⟨q, hq⟩) hqI
    rw [Ideal.span_le]
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with hr | hr
    · subst r
      exact hpC
    · subst r
      exact hqC
  · intro r hr
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (SetLike.isHomogeneousElem_coe ⟨r,
        (mem_homogeneousVanishingPolynomialSubmodule_iff
          (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 r).mp hr |>.1⟩)
    exact hcontains r hr

end PfaffianDescent
