import PfaffianDescent.VoisinHomogeneousIdealGenericSpreading

/-!
# Equations of a generic fixed curve on its contracted model

The contraction of a prime homogeneous curve ideal to an integral coefficient
ring is a model of the generic curve.  An individual equation of the generic
curve need not have coefficients in that ring.  Clearing its denominator does,
however, produce an equation *in the contracted ideal*, not merely an equation
whose generic image vanishes.  The same holds for a finite family of equations
with one denominator.  The last lemma records the resulting compatibility of
point evaluation under any further field extension.

This is an equation-level spreading result.  It does not assert that the
associated divisor class descends to a ground-field line bundle.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Clear the denominator of an equation in the generic fixed-curve ideal,
while retaining ideal membership in the contracted model. -/
theorem exists_denominator_clear_mem_homogeneousModel
    {A F : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (hcontract : ∀ g : MvPolynomial (Fin 4) A,
      g ∈ J.toIdeal ↔ MvPolynomial.map (algebraMap A F) g ∈ C.toIdeal)
    (q : MvPolynomial (Fin 4) F) (hq : q ∈ C.toIdeal) :
    ∃ (d : A) (g : MvPolynomial (Fin 4) A),
      d ≠ 0 ∧ g ∈ J.toIdeal ∧
        MvPolynomial.map (algebraMap A F) g =
          MvPolynomial.C (algebraMap A F d) * q := by
  obtain ⟨d, g, hd, hg⟩ :=
    exists_polynomial_denominator_clear (A := A) (F := F) q
  refine ⟨d, g, hd, ?_, hg⟩
  apply (hcontract g).mpr
  rw [hg]
  exact C.toIdeal.mul_mem_left _ hq

/-- The equation over the contracted model retains its homogeneous degree. -/
theorem exists_homogeneous_denominator_clear_mem_homogeneousModel
    {A F : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (hcontract : ∀ g : MvPolynomial (Fin 4) A,
      g ∈ J.toIdeal ↔ MvPolynomial.map (algebraMap A F) g ∈ C.toIdeal)
    (q : MvPolynomial (Fin 4) F) (n : ℕ)
    (hq : q ∈ C.toIdeal) (hdegree : q.IsHomogeneous n) :
    ∃ (d : A) (g : MvPolynomial (Fin 4) A),
      d ≠ 0 ∧ g ∈ J.toIdeal ∧ g.IsHomogeneous n ∧
        MvPolynomial.map (algebraMap A F) g =
          MvPolynomial.C (algebraMap A F d) * q := by
  obtain ⟨d, g, hd, hmem, hg⟩ :=
    exists_denominator_clear_mem_homogeneousModel C J hcontract q hq
  exact ⟨d, g, hd, hmem,
    polynomial_denominator_clear_isHomogeneous q g d n hdegree hg, hg⟩

/-- A finite family of equations in the generic curve ideal has a common
denominator and equations in its contracted model. -/
theorem exists_finite_homogeneousModel_equations_common_denominator
    {A F : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    {ι : Type v} [DecidableEq ι]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (hcontract : ∀ g : MvPolynomial (Fin 4) A,
      g ∈ J.toIdeal ↔ MvPolynomial.map (algebraMap A F) g ∈ C.toIdeal)
    (s : Finset ι) (q : ι → MvPolynomial (Fin 4) F)
    (hq : ∀ i ∈ s, q i ∈ C.toIdeal) :
    ∃ d : A, d ≠ 0 ∧ ∀ i ∈ s,
      ∃ g : MvPolynomial (Fin 4) A,
        g ∈ J.toIdeal ∧
          MvPolynomial.map (algebraMap A F) g =
            MvPolynomial.C (algebraMap A F d) * q i := by
  obtain ⟨d, hd, hclear⟩ :=
    exists_finite_polynomials_common_denominator_clear
      (A := A) (F := F) s q
  refine ⟨d, hd, ?_⟩
  intro i hi
  obtain ⟨g, hg⟩ := hclear i hi
  refine ⟨g, ?_, hg⟩
  apply (hcontract g).mpr
  rw [hg]
  exact C.toIdeal.mul_mem_left _ (hq i hi)

/-- A prime fixed curve on a cubic over the function field admits one prime
projective model over the coefficient domain together with a simultaneous
homogeneous spread of any finite list of its equations.  The model includes
the cubic equation, has no vertical constant in its ideal, and has exactly
the prescribed generic homogeneous ideal. -/
theorem exists_prime_fixedCurve_model_with_finite_equation_spread
    {A F : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (p : MvPolynomial (Fin 4) A) (_hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hprime : C.toIdeal.IsPrime)
    (hpC : MvPolynomial.map (algebraMap A F) p ∈ C.toIdeal)
    {m n : ℕ} (q : Fin m → MvPolynomial (Fin 4) F)
    (hq : ∀ i, q i ∈ C.toIdeal)
    (hdegree : ∀ i, (q i).IsHomogeneous n) :
    ∃ (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
      (d : A) (g : Fin m → MvPolynomial (Fin 4) A),
      J.toIdeal.FG ∧ J.toIdeal.IsPrime ∧ p ∈ J.toIdeal ∧
        Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal = C.toIdeal ∧
        (∀ a : A, MvPolynomial.C a ∈ J.toIdeal → a = 0) ∧
        d ≠ 0 ∧
        ∀ i, g i ∈ J.toIdeal ∧ (g i).IsHomogeneous n ∧
          MvPolynomial.map (algebraMap A F) (g i) =
            MvPolynomial.C (algebraMap A F d) * q i := by
  classical
  obtain ⟨J, hfg, hprimeJ, hmap, hcontract, hconstant⟩ :=
    exists_primeHomogeneousIdeal_spread_of_fractionField
      (A := A) (F := F) C hprime
  have hqfin : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      q i ∈ C.toIdeal := by
    intro i _
    exact hq i
  obtain ⟨d, hd, hclear⟩ :=
    exists_finite_homogeneousModel_equations_common_denominator
      (A := A) (F := F) (ι := Fin m)
      C J hcontract (Finset.univ : Finset (Fin m)) q hqfin
  let g : Fin m → MvPolynomial (Fin 4) A :=
    fun i => Classical.choose (hclear i (Finset.mem_univ i))
  refine ⟨J, d, g, hfg, hprimeJ, (hcontract p).mpr hpC,
    hmap, hconstant, hd, ?_⟩
  intro i
  obtain ⟨hmem, hgi⟩ :=
    Classical.choose_spec (hclear i (Finset.mem_univ i))
  exact ⟨hmem,
    polynomial_denominator_clear_isHomogeneous
      (q i) (g i) d n (hdegree i) hgi, hgi⟩

/-- Clearing an equation's denominator commutes with evaluation at any
field-valued point after extending coefficients from the fraction field. -/
theorem denominator_cleared_equation_evaluation
    {A F L : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
    (q : MvPolynomial (Fin 4) F)
    (d : A) (g : MvPolynomial (Fin 4) A)
    (hclear : MvPolynomial.map (algebraMap A F) g =
      MvPolynomial.C (algebraMap A F d) * q)
    (x : Fin 4 → L) :
    g.eval₂ (algebraMap A L) x =
      algebraMap A L d * q.eval₂ (algebraMap F L) x := by
  have heval := congrArg
    (fun r : MvPolynomial (Fin 4) F =>
      r.eval₂ (algebraMap F L) x) hclear
  have hcoeff : (algebraMap F L) ((algebraMap A F) d) =
      (algebraMap A L) d := by
    rw [IsScalarTower.algebraMap_eq A F L]
    rfl
  simpa only [MvPolynomial.eval₂_map, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, ← IsScalarTower.algebraMap_eq A F L,
    hcoeff] using heval

/-- In particular, a generic fixed-curve equation vanishing at a marked
field-valued point yields a vanishing equation in the contracted model. -/
theorem denominator_cleared_equation_evaluation_eq_zero
    {A F L : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
    (q : MvPolynomial (Fin 4) F)
    (d : A) (g : MvPolynomial (Fin 4) A)
    (hclear : MvPolynomial.map (algebraMap A F) g =
      MvPolynomial.C (algebraMap A F d) * q)
    (x : Fin 4 → L)
    (hzero : q.eval₂ (algebraMap F L) x = 0) :
    g.eval₂ (algebraMap A L) x = 0 := by
  rw [denominator_cleared_equation_evaluation q d g hclear x, hzero, mul_zero]

end PfaffianDescent
