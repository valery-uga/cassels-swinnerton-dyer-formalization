import PfaffianDescent.CorayComponentHilbertCoefficientInvariance
import PfaffianDescent.CorayCoefficientPrimeTransitivity
import PfaffianDescent.CorayActualMinimalPrimeSplitting
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Actual Galois/geometric minimal components have the SAME Hilbert function

The literal coefficient automorphism induces an actual quotient ring
isomorphism and an additive grade isomorphism. Its semilinear scalar relation
uses the original scalar structures, with no substituted action/dictionary.
Native rank invariance plus genuine finite-Galois prime transitivity gives
component Hilbert equality. Actual constructed simultaneous splitting and035
transport this equality to the actual algebraic-closure components.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private def actualCoefficientGradeAddEquiv
    {E : Type u} [Field E]
    (C D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
    (g : E ≃+* E)
    (hmap : C.toIdeal.map (MvPolynomial.map g.toRingHom) = D.toIdeal) (d : ℕ) :
    grading C d ≃+ grading D d := by
  let e := Ideal.quotientEquiv C.toIdeal D.toIdeal (MvPolynomial.mapEquiv (Fin 4) g) hmap.symm
  exact {
    toFun := fun x => ⟨e x.1, by
      obtain ⟨p, hp, hpx⟩ := x.2
      rw [← hpx]
      refine ⟨MvPolynomial.map g.toRingHom p, hp.map g.toRingHom, ?_⟩
      exact (Ideal.quotientEquiv_mk C.toIdeal D.toIdeal
        (MvPolynomial.mapEquiv (Fin 4) g) hmap.symm p).symm⟩
    invFun := fun y => ⟨e.symm y.1, by
      obtain ⟨p, hp, hpy⟩ := y.2
      rw [← hpy]
      refine ⟨MvPolynomial.map g.symm.toRingHom p, hp.map g.symm.toRingHom, ?_⟩
      have hm := Ideal.quotientEquiv_symm_mk C.toIdeal D.toIdeal
        (MvPolynomial.mapEquiv (Fin 4) g) hmap.symm p
      rw [MvPolynomial.mapEquiv_symm] at hm
      exact hm.symm⟩
    left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
    right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
    map_add' := fun x y => Subtype.ext (e.map_add x.1 y.1) }

/-- Literal coefficient automorphisms preserve ACTUAL coordinate Hilbert
values, using the original standard scalar structures on both grades. -/
theorem actualComponentGrade_finrank_eq_coefficientRingEquiv
    {E : Type u} [Field E]
    (C D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
    (g : E ≃+* E)
    (hmap : C.toIdeal.map (MvPolynomial.map g.toRingHom) = D.toIdeal) (d : ℕ) :
    finrank E (grading C d) = finrank E (grading D d) := by
  let e := Ideal.quotientEquiv C.toIdeal D.toIdeal (MvPolynomial.mapEquiv (Fin 4) g) hmap.symm
  let j := actualCoefficientGradeAddEquiv C D g hmap d
  have hmk (p : MvPolynomial (Fin 4) E) :
      e (Ideal.Quotient.mk C.toIdeal p) =
        Ideal.Quotient.mk D.toIdeal (MvPolynomial.map g.toRingHom p) :=
    Ideal.quotientEquiv_mk C.toIdeal D.toIdeal (MvPolynomial.mapEquiv (Fin 4) g) hmap.symm p
  have hscalar (r : E) (x : grading C d) : j (r • x) = g r • j x := by
    apply Subtype.ext
    change e (r • x.1) = g r • e x.1
    obtain ⟨p, _hp, hpx⟩ := x.2
    have hsrc : r • x.1 = Ideal.Quotient.mk C.toIdeal (r • p) := by
      calc
        _ = r • Ideal.Quotient.mk C.toIdeal p := congrArg (r • ·) hpx.symm
        _ = Ideal.Quotient.mk C.toIdeal (r • p) :=
          (map_smul (Ideal.Quotient.mkₐ E C.toIdeal) r p).symm
    have hpoly : MvPolynomial.map g.toRingHom (r • p) =
        g r • MvPolynomial.map g.toRingHom p := by
      simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
      rfl
    calc
      e (r • x.1) = e (Ideal.Quotient.mk C.toIdeal (r • p)) := congrArg e hsrc
      _ = Ideal.Quotient.mk D.toIdeal (MvPolynomial.map g.toRingHom (r • p)) := hmk (r • p)
      _ = Ideal.Quotient.mk D.toIdeal (g r • MvPolynomial.map g.toRingHom p) :=
        congrArg (Ideal.Quotient.mk D.toIdeal) hpoly
      _ = g r • Ideal.Quotient.mk D.toIdeal (MvPolynomial.map g.toRingHom p) :=
        map_smul (Ideal.Quotient.mkₐ E D.toIdeal) (g r) (MvPolynomial.map g.toRingHom p)
      _ = g r • e (Ideal.Quotient.mk C.toIdeal p) := congrArg (g r • ·) (hmk p).symm
      _ = g r • e x.1 := congrArg (fun y => g r • e y) hpx
  have hrank : Module.rank E (grading C d) = Module.rank E (grading D d) :=
    rank_eq_of_equiv_equiv g j g.bijective hscalar
  exact congrArg Cardinal.toNat hrank

/-- Actual finite-Galois minimal primes over an ORIGINAL prime have equal
Hilbert functions. Conjugacy is derived from native coefficient invariants and
actual contraction, rather than being a common-degree hypothesis. -/
theorem originalPrimeExtension_minimalComponents_hilbertFunction_eq
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (C D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
    (hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K E))).toIdeal.minimalPrimes)
    (hD : D.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K E))).toIdeal.minimalPrimes)
    (d : ℕ) : finrank E (grading C d) = finrank E (grading D d) := by
  obtain ⟨g, hg⟩ := polynomialCoefficientExtension_minimalPrimes_conjugate
    I.toIdeal C.toIdeal D.toIdeal hC hD
  exact actualComponentGrade_finrank_eq_coefficientRingEquiv C D g.toRingEquiv hg.symm d

/-- The actual algebraic-closure minimal components of an ORIGINAL prime have
one SAME Hilbert function. The finite splitting field is constructed internally;
no finite-field count or supplied splitting/degree certificate stands for Ω. -/
theorem originalPrime_geometricMinimalComponents_hilbertFunction_eq
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [IsGalois K Ω]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (P Q : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Ω))
    (hP : P.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes)
    (hQ : Q.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes)
    (d : ℕ) : finrank Ω (grading P d) = finrank Ω (grading Q d) := by
  obtain ⟨L, e, he, hmap⟩ :=
    originalHomogeneousIdeal_exists_finiteGalois_minimalPrimeSplitting (Ω := Ω) I
  let C := P.comap (componentPolynomialCoefficientMap (algebraMap L Ω))
  let D := Q.comap (componentPolynomialCoefficientMap (algebraMap L Ω))
  have hCeq : C.toIdeal = (e ⟨P.toIdeal, hP⟩).1 := (he ⟨P.toIdeal, hP⟩).symm
  have hDeq : D.toIdeal = (e ⟨Q.toIdeal, hQ⟩).1 := (he ⟨Q.toIdeal, hQ⟩).symm
  have hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes :=
    hCeq.symm ▸ (e ⟨P.toIdeal, hP⟩).2
  have hD : D.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes :=
    hDeq.symm ▸ (e ⟨Q.toIdeal, hQ⟩).2
  have hCP : C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = P.toIdeal := by
    rw [hCeq]
    exact hmap ⟨P.toIdeal, hP⟩
  have hDQ : D.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = Q.toIdeal := by
    rw [hDeq]
    exact hmap ⟨Q.toIdeal, hQ⟩
  rw [actualComponentGrade_finrank_eq_coefficientExtension C P hCP d,
    actualComponentGrade_finrank_eq_coefficientExtension D Q hDQ d]
  exact originalPrimeExtension_minimalComponents_hilbertFunction_eq I C D hC hD d

end PfaffianDescent.Coray
