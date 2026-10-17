import PfaffianDescent.CoraySimultaneousComponentFiniteGaloisDefinition
import PfaffianDescent.CorayPolynomialComponentContraction
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Actual minimal-prime splitting at a constructed finite Galois field

The field is constructed by accepted simultaneous whole-ideal definition.
Going down derives actual minimality of contractions; faithful flatness lifts
all base minimal primes, proving surjectivity. The literal coefficient map
and actual extension equalities prove injectivity. No component list, splitting
bijection, equal cardinality or GI certificate is supplied.
SOURCE ONLY / UNVERIFIED: root alone compiles and audits.
-/
noncomputable section
namespace PfaffianDescent.Coray
universe u v
variable {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal polynomial coefficient extension is faithfully flat, using the
actual native polynomial pushout of a faithfully flat field extension. -/
theorem polynomialCoefficientExtension_faithfullyFlat :
    (MvPolynomial.map (σ := Fin 4) (algebraMap K E)).FaithfullyFlat := by
  rw [← MvPolynomial.algebraMap_def, RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (IsBaseChange.equiv (Algebra.IsPushout.out
      (R := K) (S := MvPolynomial (Fin 4) K)
      (R' := E) (S' := MvPolynomial (Fin 4) E))).symm

/-- For an arbitrary original ideal, going down derives that contraction of
EVERY actual extended minimal prime is an actual original minimal prime.
The original ideal need not be prime; the contraction is not assumed minimal. -/
theorem polynomialCoefficientExtension_minimalPrime_comap_mem
    (I : Ideal (MvPolynomial (Fin 4) K))
    (P : Ideal (MvPolynomial (Fin 4) E))
    (hP : P ∈ (I.map (MvPolynomial.map (algebraMap K E))).minimalPrimes) :
    P.comap (MvPolynomial.map (algebraMap K E)) ∈ I.minimalPrimes := by
  letI : Algebra.HasGoingDown (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) E) :=
    polynomialCoefficientExtension_hasGoingDown (K := K) (E := E)
  letI : P.IsPrime := hP.1.1
  refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mp hP.1.2⟩, ?_⟩
  intro Q hQ hQP
  letI : Q.IsPrime := hQ.1
  obtain ⟨R, hRP, hRprime, hRover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le
      (p := Q) (q := P.under (MvPolynomial (Fin 4) K)) P hQP
  letI : R.IsPrime := hRprime
  letI : R.LiesOver Q := hRover
  have hIR : I.map (MvPolynomial.map (algebraMap K E)) ≤ R := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact hQ.2.trans (R.over_def Q).le
  have hPR : P ≤ R := hP.2 ⟨hRprime, hIR⟩ hRP
  have hRP_eq : R = P := le_antisymm hRP hPR
  change P.under (MvPolynomial (Fin 4) K) ≤ Q
  rw [← hRP_eq]
  exact (R.over_def Q).symm.le

/-- Construct one finite Galois L over ORIGINAL K and the ACTUAL equivalence
between all minimal primes over Ω and all minimal primes over L. Its forward
function is exactly contraction along the literal L-to-Ω coefficient map,
and every corresponding prime's literal coefficient extension is the original
Ω-prime. For Ω the actual algebraic closure this is the genuine splitting
correspondence; it is not an arbitrary finite-E count assumption. -/
theorem originalHomogeneousIdeal_exists_finiteGalois_minimalPrimeSplitting
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) :
    ∃ L : FiniteGaloisIntermediateField K Ω,
      let JΩ := HomogeneousIdeal.map
        (componentPolynomialCoefficientMap (algebraMap K Ω)) I
      let JL := HomogeneousIdeal.map
        (componentPolynomialCoefficientMap (algebraMap K L)) I
      ∃ e : JΩ.toIdeal.minimalPrimes ≃ JL.toIdeal.minimalPrimes,
        (∀ P, (e P).1 = P.1.comap (MvPolynomial.map (algebraMap L Ω))) ∧
          ∀ P, (e P).1.map (MvPolynomial.map (algebraMap L Ω)) = P.1 := by
  classical
  obtain ⟨L, hL⟩ :=
    originalHomogeneousIdeal_exists_simultaneousFiniteGalois_componentDefinitionField
      (Ω := Ω) I
  let f := MvPolynomial.map (σ := Fin 4) (algebraMap L Ω)
  let g := MvPolynomial.map (σ := Fin 4) (algebraMap K L)
  let k := MvPolynomial.map (σ := Fin 4) (algebraMap K Ω)
  let A := I.toIdeal.map g
  let B := I.toIdeal.map k
  have hcomp : f.comp g = k := by
    apply RingHom.ext
    intro p
    change MvPolynomial.map (algebraMap L Ω)
      (MvPolynomial.map (algebraMap K L) p) = MvPolynomial.map (algebraMap K Ω) p
    rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq K L Ω]
  have hAB : A.map f = B := by
    dsimp [A, B]
    rw [Ideal.map_map, hcomp]
  have hdesc : ∀ P ∈ B.minimalPrimes, (P.comap f).map f = P := by
    intro P hP
    obtain ⟨hCeq, _, hmap⟩ := hL P hP
    change ((P.homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin 4) Ω)).toIdeal.comap f).map f = P at hmap
    rw [hCeq] at hmap
    exact hmap
  have hmem : ∀ P ∈ B.minimalPrimes, P.comap f ∈ A.minimalPrimes := by
    intro P hP
    apply polynomialCoefficientExtension_minimalPrime_comap_mem (K := L) (E := Ω) A P
    change P ∈ (A.map f).minimalPrimes
    rw [hAB]
    exact hP
  let c : B.minimalPrimes → A.minimalPrimes := fun P => ⟨P.1.comap f, hmem P.1 P.2⟩
  have hinj : Function.Injective c := by
    intro P Q h
    apply Subtype.ext
    have hc : P.1.comap f = Q.1.comap f := congrArg Subtype.val h
    have hm := congrArg (Ideal.map f) hc
    rwa [hdesc P.1 P.2, hdesc Q.1 Q.2] at hm
  have hsurj : Function.Surjective c := by
    intro Q
    letI : Module.FaithfullyFlat (MvPolynomial (Fin 4) L) (MvPolynomial (Fin 4) Ω) :=
      RingHom.faithfullyFlat_algebraMap_iff.mp
        (show (algebraMap (MvPolynomial (Fin 4) L)
          (MvPolynomial (Fin 4) Ω)).FaithfullyFlat from
            polynomialCoefficientExtension_faithfullyFlat (K := L) (E := Ω))
    letI : Q.1.IsPrime := Q.2.1.1
    obtain ⟨R, hRprime, hRover⟩ :=
      Ideal.exists_isPrime_liesOver_of_faithfullyFlat
        (B := MvPolynomial (Fin 4) Ω) Q.1
    letI : R.IsPrime := hRprime
    letI : R.LiesOver Q.1 := hRover
    have hBR : B ≤ R := by
      rw [← hAB]
      apply Ideal.map_le_iff_le_comap.mpr
      exact Q.2.1.2.trans (R.over_def Q.1).le
    obtain ⟨P, hP, hPR⟩ := Ideal.exists_minimalPrimes_le hBR
    have hcQ : P.comap f ≤ Q.1 := by
      exact (Ideal.comap_mono (f := f) hPR).trans (R.over_def Q.1).symm.le
    have hQP : Q.1 ≤ P.comap f := Q.2.2 (hmem P hP).1 hcQ
    refine ⟨⟨P, hP⟩, Subtype.ext (le_antisymm hcQ hQP)⟩
  let e : B.minimalPrimes ≃ A.minimalPrimes := Equiv.ofBijective c ⟨hinj, hsurj⟩
  refine ⟨L, e, fun P => rfl, ?_⟩
  intro P
  exact hdesc P.1 P.2

end PfaffianDescent.Coray
