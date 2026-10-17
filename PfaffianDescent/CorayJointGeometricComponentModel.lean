import PfaffianDescent.CorayAlgebraicClosureArbitraryPrimeTest
import PfaffianDescent.CorayStabilizerHomogeneousIdealDescent
import PfaffianDescent.CorayMinimalPrimeOrbitCount
import AllCharacteristics.ProjectiveBaseChange
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# One actual geometric component model: whole descent, field degree and all-field GI

Construct ONCE the finite Galois splitting field L, original geometric prime's
homogeneous component C, ACTUAL stabilizer fixed field M and whole contraction D.
The same witness has derived original-K field degree equal to the geometric
projective component count and native GeometricallyIntegral for all fields.
No unrelated existential witnesses or desired geometry/count certificates are
combined. SOURCE ONLY / UNVERIFIED: root owns compiler and deep audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Construct one actual model of an ORIGINAL geometric minimal prime.
That same L/C/M/D has literal whole-ideal descent, field degree over ORIGINAL K
identical to the ACTUAL geometric component count, and native all-field GI.
Every field T/M has prime literal extension and integral SAME reduced projective
scheme/native Cartesian pullback. No desired conclusion is a premise. -/
theorem originalGeometricMinimalPrime_exists_jointStabilizerModel
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsAlgClosed Ω]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (P : Ideal (MvPolynomial (Fin 4) Ω))
    (hP : P ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes) :
    ∃ (L : FiniteGaloisIntermediateField K Ω)
      (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L)),
      C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes ∧
        C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = P ∧
        let M := homogeneousIdealStabilizerFixedField (K := K) C
        let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
        D.toIdeal.IsPrime ∧
          D.toIdeal.map (MvPolynomial.map (algebraMap M L)) = C.toIdeal ∧
          Module.finrank K M = Nat.card (irreducibleComponents
            (scheme (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) ∧
          GeometricallyIntegral (toBase D) ∧
        ∀ (T : Type u) [Field T] [Algebra M T],
          let DT := D.map (componentPolynomialCoefficientMap (algebraMap M T))
          DT.toIdeal.IsPrime ∧ IsIntegral (scheme DT) ∧
            IsIntegral (CategoryTheory.Limits.pullback (toBase D)
              (Spec.map (CommRingCat.ofHom (algebraMap M T)))) := by
  classical
  obtain ⟨L, e, he, hmap⟩ := originalHomogeneousIdeal_exists_finiteGalois_minimalPrimeSplitting
    (Ω := Ω) I
  let JΩ := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
  let p := (⟨P, hP⟩ :
    (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes)
  let JL := I.map (componentPolynomialCoefficientMap (algebraMap K L))
  let C := (e p).1.homogeneousCore (homogeneousSubmodule (Fin 4) L)
  have hCeq : C.toIdeal = (e p).1 :=
    homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal JL (e p).1 (e p).2
  have hCmin : C.toIdeal ∈ JL.toIdeal.minimalPrimes := by
    rw [hCeq]
    exact (e p).2
  have hCext : C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = P := by
    rw [hCeq]
    exact hmap p
  letI : C.toIdeal.IsPrime := hCmin.1.1
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  have hdesc := homogeneousPrime_stabilizerFixedField_descends (K := K) C
  letI : D.toIdeal.IsPrime := hdesc.1
  have hDL : D.toIdeal.map (MvPolynomial.map (algebraMap M L)) = C.toIdeal := hdesc.2
  have hDLC : D.map (componentPolynomialCoefficientMap (algebraMap M L)) = C :=
    HomogeneousIdeal.ext hDL
  have hCrel := homogeneousCoefficientExtension_minimalPrime_relevant I hIrel C hCmin
  have hDrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) M) ≤ D := by
    intro hbad
    have hbadL := (irrelevant_le_map_ambientCoefficientGradedRingHom
      (σ := Fin 4) (algebraMap M L)).trans (HomogeneousIdeal.map_mono _ hbad)
    change HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) L) ≤
      D.map (componentPolynomialCoefficientMap (algebraMap M L)) at hbadL
    rw [hDLC] at hbadL
    exact hCrel hbadL
  letI aMΩ : Algebra M Ω := ((algebraMap L Ω).comp (algebraMap M L)).toAlgebra
  letI hKMΩ : IsScalarTower K M Ω := IsScalarTower.of_algebraMap_eq fun k => by
    change algebraMap K Ω k = algebraMap L Ω (algebraMap M L (algebraMap K M k))
    rw [← IsScalarTower.algebraMap_apply K M L, ← IsScalarTower.algebraMap_apply K L Ω]
  letI : Algebra.IsAlgebraic M Ω :=
    @Algebra.IsAlgebraic.tower_top K M Ω
      (inferInstance : Field K) (inferInstance : Field M) (inferInstance : Ring Ω)
      (inferInstance : Algebra K M) aMΩ (inferInstance : Algebra K Ω) hKMΩ
      (inferInstance : Algebra.IsAlgebraic K Ω)
  have hcomp : (MvPolynomial.map (σ := Fin 4) (algebraMap L Ω)).comp
      (MvPolynomial.map (algebraMap M L)) = MvPolynomial.map (algebraMap M Ω) := by
    apply RingHom.ext
    intro q
    change MvPolynomial.map (algebraMap L Ω) (MvPolynomial.map (algebraMap M L) q) =
      MvPolynomial.map ((algebraMap L Ω).comp (algebraMap M L)) q
    exact MvPolynomial.map_map _ _ _
  have hDΩ : D.toIdeal.map (MvPolynomial.map (algebraMap M Ω)) = P := by
    rw [← hcomp, ← Ideal.map_map, hDL, hCext]
  have hΩprime : (D.map (componentPolynomialCoefficientMap (algebraMap M Ω))).toIdeal.IsPrime := by
    change (D.toIdeal.map (MvPolynomial.map (algebraMap M Ω))).IsPrime
    rw [hDΩ]
    exact hP.1.1
  have hall : ∀ (T : Type u) [Field T] [Algebra M T],
      let DT := D.map (componentPolynomialCoefficientMap (algebraMap M T))
      DT.toIdeal.IsPrime ∧ IsIntegral (scheme DT) ∧
        IsIntegral (CategoryTheory.Limits.pullback (toBase D)
          (Spec.map (CommRingCat.ofHom (algebraMap M T)))) := by
    intro T _ _
    let DT := D.map (componentPolynomialCoefficientMap (algebraMap M T))
    have hTprime : DT.toIdeal.IsPrime :=
      polynomialCoefficientExtension_prime_of_algClosed_algebraicExtension
        (Ω := Ω) (T := T) D.toIdeal hΩprime
    letI : DT.toIdeal.IsPrime := hTprime
    have hTmin : DT.toIdeal ∈ DT.toIdeal.minimalPrimes := by
      simp only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]
    have hTrel := homogeneousCoefficientExtension_minimalPrime_relevant D hDrel DT hTmin
    have hint : IsIntegral (scheme DT) :=
      (homogeneousMinimalPrime_projective_reducedComponent DT DT hTmin hTrel).2.1
    letI : IsIntegral (scheme DT) := hint
    let eT := projectiveBaseChangeIso (algebraMap M T) D DT rfl
    exact ⟨hTprime, hint, IsIntegral.of_isIso eT.hom⟩
  have hGI : GeometricallyIntegral (toBase D) := by
    constructor
    refine (geometrically_iff_of_commRing
      (P := fun X => IsIntegral X) (R := ↥M) (f := toBase D)).mpr ?_
    intro T _ _ Y fst snd h
    letI : IsIntegral (CategoryTheory.Limits.pullback (toBase D)
        (Spec.map (CommRingCat.ofHom (algebraMap M T)))) := (hall T).2.2
    exact IsIntegral.of_isIso h.isoPullback.inv
  have hdegree : Module.finrank K M = Nat.card JL.toIdeal.minimalPrimes :=
    homogeneousMinimalPrime_stabilizerFixedField_finrank_eq_minimalPrimes_card
      I.toIdeal C hCmin
  have hsplitCard : Nat.card JL.toIdeal.minimalPrimes = Nat.card JΩ.toIdeal.minimalPrimes :=
    Nat.card_congr e.symm
  have hgeometricCard : Nat.card JΩ.toIdeal.minimalPrimes =
      Nat.card (irreducibleComponents (scheme JΩ)) :=
    Nat.card_congr (homogeneousCoefficientExtension_minimalPrimesEquivProjectiveComponents
      (E := Ω) I hIrel)
  exact ⟨L, C, hCmin, hCext, hdesc.1, hDL,
    hdegree.trans (hsplitCard.trans hgeometricCard), hGI, hall⟩

end PfaffianDescent.Coray
