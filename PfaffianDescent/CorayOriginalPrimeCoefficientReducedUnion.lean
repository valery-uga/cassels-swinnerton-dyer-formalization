import PfaffianDescent.CorayPerfectAlgebraicScalarExtensionReduced
import PfaffianDescent.CorayWholeCoefficientQuotientTensor
import PfaffianDescent.CorayActualMinimalPrimeSplitting
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-! The actual coefficient extension of the original homogeneous prime is
its full finite minimal-component intersection, not merely the same support. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open scoped TensorProduct Classical
open AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

/-- The literal polynomial coefficient ideal of an original prime is radical
for an algebraic field extension of perfect K. Native whole quotient tensor
transport constructs reducedness, rather than assuming a reduced curve. -/
theorem polynomialPrime_perfectAlgebraicCoefficientExtension_isRadical001
    {K E : Type u} [Field K] [PerfectField K] [Field E] [Algebra K E]
    [Algebra.IsAlgebraic K E]
    (I : Ideal (MvPolynomial (Fin 4) K)) [I.IsPrime] :
    (I.map (MvPolynomial.map (algebraMap K E))).IsRadical := by
  let A := MvPolynomial (Fin 4) K ⧸ I
  letI : IsDomain A := (Ideal.Quotient.isDomain_iff_prime I).mpr inferInstance
  letI : IsReduced (E ⊗[K] A) :=
    perfectField_algebraicField_tensor_with_domain_isReduced001 K E A
  let e := wholeCoefficientQuotientTensorAlgEquiv (E := E) I
  apply (Ideal.isRadical_iff_quotient_reduced _).mpr
  exact isReduced_of_injective e.symm e.symm.injective

/-- Construct the entire finite family of actual homogeneous minimal primes
of I_E and prove its SCHEME-THEORETIC union is literally I_E. No radical,
intersection equality, reducedness or selected component is an input. -/
theorem originalHomogeneousPrime_perfectAlgebraicCoefficientExtension_eq_finiteMinimalComponentIntersection001
    {K E : Type u} [Field K] [PerfectField K] [Field E] [Algebra K E]
    [Algebra.IsAlgebraic K E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime] :
    let J := I.map (componentPolynomialCoefficientMap (algebraMap K E))
    let T := J.toIdeal.minimalPrimes
    letI : Finite T := (Ideal.finite_minimalPrimes_of_isNoetherianRing
      (MvPolynomial (Fin 4) E) J.toIdeal).to_subtype
    letI : Fintype T := Fintype.ofFinite T
    let f : T → HomogeneousIdeal (homogeneousSubmodule (Fin 4) E) :=
      fun Q => Q.1.homogeneousCore (homogeneousSubmodule (Fin 4) E)
    (Finset.univ.image f).inf id = J := by
  classical
  let J := I.map (componentPolynomialCoefficientMap (algebraMap K E))
  let T := J.toIdeal.minimalPrimes
  letI : Finite T := (Ideal.finite_minimalPrimes_of_isNoetherianRing
    (MvPolynomial (Fin 4) E) J.toIdeal).to_subtype
  letI : Fintype T := Fintype.ofFinite T
  let f : T → HomogeneousIdeal (homogeneousSubmodule (Fin 4) E) :=
    fun Q => Q.1.homogeneousCore (homogeneousSubmodule (Fin 4) E)
  let F := Finset.univ.image f
  have hCore (Q : T) : (f Q).toIdeal = Q.1 :=
    homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal J Q.1 Q.2
  have hMin : ∀ C ∈ F, C.toIdeal ∈ J.toIdeal.minimalPrimes := by
    intro C hC
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hC
    exact (hCore Q).symm ▸ Q.2
  have hRadical : J.toIdeal.IsRadical :=
    polynomialPrime_perfectAlgebraicCoefficientExtension_isRadical001 I.toIdeal
  have hInf : (F.inf id).toIdeal = F.inf (fun C => C.toIdeal) := by
    simp only [Finset.inf_eq_iInf, HomogeneousIdeal.toIdeal_iInf, id_eq]
  apply HomogeneousIdeal.ext
  change (F.inf id).toIdeal = J.toIdeal
  apply le_antisymm
  · rw [← hRadical.radical, ← Ideal.sInf_minimalPrimes]
    apply le_sInf
    intro Q hQ
    let q : T := ⟨Q, hQ⟩
    have hq : f q ∈ F := Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
    have hLe : F.inf (fun C => C.toIdeal) ≤ (f q).toIdeal := Finset.inf_le hq
    rw [hInf]
    exact hLe.trans_eq (hCore q)
  · rw [hInf]
    exact Finset.le_inf fun C hC => (hMin C hC).le

end PfaffianDescent.Coray
