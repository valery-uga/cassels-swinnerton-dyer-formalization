import PfaffianDescent.VoisinTwistCechNaturality

/-! # Actual twist multiplication on Laurent chart representatives -/
noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentLocalization TwistLaurent TwistCechTerms TwistCechTerms.GenericEvaluation
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
local notation "S" => MvPolynomial (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- Cross multiplication relates the actual chart trivializations before
and after homogeneous multiplication. -/
theorem chartAway_mulHomogeneous_cross
    (n : ℕ) (f : Fin (n + 1) → Fin 4) (m d : ℕ) (q : PS d)
    (i : Fin 4) (hdiv : MvPolynomial.X (R := K) i ∣ p3CechDenominator K n f)
    (s : Γ(sheafOfModules PS (m + d), cechBasicOpen K n f)) :
    (chartAway K n f m i hdiv ((mulHomogeneous PS q m).val.app
        (op (cechBasicOpen K n f)) s)).val *
      algebraMap S (Localization.Away (p3CechDenominator K n f))
        ((degreeOnePower PS (p3Coordinate K i) d : PS d) : S) =
    algebraMap S (Localization.Away (p3CechDenominator K n f)) (q : S) *
      (chartAway K n f (m + d) i hdiv s).val := by
  apply genericLocalizationMap_injective K n f
  rw [map_mul, map_mul, genericLocalizationMap_chartAway,
    genericLocalizationMap_chartAway, genericLocalizationMap_algebraMap,
    genericLocalizationMap_algebraMap]
  change algebraMap S (Fiber PS (p3GenericPoint K)) ((MvPolynomial.X i) ^ m) *
      (algebraMap S (Fiber PS (p3GenericPoint K)) (q : S) *
        s.1 (cechGenericPoint K n f)) *
      algebraMap S (Fiber PS (p3GenericPoint K)) ((MvPolynomial.X i) ^ d) =
    algebraMap S (Fiber PS (p3GenericPoint K)) (q : S) *
      (algebraMap S (Fiber PS (p3GenericPoint K)) ((MvPolynomial.X i) ^ (m + d)) *
        s.1 (cechGenericPoint K n f))
  rw [map_pow, map_pow, map_pow, pow_add]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The Laurent representative of ACTUAL sheaf multiplication is ordinary
multiplication by the polynomial Laurent image, with all twist shifts canceled. -/
theorem chartAway_mulHomogeneous_toLaurent
    (n : ℕ) (f : Fin (n + 1) → Fin 4) (m d : ℕ) (q : PS d)
    (i : Fin 4) (hdiv : MvPolynomial.X (R := K) i ∣ p3CechDenominator K n f)
    (s : Γ(sheafOfModules PS (m + d), cechBasicOpen K n f)) :
    awayToLaurent (K := K) n f
        (chartAway K n f m i hdiv ((mulHomogeneous PS q m).val.app
          (op (cechBasicOpen K n f)) s)) *
        AddMonoidAlgebra.single (twistShift m i) 1 =
    polynomialToLaurent (K := K) (q : S) *
      (awayToLaurent (K := K) n f (chartAway K n f (m + d) i hdiv s) *
        AddMonoidAlgebra.single (twistShift (m + d) i) 1) := by
  have h := congrArg (localizationAwayToLaurent (K := K) n f)
    (chartAway_mulHomogeneous_cross K n f m d q i hdiv s)
  simp only [map_mul, localizationAwayToLaurent_algebraMap,
    polynomialToLaurent_degreeOnePower] at h
  change awayToLaurent (K := K) n f
    (chartAway K n f m i hdiv ((mulHomogeneous PS q m).val.app
      (op (cechBasicOpen K n f)) s)) *
      AddMonoidAlgebra.single (positiveTwistShift d i) 1 =
    polynomialToLaurent (K := K) (q : S) *
      awayToLaurent (K := K) n f (chartAway K n f (m + d) i hdiv s) at h
  have hshift :
      (AddMonoidAlgebra.single (positiveTwistShift d i) 1 : LaurentLocalization.LaurentPolynomial K) *
        AddMonoidAlgebra.single (twistShift (m + d) i) 1 =
      AddMonoidAlgebra.single (twistShift m i) 1 := by
    rw [AddMonoidAlgebra.single_mul_single, one_mul]
    congr 1
    unfold positiveTwistShift twistShift
    rw [add_nsmul]
    abel
  rw [← hshift, ← mul_assoc, h, mul_assoc]

end PfaffianDescent.ProjectiveNegativeTwist
