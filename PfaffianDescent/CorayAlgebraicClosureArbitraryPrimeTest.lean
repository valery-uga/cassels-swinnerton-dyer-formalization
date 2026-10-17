import PfaffianDescent.CorayPolynomialQuotientArbitraryPrime
import PfaffianDescent.CorayActualMinimalPrimeSplitting
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Actual algebraic-closure prime test for arbitrary coefficient fields

Embed the ALGEBRAIC closed ambient field Ω/F into AlgebraicClosure T for ANY
field T/F. Derive both literal coefficient-map compositions, extend the actual
Ω-prime using the arbitrary-field tensor argument, and contract faithfully
flatly to T. SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
universe u v w
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Actual primeness after one algebraic algebraically closed ambient extension
implies primeness after EVERY field extension. T need not be algebraic.
The supplied closed-field primeness is the ordinary polynomial ideal input,
not a prime-extension or geometric-integrality conclusion for T. -/
theorem polynomialCoefficientExtension_prime_of_algClosed_algebraicExtension
    {F : Type u} {Ω : Type v} {T : Type w} [Field F] [Field Ω] [Field T]
    [Algebra F Ω] [Algebra F T] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω]
    (P : Ideal (MvPolynomial (Fin 4) F))
    (hΩ : (P.map (MvPolynomial.map (algebraMap F Ω))).IsPrime) :
    (P.map (MvPolynomial.map (algebraMap F T))).IsPrime := by
  let U := AlgebraicClosure T
  let f : Ω →ₐ[F] U := IsAlgClosed.lift
  letI : Algebra Ω U := f.toRingHom.toAlgebra
  let QΩ := P.map (MvPolynomial.map (algebraMap F Ω))
  let QT := P.map (MvPolynomial.map (algebraMap F T))
  let QU := P.map (MvPolynomial.map (algebraMap F U))
  letI : QΩ.IsPrime := hΩ
  have hΩcomp : (MvPolynomial.map (σ := Fin 4) (algebraMap Ω U)).comp
      (MvPolynomial.map (algebraMap F Ω)) = MvPolynomial.map (algebraMap F U) := by
    apply RingHom.ext
    intro q
    apply MvPolynomial.ext
    intro d
    simp only [RingHom.comp_apply, MvPolynomial.coeff_map]
    exact f.commutes (MvPolynomial.coeff d q)
  have hTcomp : (MvPolynomial.map (σ := Fin 4) (algebraMap T U)).comp
      (MvPolynomial.map (algebraMap F T)) = MvPolynomial.map (algebraMap F U) := by
    apply RingHom.ext
    intro q
    change MvPolynomial.map (algebraMap T U) (MvPolynomial.map (algebraMap F T) q) =
      MvPolynomial.map (algebraMap F U) q
    rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq F T U]
  have hΩmap : QΩ.map (MvPolynomial.map (algebraMap Ω U)) = QU := by
    dsimp [QΩ, QU]
    rw [Ideal.map_map, hΩcomp]
  have hTmap : QT.map (MvPolynomial.map (algebraMap T U)) = QU := by
    dsimp [QT, QU]
    rw [Ideal.map_map, hTcomp]
  have hUprime : QU.IsPrime := by
    rw [← hΩmap]
    exact algClosedPolynomialPrime_coefficientExtension_isPrime (T := U) QΩ
  letI : (QT.map (MvPolynomial.map (algebraMap T U))).IsPrime := by
    rw [hTmap]
    exact hUprime
  letI : Module.FaithfullyFlat (MvPolynomial (Fin 4) T) (MvPolynomial (Fin 4) U) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      (show (algebraMap (MvPolynomial (Fin 4) T)
        (MvPolynomial (Fin 4) U)).FaithfullyFlat from
          polynomialCoefficientExtension_faithfullyFlat (K := T) (E := U))
  have hcon : (QT.map (MvPolynomial.map (algebraMap T U))).comap
      (MvPolynomial.map (algebraMap T U)) = QT :=
    Ideal.comap_map_eq_self_of_faithfullyFlat QT
  change QT.IsPrime
  rw [← hcon]
  infer_instance

end PfaffianDescent.Coray
