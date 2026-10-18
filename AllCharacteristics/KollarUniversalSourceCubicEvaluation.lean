import AllCharacteristics.KollarUniversalSourceHomogeneousDominance
import PfaffianDescent.MultivariateCubic

/-! Exact coefficient compatibility between the descended cubic tensor and
the original homogeneous equation on the universal polynomial source. -/

namespace AllCharacteristics

universe u

theorem kollarUniversalLocalizedCoefficientMap_eq
    (k : Type u) [Field k] :
    kollarUniversalLocalizedCoefficientMap k =
      (MvPolynomial.C : FractionRing (MvPolynomial (Fin 3) k) →+*
        KollarUniversalLocalizedParameterRing k).comp
          (algebraMap k (FractionRing (MvPolynomial (Fin 3) k))) := by
  unfold kollarUniversalLocalizedCoefficientMap
  rw [IsScalarTower.algebraMap_eq k (MvPolynomial (Fin 3) k)
    (FractionRing (MvPolynomial (Fin 3) k)), MvPolynomial.algebraMap_eq]

/-- Coefficient extension of the actual localized coefficient map is the
coefficient map used by the raw secant polynomial. -/
theorem kollarUniversalLocalizedCoefficientMap_map
    {k L : Type u} [Field k] [CommRing L]
    (α : FractionRing (MvPolynomial (Fin 3) k) →+* L) :
    (MvPolynomial.map (σ := Fin 2 × Fin 3) α).comp
        (kollarUniversalLocalizedCoefficientMap k) =
      (MvPolynomial.C : L →+* MvPolynomial (Fin 2 × Fin 3) L).comp
        (α.comp (algebraMap k (FractionRing (MvPolynomial (Fin 3) k)))) := by
  rw [kollarUniversalLocalizedCoefficientMap_eq]
  apply RingHom.ext
  intro a
  exact MvPolynomial.map_C α _

/-- The descended tensor equation is precisely the original homogeneous
cubic equation evaluated through the actual localized coefficient map. -/
theorem kollarUniversalPolynomial_cubic_equation
    {k : Type u} [Field k] {n : ℕ}
    (c : PfaffianDescent.Cubic k n)
    (R : Fin n → KollarUniversalLocalizedParameterRing k)
    (hR : ((c.map (algebraMap k (FractionRing (MvPolynomial (Fin 3) k)))).map
      (MvPolynomial.C : FractionRing (MvPolynomial (Fin 3) k) →+*
        KollarUniversalLocalizedParameterRing k)).eval R = 0) :
    c.toMvPolynomial.eval₂ (kollarUniversalLocalizedCoefficientMap k) R = 0 := by
  rw [PfaffianDescent.Cubic.eval_toMvPolynomial,
    kollarUniversalLocalizedCoefficientMap_eq]
  exact hR

end AllCharacteristics
