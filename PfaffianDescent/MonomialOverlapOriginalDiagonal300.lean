import PfaffianDescent.NativeOpenTopInclusion300
import PfaffianDescent.MonomialOverlapDiagonalCoefficient300
import PfaffianDescent.MonomialTripleOriginalOpenDomain300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) (hk : B k = 0)

/-- The original diagonal determinant open is the entire ORIGINAL coefficient chart. -/
lemma monomialOverlapOriginalSelfOpen_eq_top300 :
    (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n B B k hk) :
      (Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n B k))).Opens) = ⊤ := by
  rw [universalMonomialOverlapDet_self300, PrimeSpectrum.basicOpen_one]

/-- Exact Scheme.GlueData.f_id for the SAME original open inclusion. -/
lemma monomialOverlapOriginalSelfInclusion_isIso300 :
    IsIso (monomialOverlapOriginalOpenInclusion300 R m n B B k hk) :=
  nativeOpenInclusion_isIso_of_eq_top300
    (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n B k)))
    (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n B B k hk))
    (monomialOverlapOriginalSelfOpen_eq_top300 R m n B k hk)

end PfaffianDescent
