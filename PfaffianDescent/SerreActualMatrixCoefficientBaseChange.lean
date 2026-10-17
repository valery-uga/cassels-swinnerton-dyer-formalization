import Mathlib.Data.Matrix.Mul

namespace PfaffianDescent
universe u v w z

/-- Change the coefficient map before specializing to scheme modules.  Keeping
this equality transport abstract avoids expanding their dependent definitions. -/
theorem serreActualMatrixCoefficientComparison_changeBase
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {ι : Type w} {κ : Type z} [Fintype κ]
    (M : Matrix ι κ R) (old : κ → S) (new : ι → S)
    (φ ψ : R →+* S) (h : φ = ψ)
    (hc : ∃ a : S, IsUnit a ∧ ∀ i, new i = a * ((M.map φ).mulVec old) i) :
    ∃ a : S, IsUnit a ∧ ∀ i, new i = a * ((M.map ψ).mulVec old) i := by
  subst ψ
  exact hc

end PfaffianDescent
