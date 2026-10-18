import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
Normalize the two rank
interfaces needed for semilocal basis assembly: the quotient-field tensor
rank used by the native semilocal basis theorem, and the canonical localized
rank supplied by the local surface syzygy theorem.
-/
noncomputable section
namespace PfaffianDescent
open Module
open scoped TensorProduct
universe u v
set_option autoImplicit false

private theorem residueTensor_finrank_eq_localized_finrank001
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (P : Ideal R) [P.IsPrime] :
    Module.finrank P.ResidueField (P.ResidueField ⊗[R] M) =
      Module.finrank (Localization.AtPrime P) (LocalizedModule.AtPrime P M) := by
  exact Ideal.finrank_fiber_eq_rankAtStalk (M := M) P

/-- At a maximal ideal, tensor rank over the actual quotient field equals
the rank of the canonical localized module.  All residue-field and
localization comparisons are native; no rank equality is supplied. -/
theorem quotientTensor_finrank_eq_localized_finrank001
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (P : Ideal R) [P.IsMaximal] :
    Module.finrank (R ⧸ P) ((R ⧸ P) ⊗[R] M) =
      Module.finrank (Localization.AtPrime P) (LocalizedModule.AtPrime P M) := by
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  let K := R ⧸ P
  let L := P.ResidueField
  let e : L ⊗[K] (K ⊗[R] M) ≃ₗ[L] L ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L M
  calc
    Module.finrank K (K ⊗[R] M) =
        Module.finrank L (L ⊗[K] (K ⊗[R] M)) :=
      (show Module.finrank L (L ⊗[K] (K ⊗[R] M)) =
          Module.finrank K (K ⊗[R] M) from Module.finrank_baseChange).symm
    _ = Module.finrank L (L ⊗[R] M) := e.finrank_eq
    _ = Module.finrank (Localization.AtPrime P) (LocalizedModule.AtPrime P M) :=
      residueTensor_finrank_eq_localized_finrank001 R M P

/-- The exact semilocal basis consumer for an actual localized-kernel rank
theorem.  No quotient-tensor rank conversion remains a caller obligation. -/
theorem semilocal_nonempty_basis_of_localized_finrank001
    (R : Type u) [CommRing R] [Finite (MaximalSpectrum R)]
    (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M]
    (n : ℕ) (hrank : ∀ P : MaximalSpectrum R,
      Module.finrank (Localization.AtPrime P.asIdeal)
        (LocalizedModule.AtPrime P.asIdeal M) = n) :
    Nonempty (Basis (Fin n) R M) :=
  Module.nonempty_basis_of_flat_of_finrank_eq R M n (fun P =>
    (quotientTensor_finrank_eq_localized_finrank001 R M P.asIdeal).trans (hrank P))

end PfaffianDescent
end
