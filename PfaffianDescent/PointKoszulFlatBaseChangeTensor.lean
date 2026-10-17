import PfaffianDescent.CubicPointTraceFieldBaseChangeLocalExt
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Canonical tensor coordinates for the actual Koszul scalar-extension functor -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TensorProduct
open scoped ChangeOfRings

universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def pointKoszulFlatBaseChangeFreeIso (φ : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} φ).obj (ModuleCat.of R R) ≅ ModuleCat.of S S := by
  letI : Algebra R S := φ.toAlgebra
  exact (AlgebraTensorModule.rid R S S).toModuleIso

theorem pointKoszulFlatBaseChangeFreeIso_tmul (φ : R →+* S) (s : S) (r : R) :
    (pointKoszulFlatBaseChangeFreeIso φ).hom (s ⊗ₜ[R,φ] r) = s * φ r := by
  change φ r * s = s * φ r
  exact mul_comm _ _

def pointKoszulFlatBaseChangePairIso (φ : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} φ).obj (ModuleCat.of R (R × R)) ≅
      ModuleCat.of S (S × S) := by
  letI : Algebra R S := φ.toAlgebra
  exact ((TensorProduct.prodRight R S S R R).trans
    ((AlgebraTensorModule.rid R S S).prodCongr
      (AlgebraTensorModule.rid R S S))).toModuleIso

theorem pointKoszulFlatBaseChangePairIso_tmul (φ : R →+* S) (s : S) (r : R × R) :
    (pointKoszulFlatBaseChangePairIso φ).hom (s ⊗ₜ[R,φ] r) =
      (s * φ r.1, s * φ r.2) := by
  letI : Algebra R S := φ.toAlgebra
  change ((TensorProduct.prodRight R S S R R).trans
    ((AlgebraTensorModule.rid R S S).prodCongr
      (AlgebraTensorModule.rid R S S))) (s ⊗ₜ[R] r) = _
  simp only [LinearEquiv.trans_apply, TensorProduct.prodRight_tmul,
    LinearEquiv.prodCongr_apply, AlgebraTensorModule.rid_tmul]
  change (φ r.1 * s, φ r.2 * s) = (s * φ r.1, s * φ r.2)
  simp only [mul_comm]

def pointKoszulFlatBaseChangeQuotientIso (φ : R →+* S) (I : Ideal R) :
    (ModuleCat.extendScalars.{u, u, u} φ).obj (ModuleCat.of R (R ⧸ I)) ≅
      ModuleCat.of S (S ⧸ I.map φ) := by
  letI : Algebra R S := φ.toAlgebra
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv.toModuleIso

theorem pointKoszulFlatBaseChangeQuotientIso_tmul
    (φ : R →+* S) (I : Ideal R) (s : S) (r : R) :
    (pointKoszulFlatBaseChangeQuotientIso φ I).hom
      (s ⊗ₜ[R,φ] (Ideal.Quotient.mk I r)) =
        Ideal.Quotient.mk (I.map φ) (s * φ r) := by
  letI : Algebra R S := φ.toAlgebra
  change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm
    (s ⊗ₜ[R] (Ideal.Quotient.mk I r)) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  change Ideal.Quotient.mk (I.map φ) (φ r * s) = _
  rw [mul_comm]

def pointKoszulFlatBaseChangePointIso (φ : R →+* S) (a b : R) :
    (ModuleCat.extendScalars.{u, u, u} φ).obj
      (ModuleCat.of R (R ⧸ Ideal.span ({a, b} : Set R))) ≅
        ModuleCat.of S (S ⧸ Ideal.span ({φ a, φ b} : Set S)) := by
  have hmap : (Ideal.span ({a, b} : Set R)).map φ =
      Ideal.span ({φ a, φ b} : Set S) := by
    rw [Ideal.map_span, Set.image_pair]
  exact pointKoszulFlatBaseChangeQuotientIso φ _ ≪≫
    (Submodule.quotEquivOfEq _ _ hmap).toModuleIso

theorem pointKoszulFlatBaseChangePointIso_tmul
    (φ : R →+* S) (a b : R) (s : S) (r : R) :
    (pointKoszulFlatBaseChangePointIso φ a b).hom
      (s ⊗ₜ[R,φ] (Ideal.Quotient.mk (Ideal.span ({a, b} : Set R)) r)) =
        Ideal.Quotient.mk (Ideal.span ({φ a, φ b} : Set S)) (s * φ r) := by
  dsimp only [pointKoszulFlatBaseChangePointIso, Iso.trans_hom]
  rw [ModuleCat.comp_apply, pointKoszulFlatBaseChangeQuotientIso_tmul]
  rfl

end PfaffianDescent
