import PfaffianDescent.PointCartierNativeStalkPrincipalNormalization
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Span.Basic

/-! SOURCE ONLY / UNCHECKED. The actual inclusion functional of a rank-one
module has its actual parameter as coefficient in the dual frame. The whole
dual increment and its projection are constructed, not assumed. -/
noncomputable section
set_option autoImplicit false
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors
universe u w
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- Evaluate the actual functional on the original frame vector. -/
def actualIdealFrameDualCoordinate190 (e : R ≃ₗ[R] M) :
    Module.Dual R M ≃ₗ[R] R :=
  e.dualMap.trans (LinearMap.ringLmapEquivSelf R R R)

lemma actualIdealFrameDualCoordinate_apply190 (e : R ≃ₗ[R] M)
    (a : Module.Dual R M) : actualIdealFrameDualCoordinate190 e a = a (e 1) := rfl

lemma actualIdealFrameDualCoordinate_inclusion190 (e : R ≃ₗ[R] M)
    (j : M →ₗ[R] R) (t : R) (he : ∀ r, j (e r) = r * t) :
    actualIdealFrameDualCoordinate190 e j = t := by
  change j (e 1) = t
  exact (he 1).trans (one_mul t)

/-- The first map is literally scalar multiplication of the ORIGINAL
inclusion functional j; the endpoint projection is built in its dual frame. -/
def actualIdealFrameDualIncrement190 (e : R ≃ₗ[R] M)
    (j : M →ₗ[R] R) (t : R) (he : ∀ r, j (e r) = r * t) :
    ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero
    (LinearMap.toSpanSingleton R (Module.Dual R M) j)
    ((Ideal.Quotient.mkₐ R (Ideal.span {t})).toLinearMap.comp
      (actualIdealFrameDualCoordinate190 e).toLinearMap) (by
        apply LinearMap.ext
        intro r
        change Ideal.Quotient.mk (Ideal.span {t})
          (actualIdealFrameDualCoordinate190 e (r • j)) = 0
        rw [(actualIdealFrameDualCoordinate190 e).map_smul,
          actualIdealFrameDualCoordinate_inclusion190 e j t he]
        change Ideal.Quotient.mk (Ideal.span {t}) (r * t) = 0
        rw [map_mul, Ideal.Quotient.mk_singleton_self, mul_zero])

lemma actualIdealFrameDualIncrement_first_square190 (e : R ≃ₗ[R] M)
    (j : M →ₗ[R] R) (t : R) (he : ∀ r, j (e r) = r * t) :
    (actualIdealFrameDualIncrement190 e j t he).f ≫
      (actualIdealFrameDualCoordinate190 e).toModuleIso.hom =
        (pointCartierYonedaCoefficientComplex t).f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change R at r
  change actualIdealFrameDualCoordinate190 e (r • j) = t * r
  rw [(actualIdealFrameDualCoordinate190 e).map_smul,
    actualIdealFrameDualCoordinate_inclusion190 e j t he]
  change r * t = t * r
  exact mul_comm r t

lemma actualIdealFrameDualIncrement_second_square190 (e : R ≃ₗ[R] M)
    (j : M →ₗ[R] R) (t : R) (he : ∀ r, j (e r) = r * t) :
    (actualIdealFrameDualIncrement190 e j t he).g =
      (actualIdealFrameDualCoordinate190 e).toModuleIso.hom ≫
        (pointCartierYonedaCoefficientComplex t).g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-- Both endpoint identities and the original inclusion square are derived. -/
def actualIdealFrameDualIncrementPrincipalIso190 (e : R ≃ₗ[R] M)
    (j : M →ₗ[R] R) (t : R) (he : ∀ r, j (e r) = r * t) :
    actualIdealFrameDualIncrement190 e j t he ≅
      pointCartierYonedaCoefficientComplex t := by
  let e₁ := Iso.refl (ModuleCat.of R R)
  let e₂ := (actualIdealFrameDualCoordinate190 e).toModuleIso
  let e₃ := Iso.refl (ModuleCat.of R (R ⧸ Ideal.span {t}))
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · change (𝟙 (ModuleCat.of R R)) ≫
      (pointCartierYonedaCoefficientComplex t).f =
        (actualIdealFrameDualIncrement190 e j t he).f ≫
          (actualIdealFrameDualCoordinate190 e).toModuleIso.hom
    exact (Category.id_comp (pointCartierYonedaCoefficientComplex t).f).trans
      (actualIdealFrameDualIncrement_first_square190 e j t he).symm
  · change (actualIdealFrameDualCoordinate190 e).toModuleIso.hom ≫
      (pointCartierYonedaCoefficientComplex t).g =
        (actualIdealFrameDualIncrement190 e j t he).g ≫
          (𝟙 (ModuleCat.of R (R ⧸ Ideal.span {t})))
    exact (actualIdealFrameDualIncrement_second_square190 e j t he).symm.trans
      (Category.comp_id (actualIdealFrameDualIncrement190 e j t he).g).symm

lemma actualIdealFrameDualIncrement_shortExact190 (e : R ≃ₗ[R] M)
    (j : M →ₗ[R] R) (t : R) (he : ∀ r, j (e r) = r * t) (ht : t ∈ R⁰) :
    (actualIdealFrameDualIncrement190 e j t he).ShortExact :=
  ShortComplex.shortExact_of_iso
    (actualIdealFrameDualIncrementPrincipalIso190 e j t he).symm
    (pointCartierYonedaCoefficientComplex_shortExact t ht)

/-- The inverse dual frame retains the native quotient augmentation. -/
lemma actualIdealFrameDualIncrement_inverse_projection190 (e : R ≃ₗ[R] M)
    (j : M →ₗ[R] R) (t : R) (he : ∀ r, j (e r) = r * t) :
    (actualIdealFrameDualCoordinate190 e).toModuleIso.inv ≫
      (actualIdealFrameDualIncrement190 e j t he).g =
        (pointCartierYonedaCoefficientComplex t).g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change Ideal.Quotient.mk (Ideal.span {t})
    (actualIdealFrameDualCoordinate190 e ((actualIdealFrameDualCoordinate190 e).symm r)) =
      Ideal.Quotient.mk (Ideal.span {t}) r
  rw [LinearEquiv.apply_symm_apply]

/-- The whole actual dual increment is the principal extension in Ext,
with the actual source and quotient endpoints unchanged. -/
lemma actualIdealFrameDualIncrement_extClass190 [HasExt.{w} (ModuleCat R)]
    (e : R ≃ₗ[R] M) (j : M →ₗ[R] R) (t : R)
    (he : ∀ r, j (e r) = r * t) (ht : t ∈ R⁰) :
    (actualIdealFrameDualIncrement_shortExact190 e j t he ht).extClass =
      (pointCartierYonedaCoefficientComplex_shortExact t ht).extClass := by
  have h := ShortComplex.ShortExact.extClass_naturality
    (actualIdealFrameDualIncrement_shortExact190 e j t he ht)
    (pointCartierYonedaCoefficientComplex_shortExact t ht)
    (actualIdealFrameDualIncrementPrincipalIso190 e j t he).hom
  change (actualIdealFrameDualIncrement_shortExact190 e j t he ht).extClass.comp
      (Ext.mk₀ (𝟙 (ModuleCat.of R R))) (add_zero 1) =
    (Ext.mk₀ (𝟙 (ModuleCat.of R (R ⧸ Ideal.span {t})))).comp
      (pointCartierYonedaCoefficientComplex_shortExact t ht).extClass (zero_add 1) at h
  exact (Ext.comp_mk₀_id
    (actualIdealFrameDualIncrement_shortExact190 e j t he ht).extClass).symm.trans
      (h.trans (Ext.mk₀_id_comp
        (pointCartierYonedaCoefficientComplex_shortExact t ht).extClass))

end PfaffianDescent
