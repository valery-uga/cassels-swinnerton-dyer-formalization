import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
namespace PfaffianDescent
universe u v w z
variable (R : Type u) [CommRing R]
variable {C : Type v} [CommRing C] [Algebra R C] (delta : C)
variable (L : Type w) [CommRing L] [Algebra C L] [Algebra R L] [IsScalarTower R C L]
variable [IsLocalization.Away delta L]
variable (A : Type z) [CommRing A] [Algebra R A]

/-- The localization universal property as an actual equivalence, with both inverse laws.
The target ring may be nonreduced or zero. -/
def localizationAlgHomUnitEquiv292 :
    (L →ₐ[R] A) ≃ {p : C →ₐ[R] A // IsUnit (p delta)} where
  toFun f := ⟨f.comp (Algebra.algHom R C L),
    (IsLocalization.Away.algebraMap_isUnit (S := L) delta).map f.toRingHom⟩
  invFun p := IsLocalization.Away.liftAlgHom delta p.property
  left_inv f := by
    apply IsLocalization.algHom_ext (Submonoid.powers delta)
    apply AlgHom.ext
    intro c
    exact IsLocalization.Away.lift_eq delta
      ((IsLocalization.Away.algebraMap_isUnit (S := L) delta).map f.toRingHom) c
  right_inv p := by
    apply Subtype.ext
    apply AlgHom.ext
    intro c
    exact IsLocalization.Away.lift_eq delta p.property c

lemma localizationAlgHomUnitEquiv_apply_val292 (f : L →ₐ[R] A) :
    (localizationAlgHomUnitEquiv292 R delta L A f).val = f.comp (Algebra.algHom R C L) := rfl

lemma localizationAlgHomUnitEquiv_symm_restrict292
    (p : {p : C →ₐ[R] A // IsUnit (p delta)}) :
    ((localizationAlgHomUnitEquiv292 R delta L A).symm p).comp (Algebra.algHom R C L) = p.val := by
  apply AlgHom.ext
  intro c
  exact IsLocalization.Away.lift_eq delta p.property c

lemma localizationAlgHomUnitEquiv_natural292
    {D : Type*} [CommRing D] [Algebra R D] (f : L →ₐ[R] A) (g : A →ₐ[R] D) :
    (localizationAlgHomUnitEquiv292 R delta L D (g.comp f)).val =
      g.comp (localizationAlgHomUnitEquiv292 R delta L A f).val := rfl

end PfaffianDescent
