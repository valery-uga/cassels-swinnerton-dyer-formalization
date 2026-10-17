import PfaffianDescent.PointCartierNativeStalkRegularPairTransfer

/-! # Restriction injectivity in the actual native module-stalk Ext universe -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u

theorem pointCartierNativeStalkSurfaceRestriction_eq_zero_iff
    {R B : Type u} [CommRing R] [CommRing B]
    [hExtR : HasExt.{u + 1} (ModuleCat.{u} R)]
    [hExtB : HasExt.{u + 1} (ModuleCat.{u} B)]
    (t : R) (e : (R ⧸ Ideal.span {t}) ≃+* B)
    (φ : R →+* B) (hφ : φ = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {t})))
    (ht : t ∈ R⁰) (f g : B) (hf : f ∈ B⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (B ⧸ Ideal.span {f})⁰)
    (M N : ModuleCat.{u} B)
    (qM : M ≅ ModuleCat.of B (B ⧸ Ideal.span ({f, g} : Set B)))
    (qN : N ≅ ModuleCat.of B B) (z : Ext.{u + 1} M N 2) :
    z.mapExactFunctor (ModuleCat.restrictScalars φ) = 0 ↔ z = 0 := by
  letI : HasExt.{u + 1} (ModuleCat.{u} (R ⧸ Ideal.span {t})) :=
    hasExt_of_enoughInjectives.{u + 1, u, u + 1} (ModuleCat.{u} (R ⧸ Ideal.span {t}))
  exact pointCartierNativeStalkActualRestrictionPair_eq_zero_iff
    t e φ hφ ht f g hf hg M N qM qN z

end PfaffianDescent
