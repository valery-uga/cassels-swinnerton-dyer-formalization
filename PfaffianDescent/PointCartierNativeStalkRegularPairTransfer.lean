import PfaffianDescent.PointCartierNativeStalkActualRestriction

/-! # Cartier restriction and ambient vanishing for any actual regular pair

The lifts of the surface parameters are chosen and transported inside generic
local algebra, so applying the result to a native stalk requires no rewriting
of dependent geometric endpoint types.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u w w' w''

theorem pointCartierNativeStalkActualRestrictionPair_eq_zero_iff
    {R B : Type u} [CommRing R] [CommRing B]
    [hExtR : HasExt.{w} (ModuleCat R)]
    (t : R) [hExtC : HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {t}))]
    [hExtB : HasExt.{w''} (ModuleCat B)]
    (e : (R ⧸ Ideal.span {t}) ≃+* B)
    (φ : R →+* B) (hφ : φ = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {t})))
    (ht : t ∈ R⁰) (f g : B) (hf : f ∈ B⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (B ⧸ Ideal.span {f})⁰)
    (M N : ModuleCat B)
    (qM : M ≅ ModuleCat.of B (B ⧸ Ideal.span ({f, g} : Set B)))
    (qN : N ≅ ModuleCat.of B B) (z : Ext.{w''} M N 2) :
    z.mapExactFunctor (ModuleCat.restrictScalars φ) = 0 ↔ z = 0 := by
  obtain ⟨gR, hgR⟩ := Ideal.Quotient.mk_surjective (e.symm f)
  obtain ⟨hR, hhR⟩ := Ideal.Quotient.mk_surjective (e.symm g)
  have heG : e (Ideal.Quotient.mk (Ideal.span {t}) gR) = f :=
    (congrArg e hgR).trans (e.apply_symm_apply f)
  have heH : e (Ideal.Quotient.mk (Ideal.span {t}) hR) = g :=
    (congrArg e hhR).trans (e.apply_symm_apply g)
  subst f g
  exact pointCartierNativeStalkActualRestrictionEndpoints_eq_zero_iff
    t gR hR e φ hφ ht hf hg M N qM qN z

theorem pointCartierNativeStalkActualAmbientExtTwoPair_subsingleton
    {R B : Type u} [CommRing R] [CommRing B]
    [hExtR : HasExt.{w} (ModuleCat R)]
    (t : R) (e : (R ⧸ Ideal.span {t}) ≃+* B)
    (φ : R →+* B) (hφ : φ = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {t})))
    (ht : t ∈ R⁰) (f g : B) (hf : f ∈ B⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (B ⧸ Ideal.span {f})⁰)
    (M : ModuleCat B)
    (qM : M ≅ ModuleCat.of B (B ⧸ Ideal.span ({f, g} : Set B))) :
    Subsingleton (Ext.{w} ((ModuleCat.restrictScalars φ).obj M) (ModuleCat.of R R) 2) := by
  obtain ⟨gR, hgR⟩ := Ideal.Quotient.mk_surjective (e.symm f)
  obtain ⟨hR, hhR⟩ := Ideal.Quotient.mk_surjective (e.symm g)
  have heG : e (Ideal.Quotient.mk (Ideal.span {t}) gR) = f :=
    (congrArg e hgR).trans (e.apply_symm_apply f)
  have heH : e (Ideal.Quotient.mk (Ideal.span {t}) hR) = g :=
    (congrArg e hhR).trans (e.apply_symm_apply g)
  subst f g
  exact pointCartierNativeStalkActualAmbientExtTwo_subsingleton
    t gR hR e φ hφ ht hf hg M qM

end PfaffianDescent
