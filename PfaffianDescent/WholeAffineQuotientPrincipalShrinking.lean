import PfaffianDescent.ActualArtinianQuotientLocalizationIso
import PfaffianDescent.FiniteFlatHilbertTestPoints195
import Mathlib.RingTheory.Flat.Basic

/-!
Principal shrinking around
the constructed finite support preserves the actual finite-flat algebra,
its rank, and its whole embedded ideal in the original ambient scheme.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u
set_option autoImplicit false

theorem wholeAffineQuotient_principalShrink_properties001
    {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
    (J : Ideal A) [IsArtinianRing (A ⧸ J)]
    [Module.Finite S (A ⧸ J)] [Module.Flat S (A ⧸ J)]
    (r : A) (hr : r ∈ finiteSupportDenominators001 (actualArtinianQuotientSupport001 J))
    {X : Scheme.{u}} (a : Spec (.of A) ⟶ X) :
    let L := Localization.Away r
    let Jr := J.map (algebraMap A L)
    Module.Finite S (L ⧸ Jr) ∧ Module.Flat S (L ⧸ Jr) ∧
      Module.finrank S (L ⧸ Jr) = Module.finrank S (A ⧸ J) ∧
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Jr)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ a)).ker =
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a).ker := by
  let L := Localization.Away r
  let Jr := J.map (algebraMap A L)
  let eA : (A ⧸ J) ≃ₐ[A] (L ⧸ Jr) :=
    actualArtinianQuotientLocalizationIso001 J (Submonoid.powers r)
      (Submonoid.powers_le.mpr hr)
  let eS : (A ⧸ J) ≃ₐ[S] (L ⧸ Jr) := eA.restrictScalars S
  letI : Module.Finite S (L ⧸ Jr) := Module.Finite.of_surjective eS.toLinearMap eS.surjective
  letI : Module.Flat S (L ⧸ Jr) := Module.Flat.of_linearEquiv eS.toLinearEquiv.symm
  let E : Spec (.of (L ⧸ Jr)) ≅ Spec (.of (A ⧸ J)) :=
    Scheme.Spec.mapIso eA.toRingEquiv.toCommRingCatIso.op
  have htriangle : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Jr)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A L)) =
      E.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Jr)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A L)) =
      Spec.map (CommRingCat.ofHom eA.toRingEquiv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  refine ⟨inferInstance, inferInstance, eS.toLinearEquiv.finrank_eq.symm, ?_⟩
  rw [← Category.assoc, htriangle, Category.assoc]
  exact Scheme.Hom.ker_comp_of_isIso E.hom _

end PfaffianDescent
end
