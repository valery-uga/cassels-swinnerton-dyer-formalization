import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability

/-!
Localizing the ambient algebra and its original
quotient preserves flatness over the original coefficient ring. The
localized quotient is a localization of the original quotient ring.
-/

noncomputable section
namespace AllCharacteristics
universe u v w

theorem localizedQuotient_baseFlat318
    {S : Type u} {A : Type v} {B : Type w}
    [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra A B] [Algebra S B] [IsScalarTower S A B]
    (P : Submonoid A) [IsLocalization P B] (J : Ideal A)
    [Module.Flat S (A ⧸ J)] :
    Module.Flat S (B ⧸ J.map (algebraMap A B)) := by
  let Q := B ⧸ J.map (algebraMap A B)
  letI : IsScalarTower S (A ⧸ J) Q :=
    IsScalarTower.of_algebraMap_eq (fun s => by
      change Ideal.Quotient.mk (J.map (algebraMap A B)) (algebraMap S B s) =
        Ideal.Quotient.mk (J.map (algebraMap A B))
          (algebraMap A B (algebraMap S A s))
      rw [IsScalarTower.algebraMap_apply S A B])
  letI : Module.Flat (A ⧸ J) Q :=
    IsLocalization.flat Q (Algebra.algebraMapSubmonoid (A ⧸ J) P)
  exact Module.Flat.trans S (A ⧸ J) Q

end AllCharacteristics
end
