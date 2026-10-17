import PfaffianDescent.ActualFamilyFiberStalkReduction171

/-! SOURCE ONLY / UNVERIFIED172. Replace a surjective base-ring map by its
canonical quotient using a CONSTRUCTED actual fiber isomorphism. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

lemma surjectiveBaseMap_specFactor172
    {B K : Type u} [CommRing B] [CommRing K]
    (b : B →+* K) (hb : Function.Surjective b) :
    Spec.map (b.quotientKerEquivOfSurjective hb).toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker b))) =
      Spec.map (CommRingCat.ofHom b) := by
  rw [← Spec.map_comp]
  congr 1

/-- Actual isomorphism from the residue-map fiber to the quotient fiber;
the quotient-to-K isomorphism is constructed from the ORIGINAL b. -/
def surjectiveFamilyFiberToQuotient172
    {B K : Type u} [CommRing B] [CommRing K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b) :
    pullback f (Spec.map (CommRingCat.ofHom b)) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker b)))) :=
  pullback.map f (Spec.map (CommRingCat.ofHom b)) f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker b))))
    (𝟙 _) (Spec.map (b.quotientKerEquivOfSurjective hb).toCommRingCatIso.hom)
    (𝟙 _) (by simp) (by
      simpa only [Category.comp_id] using (surjectiveBaseMap_specFactor172 b hb).symm)

lemma surjectiveFamilyFiberToQuotient172_toAmbient
    {B K : Type u} [CommRing B] [CommRing K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b) :
    surjectiveFamilyFiberToQuotient172 f b hb ≫
      pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker b)))) =
      pullback.fst f (Spec.map (CommRingCat.ofHom b)) := by
  simp only [surjectiveFamilyFiberToQuotient172, pullback.map,
    pullback.lift_fst, Category.comp_id]

lemma surjectiveFamilyFiberToQuotient172_isIso
    {B K : Type u} [CommRing B] [CommRing K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b) :
    IsIso (surjectiveFamilyFiberToQuotient172 f b hb) := by
  unfold surjectiveFamilyFiberToQuotient172
  infer_instance

def surjectiveFamilyFiberStalkReduction172
    {B K : Type u} [CommRing B] [CommRing K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K)
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom b)) : Scheme.{u})) :
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom b))
    X.presheaf.stalk (i z) →+* (pullback f (Spec.map (CommRingCat.ofHom b))).presheaf.stalk z :=
  ((pullback.fst f (Spec.map (CommRingCat.ofHom b))).stalkMap z).hom

lemma surjectiveFamilyFiberStalkReduction172_surjective
    {B K : Type u} [CommRing B] [CommRing K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b)
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom b)) : Scheme.{u})) :
    Function.Surjective (surjectiveFamilyFiberStalkReduction172 f b z) := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom b)) :=
    IsClosedImmersion.spec_of_surjective _ hb
  exact (pullback.fst f (Spec.map (CommRingCat.ofHom b))).stalkMap_surjective z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Literal kernel for an arbitrary ORIGINAL surjective residue map,
without imposing K = B/I or providing a fiber/kernel comparison. -/
lemma surjectiveFamilyFiberStalkReduction172_ker
    {B K : Type u} [CommRing B] [CommRing K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b)
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom b)) : Scheme.{u})) :
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom b))
    RingHom.ker (surjectiveFamilyFiberStalkReduction172 f b z) =
      (RingHom.ker b).map (familyBaseToStalk169 f (i z)) := by
  let m := surjectiveFamilyFiberToQuotient172 f b hb
  letI : IsIso m := surjectiveFamilyFiberToQuotient172_isIso f b hb
  change RingHom.ker ((pullback.fst f (Spec.map (CommRingCat.ofHom b))).stalkMap z).hom = _
  rw [← surjectiveFamilyFiberToQuotient172_toAmbient f b hb,
    Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso (m.stalkMap z)).1]
  exact familyFiberStalkReduction171_ker f (RingHom.ker b) (m z)

end PfaffianDescent
