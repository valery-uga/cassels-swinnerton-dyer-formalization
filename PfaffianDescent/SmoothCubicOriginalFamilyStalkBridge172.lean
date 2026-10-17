import PfaffianDescent.SurjectiveFamilyFiberStalkReduction172
import PfaffianDescent.SmoothCubicClosedPointNativeLCI164
import AllCharacteristics.HypersurfaceReduction

/-! SOURCE ONLY / UNVERIFIED172. The ORIGINAL cubic closed point, the
chosen ACTUAL smooth Artin cubic family, and the literal reduction stalk
map. Geometric scalar/kernel/ambient identifications are proved internally.
This does not claim the embedded-ideal base-change comparison still needed
for an actual finite-flat closed deformation's ideal in168. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal native stalk map of the CONSTRUCTED original special-fiber
inclusion, with the original K and P retained unchanged. -/
def smoothCubic_originalFamilyStalkReduction172
    {B K : Type u} [CommRing B] [Field K] (b : B →+* K)
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (he : q.map b = p)
    (P : closedPoints (hypersurface p hp)) :
    (hypersurface q hq).presheaf.stalk (hypersurfaceReductionMap b q hq p hp he P.1) →+*
      (hypersurface p hp).presheaf.stalk P.1 :=
  ((hypersurfaceReductionMap b q hq p hp he).stalkMap P.1).hom

lemma smoothCubic_originalFamilyStalkReduction172_surjective
    {B K : Type u} [CommRing B] [Field K]
    (b : B →+* K) (hb : Function.Surjective b)
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (he : q.map b = p)
    (P : closedPoints (hypersurface p hp)) :
    Function.Surjective (smoothCubic_originalFamilyStalkReduction172 b q hq p hp he P) := by
  letI : IsClosedImmersion (hypersurfaceReductionMap b q hq p hp he) :=
    isClosedImmersion_hypersurfaceReductionMap b q hq p hp he hb
  exact (hypersurfaceReductionMap b q hq p hp he).stalkMap_surjective P.1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- ENTIRE kernel, under the original canonical B action. The native
hypersurface reduction isomorphism is constructed from the equation
reduction, so no special-fiber ring isomorphism/certificate is supplied. -/
lemma smoothCubic_originalFamilyStalkReduction172_ker
    {B K : Type u} [CommRing B] [Field K]
    (b : B →+* K) (hb : Function.Surjective b)
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (he : q.map b = p)
    (P : closedPoints (hypersurface p hp)) :
    RingHom.ker (smoothCubic_originalFamilyStalkReduction172 b q hq p hp he P) =
      (RingHom.ker b).map (familyBaseToStalk169 (hypersurfaceToBase q hq)
        (hypersurfaceReductionMap b q hq p hp he P.1)) := by
  let e := hypersurfaceReductionIso b q hq p hp he
  let i := pullback.fst (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom b))
  change RingHom.ker ((e.hom ≫ i).stalkMap P.1).hom = _
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap P.1)).1]
  exact surjectiveFamilyFiberStalkReduction172_ker (hypersurfaceToBase q hq) b hb (e.hom P.1)

def smoothCubic_originalFamilyStalkQuotientEquiv172
    {B K : Type u} [CommRing B] [Field K]
    (b : B →+* K) (hb : Function.Surjective b)
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (he : q.map b = p)
    (P : closedPoints (hypersurface p hp)) :
    ((hypersurface q hq).presheaf.stalk (hypersurfaceReductionMap b q hq p hp he P.1) ⧸
      (RingHom.ker b).map (familyBaseToStalk169 (hypersurfaceToBase q hq)
        (hypersurfaceReductionMap b q hq p hp he P.1))) ≃+*
      (hypersurface p hp).presheaf.stalk P.1 :=
  (Ideal.quotEquivOfEq (smoothCubic_originalFamilyStalkReduction172_ker b hb q hq p hp he P).symm).trans
    ((smoothCubic_originalFamilyStalkReduction172 b q hq p hp he P).quotientKerEquivOfSurjective
      (smoothCubic_originalFamilyStalkReduction172_surjective b hb q hq p hp he P))

lemma smoothCubic_originalFamilyStalkQuotientEquiv172_mk
    {B K : Type u} [CommRing B] [Field K]
    (b : B →+* K) (hb : Function.Surjective b)
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (he : q.map b = p)
    (P : closedPoints (hypersurface p hp))
    (a : (hypersurface q hq).presheaf.stalk (hypersurfaceReductionMap b q hq p hp he P.1)) :
    smoothCubic_originalFamilyStalkQuotientEquiv172 b hb q hq p hp he P (Ideal.Quotient.mk _ a) =
      smoothCubic_originalFamilyStalkReduction172 b q hq p hp he P a := by
  simp only [smoothCubic_originalFamilyStalkQuotientEquiv172, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ a

/-- The actual chosen smooth Artin family supplies168's ambient stalk
properties under its EXACT original coefficient action. -/
lemma smoothCubic_originalFamilyStalk_properties172
    {B K : Type u} [CommRing B] [Field K] [IsArtinianRing B]
    (b : B →+* K)
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase q hq)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (he : q.map b = p)
    (P : closedPoints (hypersurface p hp)) :
    let x := hypersurfaceReductionMap b q hq p hp he P.1
    letI := familyStalkAlgebra169 (hypersurfaceToBase q hq) x
    Module.Flat B ((hypersurface q hq).presheaf.stalk x) ∧
      IsLocalRing ((hypersurface q hq).presheaf.stalk x) ∧
      IsNoetherianRing ((hypersurface q hq).presheaf.stalk x) :=
  smooth_family_stalk_properties_artin169 (hypersurfaceToBase q hq)
    (hypersurfaceReductionMap b q hq p hp he P.1)

/-- Nilpotence of the original residue-map kernel is DERIVED from Artin
locality and surjectivity to the ORIGINAL field; it is not a certificate. -/
lemma smoothCubic_artin_residueKernel_isNilpotent172
    {B K : Type u} [CommRing B] [Field K] [IsArtinianRing B] [IsLocalRing B]
    (b : B →+* K) (hb : Function.Surjective b) : IsNilpotent (RingHom.ker b) := by
  rw [IsLocalRing.ker_eq_maximalIdeal b hb]
  exact (isArtinianRing_iff_isNilpotent_maximalIdeal B).mp inferInstance

/-- The ORIGINAL point's native LCI generators come from164; even
smoothness of the original cubic is derived by ACTUAL family base change.
No regular sequence or point-ring regularity premise is supplied. -/
lemma smoothCubic_originalFamily_specialPoint_LCI172
    {B K : Type u} [CommRing B] [Field K]
    (b : B →+* K)
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase q hq)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (he : q.map b = p) (P : closedPoints (hypersurface p hp)) :
    ∃ f g : (hypersurface p hp).presheaf.stalk P.1,
      RingTheory.Sequence.IsRegular ((hypersurface p hp).presheaf.stalk P.1) [f, g] ∧
      Ideal.span ({f, g} : Set ((hypersurface p hp).presheaf.stalk P.1)) =
        RingHom.ker (((hypersurface p hp).residue P.1).hom) := by
  letI : Smooth (hypersurfaceToBase p hp) := MorphismProperty.of_isPullback
    (isPullback_hypersurfaceReductionMap b q hq p hp he)
    (inferInstance : Smooth (hypersurfaceToBase q hq))
  exact smoothCubic_originalClosedPoint_residueKernel_regularSequence164 p hp hp0 P

end PfaffianDescent
