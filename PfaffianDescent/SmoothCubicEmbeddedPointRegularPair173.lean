import PfaffianDescent.EmbeddedFiberStalkIdealImage173
import PfaffianDescent.SmoothCubicOriginalFamilyStalkBridge172
import PfaffianDescent.SmoothCubicPrescribedIdealRegularPair168

/-! SOURCE ONLY / UNVERIFIED173. An ACTUAL flat closed deformation with
Cartesian special fiber the ORIGINAL closed point has an ACTUAL upstairs
regular pair. No ambient/reduction/quotient-flatness/ideal-image/regularity
certificate is supplied. Finiteness of the chosen deformation is unnecessary
for this local conclusion. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open scoped nonZeroDivisors
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma smoothCubic_embeddedPoint_ambient_eq173
    {B K : Type u} [CommRing B] [Field K] {Z : Scheme.{u}}
    (b : B →+* K) (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (he : q.map b = p)
    (P : closedPoints (hypersurface p hp)) (i : Z ⟶ hypersurface q hq)
    (u0 : Spec ((hypersurface p hp).residueField P.1) ⟶ Z)
    (H : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.1)
      i (hypersurfaceReductionMap b q hq p hp he)) :
    hypersurfaceReductionMap b q hq p hp he P.1 = i (u0 default) := by
  simpa only [Scheme.fromSpecResidueField_apply] using cartesianStalkPointEq173 H default

/-- The ideal is the ENTIRE actual closed-deformation stalk kernel, which
closedImmersionStalkAt173_ker_eq_ideal_germ identifies with its actual affine
ideal germ. Original ambient point, map and scalar action are retained. -/
def smoothCubic_embeddedOriginalPointStalkIdeal173
    {B K : Type u} [CommRing B] [Field K] {Z : Scheme.{u}}
    (b : B →+* K) (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (he : q.map b = p)
    (P : closedPoints (hypersurface p hp)) (i : Z ⟶ hypersurface q hq)
    (u0 : Spec ((hypersurface p hp).residueField P.1) ⟶ Z)
    (H : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.1)
      i (hypersurfaceReductionMap b q hq p hp he)) :
    Ideal ((hypersurface q hq).presheaf.stalk (hypersurfaceReductionMap b q hq p hp he P.1)) :=
  RingHom.ker (closedImmersionStalkAt173 i
    (hypersurfaceReductionMap b q hq p hp he P.1) (u0 default)
    (smoothCubic_embeddedPoint_ambient_eq173 b q hq p hp he P i u0 H))

lemma smoothCubic_embeddedOriginalPointStalkIdeal173_quotient_flat
    {B K : Type u} [CommRing B] [Field K] {Z : Scheme.{u}}
    (b : B →+* K) (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (he : q.map b = p)
    (P : closedPoints (hypersurface p hp)) (i : Z ⟶ hypersurface q hq)
    [IsClosedImmersion i] [Flat (i ≫ hypersurfaceToBase q hq)]
    (u0 : Spec ((hypersurface p hp).residueField P.1) ⟶ Z)
    (H : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.1)
      i (hypersurfaceReductionMap b q hq p hp he)) :
    let x := hypersurfaceReductionMap b q hq p hp he P.1
    letI := familyStalkAlgebra169 (hypersurfaceToBase q hq) x
    Module.Flat B ((hypersurface q hq).presheaf.stalk x ⧸
      smoothCubic_embeddedOriginalPointStalkIdeal173 b q hq p hp he P i u0 H) :=
  closedImmersionStalkAt173_quotient_flat (hypersurfaceToBase q hq) i
    (hypersurfaceReductionMap b q hq p hp he P.1) (u0 default)
    (smoothCubic_embeddedPoint_ambient_eq173 b q hq p hp he P i u0 H)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma smoothCubic_embeddedOriginalPointStalkIdeal173_image
    {B K : Type u} [CommRing B] [Field K] {Z : Scheme.{u}}
    (b : B →+* K) (hb : Function.Surjective b)
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (he : q.map b = p)
    (P : closedPoints (hypersurface p hp)) (i : Z ⟶ hypersurface q hq) [IsClosedImmersion i]
    (u0 : Spec ((hypersurface p hp).residueField P.1) ⟶ Z)
    (H : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.1)
      i (hypersurfaceReductionMap b q hq p hp he)) :
    (smoothCubic_embeddedOriginalPointStalkIdeal173 b q hq p hp he P i u0 H).map
      (smoothCubic_originalFamilyStalkReduction172 b q hq p hp he P) =
      RingHom.ker (((hypersurface p hp).residue P.1).hom) := by
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  have h := embeddedCartesianFieldPoint_stalkIdeal_image_residue173
    (hypersurfaceToBase q hq) b hb (hypersurfaceReductionMap b q hq p hp he)
    (hypersurfaceToBase p hp) (isPullback_hypersurfaceReductionMap b q hq p hp he)
    i u0 ((hypersurface p hp).fromSpecResidueField P.1) H default
  have haux (x : hypersurface p hp)
      (hx : x = (hypersurface p hp).fromSpecResidueField P.1 default) :
      (RingHom.ker (closedImmersionStalkAt173 i
        (hypersurfaceReductionMap b q hq p hp he x) (u0 default)
        (by rw [hx]; exact cartesianStalkPointEq173 H default))).map
          ((hypersurfaceReductionMap b q hq p hp he).stalkMap x).hom =
        RingHom.ker (((hypersurface p hp).residue x).hom) := by
    subst x
    exact h
  exact haux P.1 (Scheme.fromSpecResidueField_apply P.1 default).symm

/-- ORIGINAL Section5 local deformation conclusion: every ACTUAL flat
closed deformation whose whole special fiber is the ORIGINAL point has
its ENTIRE prescribed ideal generated by an ACTUAL lifted regular pair.
Only the chosen smooth Artin family and Cartesian point deformation are
input data. All168 ambient/reduction/ideal hypotheses are derived above. -/
lemma smoothCubic_embeddedOriginalPointStalkIdeal173_regular_pair
    {B K : Type u} [CommRing B] [Field K] [IsArtinianRing B] [IsLocalRing B]
    {Z : Scheme.{u}} (b : B →+* K) (hb : Function.Surjective b)
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase q hq)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (he : q.map b = p) (P : closedPoints (hypersurface p hp))
    (i : Z ⟶ hypersurface q hq) [IsClosedImmersion i] [Flat (i ≫ hypersurfaceToBase q hq)]
    (u0 : Spec ((hypersurface p hp).residueField P.1) ⟶ Z)
    (H : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.1)
      i (hypersurfaceReductionMap b q hq p hp he)) :
    let A := (hypersurface q hq).presheaf.stalk (hypersurfaceReductionMap b q hq p hp he P.1)
    let J := smoothCubic_embeddedOriginalPointStalkIdeal173 b q hq p hp he P i u0 H
    ∃ a c : A, a ∈ J ∧ c ∈ J ∧ J = Ideal.span ({a, c} : Set A) ∧
      a ∈ A⁰ ∧ Ideal.Quotient.mk (Ideal.span {a}) c ∈ (A ⧸ Ideal.span {a})⁰ := by
  let x := hypersurfaceReductionMap b q hq p hp he P.1
  let A := (hypersurface q hq).presheaf.stalk x
  let J := smoothCubic_embeddedOriginalPointStalkIdeal173 b q hq p hp he P i u0 H
  letI : Algebra B A := familyStalkAlgebra169 (hypersurfaceToBase q hq) x
  have hA := smoothCubic_originalFamilyStalk_properties172 b q hq p hp he P
  letI : Module.Flat B A := hA.1
  letI : IsLocalRing A := hA.2.1
  letI : IsNoetherianRing A := hA.2.2
  letI : Module.Flat B (A ⧸ J) :=
    smoothCubic_embeddedOriginalPointStalkIdeal173_quotient_flat b q hq p hp he P i u0 H
  letI : Smooth (hypersurfaceToBase p hp) := MorphismProperty.of_isPullback
    (isPullback_hypersurfaceReductionMap b q hq p hp he)
    (inferInstance : Smooth (hypersurfaceToBase q hq))
  exact smoothCubic_originalClosedPoint_prescribedIdeal_regularPair168 p hp hp0 P
    (smoothCubic_originalFamilyStalkReduction172 b q hq p hp he P)
    (smoothCubic_originalFamilyStalkReduction172_surjective b hb q hq p hp he P)
    (RingHom.ker b) (smoothCubic_artin_residueKernel_isNilpotent172 b hb)
    (smoothCubic_originalFamilyStalkReduction172_ker b hb q hq p hp he P) J
    (smoothCubic_embeddedOriginalPointStalkIdeal173_image b hb q hq p hp he P i u0 H)

end PfaffianDescent
