import PfaffianDescent.SmoothCubicEmbeddedPointRegularPair173
import PfaffianDescent.AffineIdealGermNeighborhood179
import Mathlib.AlgebraicGeometry.Noetherian

/-! Source-only188. ORIGINAL cubic geometry derives Noetherian chart
sections and WHOLE affine ideal germ regularity, then constructs179's
principal regular neighborhood. No chart regularity certificate is input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open scoped nonZeroDivisors
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every ACTUAL affine chart of the smooth original Artin cubic has
Noetherian sections; no chart Noetherianity premise is supplied. -/
lemma smoothCubic_affineSections_noetherian188
    {B : Type u} [CommRing B] [IsArtinianRing B]
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase q hq)] (U : (hypersurface q hq).affineOpens) :
    IsNoetherianRing Γ(hypersurface q hq, U) := by
  letI : IsLocallyNoetherian (hypersurface q hq) :=
    LocallyOfFiniteType.isLocallyNoetherian (hypersurfaceToBase q hq)
  exact IsLocallyNoetherian.component_noetherian U

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/--173's actual embedded kernel is the WHOLE original affine ideal germ.
Its stalk regular pair is derived from the original Cartesian deformation. -/
lemma exists_smoothCubic_wholeAffineIdeal_germ_regular_pair188
    {B K : Type u} [CommRing B] [Field K] [IsArtinianRing B] [IsLocalRing B]
    {Z : Scheme.{u}} (b : B →+* K) (hb : Function.Surjective b)
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase q hq)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (he : q.map b = p) (P : closedPoints (hypersurface p hp))
    (i : Z ⟶ hypersurface q hq) [IsClosedImmersion i] [Flat (i ≫ hypersurfaceToBase q hq)]
    (u0 : Spec ((hypersurface p hp).residueField P.1) ⟶ Z)
    (H : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.1)
      i (hypersurfaceReductionMap b q hq p hp he))
    (U : (hypersurface q hq).affineOpens)
    (hx : hypersurfaceReductionMap b q hq p hp he P.1 ∈ U.1) :
    let x := hypersurfaceReductionMap b q hq p hp he P.1
    ∃ a c : (hypersurface q hq).presheaf.stalk x,
      (i.ker.ideal U).map ((hypersurface q hq).presheaf.germ U.1 x hx).hom =
        Ideal.span ({a, c} : Set ((hypersurface q hq).presheaf.stalk x)) ∧
      a ∈ ((hypersurface q hq).presheaf.stalk x)⁰ ∧
      Ideal.Quotient.mk (Ideal.span ({a} : Set ((hypersurface q hq).presheaf.stalk x))) c ∈
        (((hypersurface q hq).presheaf.stalk x) ⧸
          Ideal.span ({a} : Set ((hypersurface q hq).presheaf.stalk x)))⁰ := by
  obtain ⟨a, c, haJ, hcJ, hgen, ha, hc⟩ :=
    smoothCubic_embeddedOriginalPointStalkIdeal173_regular_pair
      b hb q hq p hp hp0 he P i u0 H
  have hwhole : smoothCubic_embeddedOriginalPointStalkIdeal173 b q hq p hp he P i u0 H =
      (i.ker.ideal U).map ((hypersurface q hq).presheaf.germ U.1
        (hypersurfaceReductionMap b q hq p hp he P.1) hx).hom :=
    closedImmersionStalkAt173_ker_eq_ideal_germ i
      (hypersurfaceReductionMap b q hq p hp he P.1) (u0 default)
      (smoothCubic_embeddedPoint_ambient_eq173 b q hq p hp he P i u0 H) U hx
  exact ⟨a, c, hwhole.symm.trans hgen, ha, hc⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- ORIGINAL cubic caller: construct179's neighborhood pair from the
actual flat Cartesian point deformation. Whole ideal, Noetherian chart,
stalk pair and neighborhood regularity are all DERIVED. -/
lemma exists_smoothCubic_wholeAffinePrincipal_regular_pair188
    {B K : Type u} [CommRing B] [Field K] [IsArtinianRing B] [IsLocalRing B]
    {Z : Scheme.{u}} (b : B →+* K) (hb : Function.Surjective b)
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase q hq)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (he : q.map b = p) (P : closedPoints (hypersurface p hp))
    (i : Z ⟶ hypersurface q hq) [IsClosedImmersion i] [Flat (i ≫ hypersurfaceToBase q hq)]
    (u0 : Spec ((hypersurface p hp).residueField P.1) ⟶ Z)
    (H : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.1)
      i (hypersurfaceReductionMap b q hq p hp he))
    (U : (hypersurface q hq).affineOpens)
    (hx : hypersurfaceReductionMap b q hq p hp he P.1 ∈ U.1) :
    ∃ f : Γ(hypersurface q hq, U),
      f ∉ (U.2.primeIdealOf ⟨hypersurfaceReductionMap b q hq p hp he P.1, hx⟩).asIdeal ∧
      hypersurfaceReductionMap b q hq p hp he P.1 ∈ (hypersurface q hq).basicOpen f ∧
      ∃ a c : Localization.Away f,
        (i.ker.ideal U).map (algebraMap Γ(hypersurface q hq, U) (Localization.Away f)) =
          Ideal.span ({a, c} : Set (Localization.Away f)) ∧
        a ∈ (Localization.Away f)⁰ ∧
        Ideal.Quotient.mk (Ideal.span ({a} : Set (Localization.Away f))) c ∈
          ((Localization.Away f) ⧸ Ideal.span ({a} : Set (Localization.Away f)))⁰ := by
  letI : IsNoetherianRing Γ(hypersurface q hq, U) :=
    smoothCubic_affineSections_noetherian188 q hq U
  obtain ⟨a, c, hgen, ha, hc⟩ := exists_smoothCubic_wholeAffineIdeal_germ_regular_pair188
    b hb q hq p hp hp0 he P i u0 H U hx
  exact exists_affine_principal_regular_pair_of_ideal_germ179 U
    (hypersurfaceReductionMap b q hq p hp he P.1) hx (i.ker.ideal U) a c hgen ha hc

end PfaffianDescent
