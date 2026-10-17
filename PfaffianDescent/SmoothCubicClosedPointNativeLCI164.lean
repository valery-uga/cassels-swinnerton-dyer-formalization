import PfaffianDescent.RegularPairNativeRegularSequence164
import PfaffianDescent.SmoothPointKoszulParameters
import AllCharacteristics.SmoothSchemeRegularity
import AllCharacteristics.ProjectiveHypersurfaceClosedDimension
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! SOURCE ONLY / UNVERIFIED164. ORIGINAL closed point of an ORIGINAL
smooth cubic over ANY field: native regular-sequence generators of the
ENTIRE actual residue kernel, and actual affine germs near that point.
No perfection, separability, finite/infinite residue-field or char0 premise.
No Hilbert functor, lifting certificate or native LCI predicate is defined. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The exact local-ring premise in lem:lift: two actual parameters are a
native regular sequence and generate the kernel of the ORIGINAL closed
point's actual scheme residue map. All geometric inputs are derived. -/
theorem smoothCubic_originalClosedPoint_residueKernel_regularSequence164
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (P : closedPoints (hypersurface p hp)) :
    ∃ f g : (hypersurface p hp).presheaf.stalk P.1,
      RingTheory.Sequence.IsRegular ((hypersurface p hp).presheaf.stalk P.1) [f, g] ∧
      Ideal.span ({f, g} : Set ((hypersurface p hp).presheaf.stalk P.1)) =
        RingHom.ker (((hypersurface p hp).residue P.1).hom) := by
  let S := hypersurface p hp
  let A := S.presheaf.stalk P.1
  let pi := hypersurfaceToBase p hp
  letI : IsRegularRing Γ(Spec (.of K), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  letI : IsRegularLocalRing A :=
    AllCharacteristics.isRegularLocalRing_stalk_of_smooth_over_affine pi P.1
  have hdim : ringKrullDim A = 2 :=
    ringKrullDim_stalk_projective_hypersurface_eq_two p hp hp0 P.1 P.2
  obtain ⟨f, g, hf, hg, hspan⟩ := exists_regular_pair_span_maximalIdeal_of_dim_two hdim
  have hreg := regularPair_span_maximalIdeal_isRegular164 f g hf hg hspan
  have hker : RingHom.ker ((S.residue P.1).hom) = IsLocalRing.maximalIdeal A := by
    change RingHom.ker (IsLocalRing.residue A) = IsLocalRing.maximalIdeal A
    exact IsLocalRing.ker_residue
  exact ⟨f, g, hreg, hspan.trans hker.symm⟩

/-- ORIGINAL closed point admits two actual affine sections in every
prescribed neighborhood, regular at P with full original residue kernel,
and no other common zero. Regularity at OTHER points is not asserted. -/
theorem smoothCubic_originalClosedPoint_affine_residueKernel_parameters164
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (P : closedPoints (hypersurface p hp))
    (O : (hypersurface p hp).Opens) (hPO : P.1 ∈ O) :
    ∃ (W : (hypersurface p hp).Opens) (_hW : IsAffineOpen W) (hPW : P.1 ∈ W)
      (f g : Γ(hypersurface p hp, W)), W ≤ O ∧
      (hypersurface p hp).presheaf.germ W P.1 hPW f ∈
        ((hypersurface p hp).presheaf.stalk P.1)⁰ ∧
      Ideal.Quotient.mk
          (Ideal.span {(hypersurface p hp).presheaf.germ W P.1 hPW f})
          ((hypersurface p hp).presheaf.germ W P.1 hPW g) ∈
        (((hypersurface p hp).presheaf.stalk P.1) ⧸
          Ideal.span {(hypersurface p hp).presheaf.germ W P.1 hPW f})⁰ ∧
      Ideal.span ({(hypersurface p hp).presheaf.germ W P.1 hPW f,
        (hypersurface p hp).presheaf.germ W P.1 hPW g} :
          Set ((hypersurface p hp).presheaf.stalk P.1)) =
        RingHom.ker (((hypersurface p hp).residue P.1).hom) ∧
      ∀ (z : hypersurface p hp) (hz : z ∈ W), z ≠ P.1 →
        Ideal.span ({(hypersurface p hp).presheaf.germ W z hz f,
          (hypersurface p hp).presheaf.germ W z hz g} :
            Set ((hypersurface p hp).presheaf.stalk z)) = ⊤ := by
  let S := hypersurface p hp
  let pi := hypersurfaceToBase p hp
  letI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian pi
  letI : IsRegularRing Γ(Spec (.of K), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  letI : IsRegularLocalRing (S.presheaf.stalk P.1) :=
    AllCharacteristics.isRegularLocalRing_stalk_of_smooth_over_affine pi P.1
  have hdim : ringKrullDim (S.presheaf.stalk P.1) = 2 :=
    ringKrullDim_stalk_projective_hypersurface_eq_two p hp hp0 P.1 P.2
  obtain ⟨W, hW, hPW, f, g, hWO, hf, hg, hspan, hzero⟩ :=
    exists_affine_point_koszul_parameters P.1 hdim P.2 O hPO
  have hker : RingHom.ker ((S.residue P.1).hom) =
      IsLocalRing.maximalIdeal (S.presheaf.stalk P.1) := by
    change RingHom.ker (IsLocalRing.residue (S.presheaf.stalk P.1)) =
      IsLocalRing.maximalIdeal (S.presheaf.stalk P.1)
    exact IsLocalRing.ker_residue
  exact ⟨W, hW, hPW, f, g, hWO, hf, hg, hspan.trans hker.symm, hzero⟩

end PfaffianDescent
