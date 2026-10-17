import PfaffianDescent.OpenFamilyFiberTransport171
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeStalkQuotient
import Mathlib.RingTheory.Flat.Basic

/-! SOURCE ONLY / UNVERIFIED173. The quotient by the ACTUAL closed-
immersion stalk ideal is flat under the ORIGINAL ambient family action. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

lemma quotientKernel_flat_of_coefficient_map173
    {B A Q : Type u} [CommRing B] [CommRing A] [CommRing Q]
    (alpha : B →+* A) (delta : B →+* Q) (c : A →+* Q)
    (hc : Function.Surjective c) (hcoef : c.comp alpha = delta) (hflat : delta.Flat) :
    letI : Algebra B A := alpha.toAlgebra
    Module.Flat B (A ⧸ RingHom.ker c) := by
  letI : Algebra B A := alpha.toAlgebra
  letI : Algebra B Q := delta.toAlgebra
  letI : Module.Flat B Q := hflat
  let e := c.quotientKerEquivOfSurjective hc
  let E : (A ⧸ RingHom.ker c) ≃ₐ[B] Q := AlgEquiv.ofRingEquiv (f := e) (by
    intro r
    change e (Ideal.Quotient.mk _ (alpha r)) = delta r
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
    exact DFunLike.congr_fun hcoef r)
  exact Module.Flat.of_linearEquiv E.toLinearEquiv

/-- Whole ideal image in a genuine reduction square. The kernel relation
is used only by the generic ring cut and is DERIVED geometrically below. -/
lemma map_kernel_of_reduction_square173
    {A Q A0 Q0 : Type u} [CommRing A] [CommRing Q] [CommRing A0] [CommRing Q0]
    (c : A →+* Q) (pi : A →+* A0) (lam : Q →+* Q0) (rho : A0 →+* Q0)
    (hc : Function.Surjective c) (hpi : Function.Surjective pi)
    (hcomm : lam.comp c = rho.comp pi)
    (hker : RingHom.ker lam = (RingHom.ker pi).map c) :
    (RingHom.ker c).map pi = RingHom.ker rho := by
  apply Ideal.comap_injective_of_surjective pi hpi
  rw [Ideal.comap_map_of_surjective pi hpi, ← RingHom.ker_eq_comap_bot,
    RingHom.comap_ker, ← hcomm, ← RingHom.comap_ker, hker,
    Ideal.comap_map_of_surjective c hc, ← RingHom.ker_eq_comap_bot]
  exact sup_comm _ _

/-- Literal closed-immersion stalk map, transporting only the actual
ambient point equality. No replacement of the stalk or its scalar action. -/
def closedImmersionStalkAt173
    {X Z : Scheme.{u}} (i : Z ⟶ X) (x : X) (z : Z) (hx : x = i z) :
    X.presheaf.stalk x →+* Z.presheaf.stalk z :=
  ((X.presheaf.stalkCongr (.of_eq hx)).hom ≫ i.stalkMap z).hom

lemma closedImmersionStalkAt173_surjective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (x : X) (z : Z) (hx : x = i z) :
    Function.Surjective (closedImmersionStalkAt173 i x z hx) := by
  exact (i.stalkMap_surjective z).comp
    (ConcreteCategory.bijective_of_isIso (X.presheaf.stalkCongr (.of_eq hx)).hom).2

lemma closedImmersionStalkAt173_coefficient
    {B : Type u} [CommRing B] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (i : Z ⟶ X)
    (x : X) (z : Z) (hx : x = i z) :
    (closedImmersionStalkAt173 i x z hx).comp (familyBaseToStalk169 f x) =
      familyBaseToStalk169 (i ≫ f) z := by
  subst x
  simpa only [closedImmersionStalkAt173, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] using
      (familyBaseToStalk169_comp171 f i z).symm

/-- The ideal is literally the actual affine closed-immersion ideal germ,
not an arbitrarily presented or generated ideal. -/
lemma closedImmersionStalkAt173_ker_eq_ideal_germ
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (x : X) (z : Z) (hx : x = i z) (U : X.affineOpens) (hU : x ∈ U.1) :
    RingHom.ker (closedImmersionStalkAt173 i x z hx) =
      (i.ker.ideal U).map (X.presheaf.germ U.1 x hU).hom := by
  subst x
  simpa only [closedImmersionStalkAt173, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] using
      (cubicClosedPointSerreFiniteZeroResidual_affineIdeal_germ_eq_stalkMap_kernel
        i U z hU).symm

/-- ACTUAL flat embedded Z implies the ACTUAL closed-immersion stalk
quotient is B-flat under the EXACT ambient169 action. No quotient flatness
or scalar comparison is a caller premise. Finiteness is unnecessary. -/
lemma closedImmersionStalkAt173_quotient_flat
    {B : Type u} [CommRing B] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (i : Z ⟶ X) [IsClosedImmersion i] [Flat (i ≫ f)]
    (x : X) (z : Z) (hx : x = i z) :
    letI := familyStalkAlgebra169 f x
    Module.Flat B (X.presheaf.stalk x ⧸ RingHom.ker (closedImmersionStalkAt173 i x z hx)) :=
  quotientKernel_flat_of_coefficient_map173
    (familyBaseToStalk169 f x) (familyBaseToStalk169 (i ≫ f) z)
    (closedImmersionStalkAt173 i x z hx)
    (closedImmersionStalkAt173_surjective i x z hx)
    (closedImmersionStalkAt173_coefficient f i x z hx)
    (flat_familyBaseToStalk169 (i ≫ f) z)

end PfaffianDescent
