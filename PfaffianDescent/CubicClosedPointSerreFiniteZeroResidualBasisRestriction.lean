import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodStalkIsoTransport
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalStalk

/-! # Actual restriction transports scalar coordinate ideals on stalks -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_restrictionBasis
    {X : Scheme.{u}} (U : X.Opens) (x : U) (E : X.Modules) :
    letI : Module (X.presheaf.stalk (U.ι x)) (E.presheaf.stalk (U.ι x)) :=
      schemeModuleStalkModule E (U.ι x)
    letI : Module ((U : Scheme).presheaf.stalk x) ((E.restrict U.ι).presheaf.stalk x) :=
      schemeModuleStalkModule (E.restrict U.ι) x
    ((E.restrict U.ι).presheaf.stalk x ≃ₗ[(U : Scheme).presheaf.stalk x]
      (((U : Scheme).presheaf.stalk x) × ((U : Scheme).presheaf.stalk x))) →
    (E.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((X.presheaf.stalk (U.ι x)) × (X.presheaf.stalk (U.ι x)))) := by
  dsimp only
  letI := schemeModuleStalkModule E (U.ι x)
  letI := schemeModuleStalkModule (E.restrict U.ι) x
  intro t
  let a : (E.restrict U.ι).presheaf.stalk x ≃+ E.presheaf.stalk (U.ι x) :=
    ((Scheme.Modules.restrictStalkNatIso U.ι x).app E).addCommGroupIsoToAddEquiv
  let σ : X.presheaf.stalk (U.ι x) ≃+* (U : Scheme).presheaf.stalk x :=
    (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
  refine
    { toAddEquiv := a.symm.trans
        (t.toAddEquiv.trans (σ.symm.toAddEquiv.prodCongr σ.symm.toAddEquiv))
      map_smul' := ?_ }
  intro r m
  have ha := schemeModuleRestrictStalk_inv_smul U x E r m
  change a.symm (r • m) = σ r • a.symm m at ha
  change (σ.symm ((t (a.symm (r • m))).1),
    σ.symm ((t (a.symm (r • m))).2)) =
      r • (σ.symm ((t (a.symm m)).1), σ.symm ((t (a.symm m)).2))
  rw [ha, t.map_smul]
  ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    map_mul, RingEquiv.symm_apply_apply]

theorem cubicClosedPointSerreFiniteZeroResidual_restrictionBasis_span
    {X : Scheme.{u}} (U : X.Opens) (x : U) (E : X.Modules) :
    letI : Module (X.presheaf.stalk (U.ι x)) (E.presheaf.stalk (U.ι x)) :=
      schemeModuleStalkModule E (U.ι x)
    letI : Module ((U : Scheme).presheaf.stalk x) ((E.restrict U.ι).presheaf.stalk x) :=
      schemeModuleStalkModule (E.restrict U.ι) x
    ∀ (t : (E.restrict U.ι).presheaf.stalk x ≃ₗ[(U : Scheme).presheaf.stalk x]
        (((U : Scheme).presheaf.stalk x) × ((U : Scheme).presheaf.stalk x)))
      (m : E.presheaf.stalk (U.ι x)),
      Ideal.map (U.ι.stalkMap x).hom
        (Ideal.span ({(cubicClosedPointSerreFiniteZeroResidual_restrictionBasis U x E t m).1,
          (cubicClosedPointSerreFiniteZeroResidual_restrictionBasis U x E t m).2} :
          Set (X.presheaf.stalk (U.ι x)))) =
      Ideal.span ({
        (t ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app E m)).1,
        (t ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app E m)).2} :
        Set ((U : Scheme).presheaf.stalk x)) := by
  dsimp only
  intro t m
  rw [Ideal.map_span, Set.image_pair]
  let σ := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
  change Ideal.span ({σ (σ.symm _), σ (σ.symm _)} :
    Set ((U : Scheme).presheaf.stalk x)) = _
  simp only [RingEquiv.apply_symm_apply]
  rfl

theorem cubicClosedPointSerreFiniteZeroResidual_restriction_maximalIdeal
    {X : Scheme.{u}} (U : X.Opens) (x : U) :
    Ideal.map (U.ι.stalkMap x).hom (IsLocalRing.maximalIdeal (X.presheaf.stalk (U.ι x))) =
      IsLocalRing.maximalIdeal ((U : Scheme).presheaf.stalk x) := by
  rw [← IsLocalRing.maximalIdeal_comap (U.ι.stalkMap x).hom]
  exact Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap x)).surjective _

end PfaffianDescent
