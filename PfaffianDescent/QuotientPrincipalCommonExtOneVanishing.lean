import PfaffianDescent.SchemeCoverDegreeZeroAcyclic
import PfaffianDescent.QuotientPrincipalPointCommonCover

/-! # Actual acyclicity of the common point and projective cover -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {σ : Type} [Finite σ]
local notation "AA" => MvPolynomial.homogeneousSubmodule σ K

set_option backward.isDefEq.respectTransparency false in
/-- Every actual common-cover member is acyclic for the negative twist.
Its affine geometry and twist trivialization are constructed, not assumed. -/
theorem quotientPrincipalPointCommon_member_ext_one_subsingleton
    (I : HomogeneousIdeal AA) [hExt : HasExt.{u} (Proj (grading I)).Modules]
    [IsAffineHom (pullback.diagonal (terminal.from (Proj (grading I))))]
    (U : (Proj (grading I)).Opens) (hU : IsAffineOpen U)
    (x : Proj (grading I)) (q f : Γ(Proj (grading I), U)) (m : ℕ)
    (a : PointAdaptedAffineCover.PrincipalIndex (Proj (grading I)) x × ULift.{u} σ) :
    Subsingleton (Ext.{u} (C := (Proj (grading I)).Modules)
      (sectionRepresenter (Proj (grading I)).ringCatSheaf
        (quotientPrincipalPointCommonOpens I U x q f a))
      (sheafOfModules (grading I) m) 1) := by
  let W := quotientPrincipalPointCommonOpens I U x q f a
  have hW : IsAffineOpen W := quotientPrincipalPointCommonOpens_isAffineOpen I U hU x q f a
  letI : IsLocallyNoetherian (Proj (grading I)) := quotientProj_isLocallyNoetherian I
  letI : IsAffine (W : Scheme) := hW
  letI : IsNoetherianRing Γ((W : Scheme), ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (W : Scheme)⟩
  let e : (Scheme.Modules.restrictFunctor W.ι).obj (sheafOfModules (grading I) m) ≅
      SheafOfModules.unit (W : Scheme).ringCatSheaf :=
    quotientNegativeTwistOpenIsoUnit I W a.2.down inf_le_right m
  exact (sectionRepresenter_ext_one_and_two_subsingleton_of_affineOpen_of_restrictIsoUnit
    W hW (sheafOfModules (grading I) m) e).1

set_option backward.isDefEq.respectTransparency false in
/-- The infinite common-cover zero term has vanishing Ext¹, supplying the
boundary-detection hypothesis internally. -/
theorem quotientPrincipalPointCommon_degree_zero_ext_one_subsingleton
    (I : HomogeneousIdeal AA) [hExt : HasExt.{u} (Proj (grading I)).Modules]
    [IsAffineHom (pullback.diagonal (terminal.from (Proj (grading I))))]
    (U : (Proj (grading I)).Opens) (hU : IsAffineOpen U)
    (x : Proj (grading I)) (q f : Γ(Proj (grading I), U)) (m : ℕ) :
    Subsingleton (Ext.{u} (C := (Proj (grading I)).Modules)
      ((sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
        (quotientPrincipalPointCommonOpens I U x q f)).X 0)
      (sheafOfModules (grading I) m) 1) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading I)).ringCatSheaf) := hExt
  letI : ∀ a, Subsingleton (Ext.{u} (C := (Proj (grading I)).Modules)
      (sectionRepresenter (Proj (grading I)).ringCatSheaf
        (quotientPrincipalPointCommonOpens I U x q f a))
      (sheafOfModules (grading I) m) 1) :=
    fun a => quotientPrincipalPointCommon_member_ext_one_subsingleton I U hU x q f m a
  exact schemeCover_degree_zero_ext_one_subsingleton
    (quotientPrincipalPointCommonOpens I U x q f) (sheafOfModules (grading I) m)
end PfaffianDescent.ProjectiveNegativeTwist
