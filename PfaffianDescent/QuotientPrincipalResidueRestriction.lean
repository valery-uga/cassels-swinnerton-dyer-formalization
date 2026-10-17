import PfaffianDescent.QuotientPrincipalPointCommonCover
import PfaffianDescent.SectionRepresenterScalar

/-! # The local residue section on the actual common projective cover -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {σ : Type} [Finite σ]
local notation "AA" => MvPolynomial.homogeneousSubmodule σ K

set_option backward.isDefEq.respectTransparency false in
/-- A computed principal triple coefficient restricts literally to every
coordinate triple of the common cover, with no coefficient transport assumed. -/
theorem quotientPrincipalResidue_common_coefficient
    (I : HomogeneousIdeal AA) (U : (Proj (grading I)).Opens)
    (x : Proj (grading I)) (q f : Γ(Proj (grading I), U))
    (Y : (Proj (grading I)).Modules)
    (h : (sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
      (PointAdaptedAffineCover.principalOpens U x q f)).X 2 ⟶ Y)
    (s : Fin 3 → PointAdaptedAffineCover.PrincipalIndex (Proj (grading I)) x)
    (v : Y.val.obj (op (∏ᶜ fun k : Fin 3 =>
      PointAdaptedAffineCover.principalOpens U x q f (s k))))
    (hv : Sigma.ι (fun g : Fin 3 → PointAdaptedAffineCover.PrincipalIndex (Proj (grading I)) x =>
      sectionRepresenter (Proj (grading I)).ringCatSheaf
        (∏ᶜ fun k : Fin 3 => PointAdaptedAffineCover.principalOpens U x q f (g k))) s ≫ h =
      sectionRepresenterAugmentation (Proj (grading I)).ringCatSheaf _ Y v)
    (j : Fin 3 → ULift.{u} σ) :
    sectionRepresenterCechHomEquivPi (Proj (grading I)).ringCatSheaf
      (quotientPrincipalPointCommonOpens I U x q f) Y 2
      ((quotientPrincipalPointCommonToPrincipalChain I U x q f).f 2 ≫ h)
      (fun k => (s k, j k)) =
    Y.val.map (CategoryTheory.Limits.Pi.map (fun k : Fin 3 =>
      (homOfLE inf_le_left : quotientPrincipalPointCommonOpens I U x q f (s k, j k) ⟶
        PointAdaptedAffineCover.principalOpens U x q f (s k)))).op v := by
  let P := PointAdaptedAffineCover.principalOpens U x q f
  let W := quotientPrincipalPointCommonOpens I U x q f
  let a : Fin 3 → PointAdaptedAffineCover.PrincipalIndex (Proj (grading I)) x × ULift.{u} σ :=
    fun k => (s k, j k)
  let ρ : (∏ᶜ fun k : Fin 3 => W (a k)) ⟶ (∏ᶜ fun k : Fin 3 => P (s k)) :=
    CategoryTheory.Limits.Pi.map (fun k : Fin 3 =>
      (homOfLE inf_le_left : W (a k) ⟶ P (s k)))
  have hc : sectionRepresenterCechHomEquivPi (Proj (grading I)).ringCatSheaf
      P Y 2 h s = v :=
    (congrArg (sectionRepresenterHomEquiv (Proj (grading I)).ringCatSheaf
      (∏ᶜ fun k : Fin 3 => P (s k)) Y) hv).trans
      (sectionRepresenterHomEquiv_augmentation (Proj (grading I)).ringCatSheaf _ Y v)
  have hr : sectionRepresenterCechHomEquivPi (Proj (grading I)).ringCatSheaf
      W Y 2 ((quotientPrincipalPointCommonToPrincipalChain I U x q f).f 2 ≫ h) a =
      Y.val.map ρ.op (sectionRepresenterCechHomEquivPi (Proj (grading I)).ringCatSheaf
        P Y 2 h s) :=
    sectionRepresenterCechHomEquivPi_refinement (Proj (grading I)).ringCatSheaf
      P W Prod.fst (fun _ => homOfLE inf_le_left) Y 2 h a
  exact hr.trans (congrArg (Y.val.map ρ.op) hc)

end PfaffianDescent.ProjectiveNegativeTwist
