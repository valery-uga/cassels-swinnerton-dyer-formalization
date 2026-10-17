import PfaffianDescent.CubicCanonicalPointLaurentEvaluation
import PfaffianDescent.P3RawLaurentPolynomialEvaluation

/-! # Polynomial coefficient formula for the canonical closed-point pullback -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Opposite MvPolynomial AllCharacteristics.HomogeneousProjective
open scoped nonZeroDivisors
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentCechExact LaurentLocalization
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
local notation "CS" => Proj (grading (equationIdeal p hp))

set_option backward.isDefEq.respectTransparency false in
/-- The actual canonical restriction to a closed field point, applied to
its explicit Koszul class, has the native Laurent residue formula. No
trace-residue compatibility or class-comparison equality is assumed. -/
theorem exists_cubic_canonical_point_laurent_polynomial_evaluation
    (hp0 : p ≠ 0) [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules] [hExt : HasExt.{u} (CS).Modules]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ CS) [IsClosedImmersion i]
    [IsAffineHom (pullback.diagonal (terminal.from CS))]
    {J : Type u} (V : J → (CS).Opens)
    (hV : (Opens.grothendieckTopology CS).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor (CS).ringCatSheaf (V j)).obj
      (SheafOfModules.unit (CS).ringCatSheaf) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver (CS).sheaf (V j))))
    (U : (CS).Opens) (hU : IsAffineOpen U) (hx : i default ∈ U) (q f : Γ(CS, U))
    (hqmax : (CS).presheaf.germ U (i default) hx q ∈ IsLocalRing.maximalIdeal
      ((CS).presheaf.stalk (i default)))
    (hfmax : (CS).presheaf.germ U (i default) hx f ∈ IsLocalRing.maximalIdeal
      ((CS).presheaf.stalk (i default)))
    (haway : ∀ (z : CS) (hz : z ∈ U), z ≠ i default →
      Ideal.span ({(CS).presheaf.germ U z hz q, (CS).presheaf.germ U z hz f} :
        Set ((CS).presheaf.stalk z)) = ⊤)
    (hqreg : (CS).presheaf.germ U (i default) hx q ∈ ((CS).presheaf.stalk (i default))⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {(CS).presheaf.germ U (i default) hx q})
      ((CS).presheaf.germ U (i default) hx f) ∈
      (((CS).presheaf.stalk (i default)) ⧸
        Ideal.span {(CS).presheaf.germ U (i default) hx q})⁰)
    (y : (sheafOfModules (grading (equationIdeal p hp)) 3).val.obj (op U)) :
    letI := schemeModuleStalkModule (show (CS).Modules from
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
      (i default)
    ∀ (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap
      i (i default)) = Ideal.span ({(CS).presheaf.germ U (i default) hx q,
        (CS).presheaf.germ U (i default) hx f} : Set _)),
    let qM := closedImmersionUnitTwistStalkQuotientIso i (i default)
      ((CS).presheaf.germ U (i default) hx q) ((CS).presheaf.germ U (i default) hx f) hkernel
    ∃ (w : QuotientCechDegreeTwoCocycle (equationIdeal p hp) 3)
      (d : CubicNegativeThreeCechLift K p hp (cubicSurfaceCocycleToPushforward K p hp 3 w)),
      ∀ r : homogeneousSubmodule (Fin 4) K 2,
      cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0
        ((Ext.mk₀ (C := (CS).Modules)
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
            (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp
          (fieldPointSectionRepresenterKoszulDegreeTwoClass i (SheafOfModules.unit (CS).ringCatSheaf)
            V hV eV U hx q f qM haway hqreg hfreg
            (sheafOfModules (grading (equationIdeal p hp)) 3) y) (zero_add 2)) r =
      (polynomialToLaurent (K := K) (r : MvPolynomial (Fin 4) K) *
        (p3NegativeTwistCechTermToLaurent K 6 3
          (cubicNegativeThreeLiftRawBoundary K p hp
            (cubicSurfaceCocycleToPushforward K p hp 3 w) d).1) id).coeff
        (p3SerreDualExponent 0) := by
  dsimp only
  letI := schemeModuleStalkModule (show (CS).Modules from
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (i default)
  letI : HasExt.{u} (SheafOfModules.{u} (CS).ringCatSheaf) := hExt
  intro hkernel
  obtain ⟨w, d, heval⟩ := exists_cubic_canonical_point_laurent_evaluation
    K p hp hp0 i V hV eV U hU hx q f hqmax hfmax haway hqreg hfreg y hkernel
  refine ⟨w, d, ?_⟩
  intro r
  exact (congrArg (fun phi : Module.Dual K (homogeneousSubmodule (Fin 4) K 2) => phi r)
    heval).trans (p3NegativeSix_raw_residue_dual_apply_quadratic K
      (cubicNegativeThreeLiftRawBoundary K p hp
        (cubicSurfaceCocycleToPushforward K p hp 3 w) d) r)

end PfaffianDescent.ProjectiveNegativeTwist
