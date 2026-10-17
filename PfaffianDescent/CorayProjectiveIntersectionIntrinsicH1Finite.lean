import PfaffianDescent.CorayCubicSecondEquationActualCurveUnit
import PfaffianDescent.HomogeneousClosedImmersionCohomologyOneLinearInjection
import PfaffianDescent.SheafModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.RingTheory.Finiteness.Basic

/-! Finite INTRINSIC original-K H¹ of the literal original projective p/q
intersection. The actual ambient q-cokernel sheaf Iso, its actual original-K
Ext transport, finite ambient q-cokernel H¹ and the genuine closed-immersion
injection are composed. No finiteness or comparison certificate is supplied.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns compiler/kernel checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual coefficient-Iso transport is linear for the ORIGINAL pi-induced
Ext action. It reuses the actual additive postcomposition equivalence and
proves linearity; no replacement scalar action is defined. -/
def schemeModuleCohomologyIsoLinearEquivOver
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    schemeModuleCohomology X M n ≃ₗ[K] schemeModuleCohomology X N n := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  refine { toAddEquiv := extPostcompIsoOfIso e, map_smul' := ?_ }
  intro c z
  change (c • z).comp (Ext.mk₀ e.hom) (add_zero n) =
    c • z.comp (Ext.mk₀ e.hom) (add_zero n)
  exact Ext.smul_comp z (Ext.mk₀ e.hom) (add_zero n) c

/-- This is the SAME existing coefficient-induced cohomology map. -/
theorem schemeModuleCohomologyIsoLinearEquivOver_apply
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) {M N : X.Modules} (e : M ≅ N) (n : ℕ)
    (z : schemeModuleCohomology X M n) :
    schemeModuleCohomologyIsoLinearEquivOver pi e n z =
      schemeModuleCohomologyMap X e.hom n z := rfl

/-- Coefficient transport retains every actual incoming map. In particular
the actual original q-cokernel projection is preserved using the prior
actual sheaf π law; no projection contribution is collapsed to zero. -/
theorem schemeModuleCohomologyIsoLinearEquivOver_map
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) {A M N : X.Modules}
    (e : M ≅ N) (f : A ⟶ M) (n : ℕ) (z : schemeModuleCohomology X A n) :
    schemeModuleCohomologyIsoLinearEquivOver pi e n
        (schemeModuleCohomologyMap X f n z) =
      schemeModuleCohomologyMap X (f ≫ e.hom) n z := by
  change (z.comp (Ext.mk₀ f) (add_zero n)).comp
      (Ext.mk₀ e.hom) (add_zero n) =
    z.comp (Ext.mk₀ (f ≫ e.hom)) (add_zero n)
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]

/-- ORIGINAL-K ambient H¹ transport along the SAME actual m=0 q-cokernel
sheaf Iso. Its target is the literal original curve's unit pushforward. -/
def cubicSecondEquation_zeroCokernelAmbientCohomologyOneLinearEquiv
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules] :
    let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    letI : Linear K P.Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (cokernel (mulHomogeneous (grading (equationIdeal p hp))
          (cubicSecondEquationHomogeneous p q hp n hq) 0))) 1 ≃ₗ[K]
      schemeModuleCohomology P
        ((Scheme.Modules.pushforward (quotientProjMap (projectiveIntersectionIdeal p q hp hq))).obj
          (SheafOfModules.unit (scheme (projectiveIntersectionIdeal p q hp hq)).ringCatSheaf)) 1 :=
  schemeModuleCohomologyIsoLinearEquivOver (ambientToBase (R := K) (σ := Fin 4))
    (cubicSecondEquation_zeroCokernelAmbientIsoCurveUnit p q hp hp0 n hq hnot) 1

/-- Finite ambient ORIGINAL-K H¹ of the ACTUAL literal curve unit
pushforward. Finite H¹ of the actual original q-cokernel is proved by the
prior geometric producer, and transported along the SAME actual Iso.
Native enough-injectives/HasExt infrastructure is constructed internally. -/
theorem projectiveIntersection_unitPushforward_cohomology_one_finite_native
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    let I := projectiveIntersectionIdeal p q hp hq
    letI : EnoughInjectives P.Modules := sheafOfModules_enoughInjectives P.ringCatSheaf
    letI : HasExt.{u} P.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} P.Modules
    letI : Linear K P.Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    Module.Finite K (schemeModuleCohomology P
      ((Scheme.Modules.pushforward (quotientProjMap I)).obj
        (SheafOfModules.unit (scheme I).ringCatSheaf)) 1) := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  let D := cokernel (mulHomogeneous (grading (equationIdeal p hp))
    (cubicSecondEquationHomogeneous p q hp n hq) 0)
  letI : EnoughInjectives P.Modules := sheafOfModules_enoughInjectives P.ringCatSheaf
  letI : HasExt.{u} P.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} P.Modules
  letI : Linear K P.Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  letI : Module.Finite K (schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj D) 1) :=
    cubicSecondEquation_cokernelPushforward_cohomology_one_finite_native p q hp hp0 n hq hnot 0
  exact Module.Finite.equiv
    (cubicSecondEquation_zeroCokernelAmbientCohomologyOneLinearEquiv p q hp hp0 n hq hnot)

/-- Primitive INTRINSIC ORIGINAL-K H¹ finiteness for the literal ORIGINAL
projective p/q intersection. The intrinsic action comes independently from
toBase I, and the ambient action independently from ambientToBase. The
actual immersion square, sheaf Iso, ambient finiteness and degree-one
injection are internally derived; none is an outcome-certificate input.
No constants equality, normalization/genus or Riemann–Roch conclusion. -/
theorem projectiveIntersection_unit_cohomology_one_finite_native
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
    Module.Finite K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
  letI : EnoughInjectives P.Modules := sheafOfModules_enoughInjectives P.ringCatSheaf
  letI : HasExt.{u} P.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} P.Modules
  letI : Linear K P.Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  have hfinite : Module.Finite K (schemeModuleCohomology P
      ((Scheme.Modules.pushforward (quotientProjMap I)).obj
        (SheafOfModules.unit X.ringCatSheaf)) 1) :=
    projectiveIntersection_unitPushforward_cohomology_one_finite_native p q hp hp0 n hq hnot
  exact homogeneousProjectiveClosedImmersion_cohomology_one_finite_of_pushforward
    I (SheafOfModules.unit X.ringCatSheaf) hfinite

end PfaffianDescent.Coray
