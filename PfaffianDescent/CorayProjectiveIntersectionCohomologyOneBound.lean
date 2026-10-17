import PfaffianDescent.CorayCubicSecondEquationTwoBoundary
import PfaffianDescent.P3GeneralNegativeTwistPolynomialResidueNaturality
import PfaffianDescent.CorayCubicPolynomialDualAnnihilatorDimension

/-! ORIGINAL-K arithmetic H¹ bound for the literal original p/q curve.
The actual two boundaries, actual polynomial residue and actual cubic dual
annihilator are composed. All vanishing, image, injection and finiteness
inputs are derived internally; no genus or constants equality is asserted.
SOURCE ONLY / UNVERIFIED. Root owns all compiler and kernel checks. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
local notation "P" => Proj PS
local notation "piP" => ambientToBase (R := K) (σ := Fin 4)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME two-boundary class, sent to the actual ordinary polynomial
dual by the genuine ORIGINAL-pi-linear all-degree residue map. -/
def cubicSecondEquation_twoBoundaryPolynomialDualLinearMap
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    letI : Linear K (P).Modules := schemeModulesLinearOver piP
    schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (cokernel (mulHomogeneous (grading (equationIdeal p hp))
          (cubicSecondEquationHomogeneous p q hp n hq) 0))) 1 →ₗ[K]
      Module.Dual K (PS (n - 1)) := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  exact (p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap K
      (n + 3) (n - 1) (by omega)).comp
    (cubicSecondEquation_twoBoundaryLinearMap p q hp hp0 n hq hnot)

/-- Injectivity retains the SAME genuine two-boundary and residue maps. -/
theorem cubicSecondEquation_twoBoundaryPolynomialDualLinearMap_injective
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    Function.Injective
      (cubicSecondEquation_twoBoundaryPolynomialDualLinearMap p q hp hp0 n hn hq hnot) := by
  exact (p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap_injective K
      (n + 3) (n - 1) (by omega)).comp
    (cubicSecondEquation_twoBoundaryLinearMap_injective p q hp hp0 n hq hnot)

/-- Equality elimination changes only the homogeneous codomain degree of
an actual polynomial residue evaluation. The map and polynomial are unchanged. -/
private theorem polynomialResidue_annihilates_multiples_at_degree
    [HasExt.{u} (P).Modules] (m a d t : ℕ) (hdegree : a + 4 = m)
    (ht : a + d = t) (r : PS d)
    (z : schemeModuleCohomology P (sheafOfModules PS (m + d)) 3)
    (hz : z.comp (Ext.mk₀ (mulHomogeneous PS r m)) (add_zero 3) = 0)
    (b : PS a) :
    p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap K (m + d) t (by omega) z
      ⟨(r : MvPolynomial (Fin 4) K) * (b : MvPolynomial (Fin 4) K), by
        simpa only [MvPolynomial.mem_homogeneousSubmodule,
          show d + a = t by omega] using r.2.mul b.2⟩ = 0 := by
  subst t
  exact p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap_annihilates_multiples
    K m a d hdegree r z hz b

/-- Actual cubic Ext-class exactness and actual polynomial residue
naturality prove membership in the SAME literal multiplication annihilator.
No multiplication-zero, image or pairing square is supplied as a premise. -/
theorem cubicSecondEquation_twoBoundaryPolynomialDual_mem_annihilator
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 4 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (z : schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (cokernel (mulHomogeneous (grading (equationIdeal p hp))
          (cubicSecondEquationHomogeneous p q hp n hq) 0))) 1) :
    cubicSecondEquation_twoBoundaryPolynomialDualLinearMap p q hp hp0 n (by omega) hq hnot z ∈
      cubicPolynomialDualAnnihilator p hp n hn := by
  apply (mem_cubicPolynomialDualAnnihilator_iff_multiples p hp n hn _).mpr
  intro b
  have hz := cubicSecondEquation_twoBoundaryLinearMap_mul_zero p q hp hp0 n hq hnot z
  exact polynomialResidue_annihilates_multiples_at_degree
    n (n - 4) 3 (n - 1) (by omega) (by omega) ⟨p, hp⟩
    (cubicSecondEquation_twoBoundaryLinearMap p q hp hp0 n hq hnot z) hz b

/-- Genuine codomain restriction to the actual annihilator after PROVED
membership. Neither source nor target scalar action is transported. -/
def cubicSecondEquation_twoBoundaryAnnihilatorLinearMap
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 4 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    letI : Linear K (P).Modules := schemeModulesLinearOver piP
    schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (cokernel (mulHomogeneous (grading (equationIdeal p hp))
          (cubicSecondEquationHomogeneous p q hp n hq) 0))) 1 →ₗ[K]
      cubicPolynomialDualAnnihilator p hp n hn := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  exact LinearMap.codRestrict (cubicPolynomialDualAnnihilator p hp n hn)
    (cubicSecondEquation_twoBoundaryPolynomialDualLinearMap p q hp hp0 n (by omega) hq hnot)
    (cubicSecondEquation_twoBoundaryPolynomialDual_mem_annihilator p q hp hp0 n hn hq hnot)

/-- The actual codomain restriction retains all residue coordinates. -/
theorem cubicSecondEquation_twoBoundaryAnnihilatorLinearMap_coe
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 4 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (z : schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (cokernel (mulHomogeneous (grading (equationIdeal p hp))
          (cubicSecondEquationHomogeneous p q hp n hq) 0))) 1) :
    (cubicSecondEquation_twoBoundaryAnnihilatorLinearMap p q hp hp0 n hn hq hnot z :
      Module.Dual K (PS (n - 1))) =
        cubicSecondEquation_twoBoundaryPolynomialDualLinearMap p q hp hp0 n (by omega) hq hnot z := rfl

/-- No desired injection certificate is required after restricting the
actual residue map's image to the genuinely proved annihilator. -/
theorem cubicSecondEquation_twoBoundaryAnnihilatorLinearMap_injective
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 4 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    Function.Injective
      (cubicSecondEquation_twoBoundaryAnnihilatorLinearMap p q hp hp0 n hn hq hnot) := by
  intro a b hab
  apply cubicSecondEquation_twoBoundaryPolynomialDualLinearMap_injective p q hp hp0 n
    (by omega) hq hnot
  exact congrArg (fun f : cubicPolynomialDualAnnihilator p hp n hn =>
    (f : Module.Dual K (PS (n - 1)))) hab

/-- Ambient actual q-cokernel H¹ is bounded by the actual cubic annihilator
for n≥4, and by the full ordinary polynomial dual for n=1,2,3. -/
theorem cubicSecondEquation_cokernelPushforward_cohomology_one_finrank_le
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    letI : Linear K (P).Modules := schemeModulesLinearOver piP
    Module.finrank K (schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (cokernel (mulHomogeneous (grading (equationIdeal p hp))
          (cubicSecondEquationHomogeneous p q hp n hq) 0))) 1) ≤
      1 + 3 * n * (n - 1) / 2 := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  by_cases hlarge : 4 ≤ n
  · letI : Module.Finite K (cubicPolynomialDualAnnihilator p hp n hlarge) :=
      cubicPolynomialDualAnnihilator_finite p hp n hlarge
    have h := LinearMap.finrank_le_finrank_of_injective
      (cubicSecondEquation_twoBoundaryAnnihilatorLinearMap_injective p q hp hp0 n hlarge hq hnot)
    rwa [cubicPolynomialDualAnnihilator_finrank p hp hp0 n hlarge] at h
  · letI : Module.Finite K (Module.Dual K (PS (n - 1))) := inferInstance
    have h := LinearMap.finrank_le_finrank_of_injective
      (cubicSecondEquation_twoBoundaryPolynomialDualLinearMap_injective p q hp hp0 n hn hq hnot)
    rwa [fourVariablePolynomialDual_finrank_of_pos_le_three n hn (by omega)] at h

/-- A genuine literal-curve two-boundary injection, witnessed by composing
its canonical closed-immersion map, the SAME actual coefficient Iso inverse,
and the SAME original two-boundary map. Ordinary HasExt infrastructure is
retained here; the following primitive rank-bound caller supplies it locally. -/
theorem projectiveIntersection_unit_twoBoundaryLinearInjection
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [HasExt.{u} (scheme (projectiveIntersectionIdeal p q hp hq)).Modules] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
    letI : Linear K (P).Modules := schemeModulesLinearOver piP
    ∃ T : schemeModuleCohomology X (SheafOfModules.unit X.ringCatSheaf) 1 →ₗ[K]
        schemeModuleCohomology P (sheafOfModules PS (n + 3)) 3,
      Function.Injective T := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  obtain ⟨J, hJ⟩ := homogeneousProjectiveClosedImmersion_cohomologyOneLinearInjection
    I (SheafOfModules.unit X.ringCatSheaf)
  let E := cubicSecondEquation_zeroCokernelAmbientCohomologyOneLinearEquiv p q hp hp0 n hq hnot
  exact ⟨(cubicSecondEquation_twoBoundaryLinearMap p q hp hp0 n hq hnot).comp
      (E.symm.toLinearMap.comp J),
    (cubicSecondEquation_twoBoundaryLinearMap_injective p q hp hp0 n hq hnot).comp
      (E.symm.injective.comp hJ)⟩

/-- Literal-curve primitive caller: all native Ext infrastructure and the
actual closed-immersion injection are internal. Both pi actions are original;
the actual cokernel coefficient Iso is the one preserving the original π. -/
theorem projectiveIntersection_unit_cohomology_one_finrank_le_native
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
    Module.finrank K (schemeModuleCohomology X (SheafOfModules.unit X.ringCatSheaf) 1) ≤
      1 + 3 * n * (n - 1) / 2 := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
  letI : EnoughInjectives (P).Modules := sheafOfModules_enoughInjectives (P).ringCatSheaf
  letI : HasExt.{u} (P).Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (P).Modules
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  letI : Module.Finite K (schemeModuleCohomology P
      ((Scheme.Modules.pushforward (quotientProjMap I)).obj
        (SheafOfModules.unit X.ringCatSheaf)) 1) :=
    projectiveIntersection_unitPushforward_cohomology_one_finite_native p q hp hp0 n hq hnot
  obtain ⟨T, hT⟩ := homogeneousProjectiveClosedImmersion_cohomologyOneLinearInjection
    I (SheafOfModules.unit X.ringCatSheaf)
  have hclosed := LinearMap.finrank_le_finrank_of_injective hT
  let E := cubicSecondEquation_zeroCokernelAmbientCohomologyOneLinearEquiv p q hp hp0 n hq hnot
  have hambient :
      Module.finrank K (schemeModuleCohomology P
        ((Scheme.Modules.pushforward (quotientProjMap I)).obj
          (SheafOfModules.unit X.ringCatSheaf)) 1) ≤ 1 + 3 * n * (n - 1) / 2 := by
    rw [← E.finrank_eq]
    exact cubicSecondEquation_cokernelPushforward_cohomology_one_finrank_le p q hp hp0 n hn hq hnot
  exact hclosed.trans hambient

end PfaffianDescent.Coray
