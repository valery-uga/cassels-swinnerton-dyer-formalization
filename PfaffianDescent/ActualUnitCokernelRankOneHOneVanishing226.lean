import PfaffianDescent.SchemeModuleOpenTopConnectingLinearExact
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A bounded native LES consequence. The explicit intermediate inputs are
rank-one unit H1, the genuine whole-cokernel ShortExact complex, a nonzero
actual connecting value (or the native connecting AddHom), and whole
quotient H1 vanishing. Original geometric callers must derive these inputs. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual nonzero connecting value fills rank-one unit H1. Exactness
then makes the actual H1(unit)→H1(M) map zero; whole quotient H1 vanishing
makes the SAME map surjective. No finiteness of H1(M) is assumed. -/
theorem actualUnitCokernel_cohomologyOne_subsingleton_of_rankOne_boundaryValue226
    (pi : X ⟶ Spec (.of K)) (M : X.Modules)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M)
    (hphi : (ShortComplex.cokernelSequence (C := X.Modules) phi).ShortExact)
    (c : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      cokernel (C := X.Modules) phi)
    (hc : (Ext.mk₀.{u} (C := X.Modules) c).comp
      (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi) (zero_add 1) ≠ 0) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) →
    Module.finrank K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) = 1 →
    Subsingleton (schemeModuleCohomology X (cokernel (C := X.Modules) phi) 1) →
    Subsingleton (schemeModuleCohomology X M 1) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro hFinite hRank hQuotient
  letI : Module.Finite K (schemeModuleCohomology X
    (SheafOfModules.unit X.ringCatSheaf) 1) := hFinite
  letI : Subsingleton (schemeModuleCohomology X (cokernel (C := X.Modules) phi) 1) :=
    hQuotient
  let S := ShortComplex.cokernelSequence (C := X.Modules) phi
  let b := schemeModuleHomConnectingLinearMapOver pi S hphi
  have hb : b ≠ 0 := by
    intro hzero
    apply hc
    change b c = 0
    rw [hzero]
    rfl
  have hSurjB : Function.Surjective b :=
    surjective_of_nonzero_of_finrank_eq_one hRank hb
  let e := schemeModuleUnitHomGroundLinearEquivOpenTop pi S.X₃
  let delta := schemeModuleOpenTopConnectingLinearMapOver pi S hphi
  have hSurjDelta : Function.Surjective delta := by
    intro z
    obtain ⟨d, hd⟩ := hSurjB z
    refine ⟨e d, ?_⟩
    change b (e.symm (e d)) = z
    rw [e.symm_apply_apply]
    exact hd
  let j := schemeModuleCohomologyLinearMapOver pi S.f 1
  have hExact : Function.Exact delta j :=
    (schemeModuleOpenTopConnectingLinearMaps_exact pi S hphi).2
  have hjZero (z : schemeModuleCohomology X S.X₁ 1) : j z = 0 := by
    obtain ⟨d, rfl⟩ := hSurjDelta z
    exact hExact.apply_apply_eq_zero d
  letI : Subsingleton (schemeModuleCohomology X S.X₃ 1) := hQuotient
  have hjSurj : Function.Surjective j :=
    schemeModuleCohomologyOneMap_surjective_of_quotient_subsingleton pi S hphi
  have hZero (z : schemeModuleCohomology X M 1) : z = 0 := by
    obtain ⟨d, hd⟩ := hjSurj z
    exact hd.symm.trans (hjZero d)
  exact ⟨fun a b => (hZero a).trans (hZero b).symm⟩

/-- The literal native Ext0→Ext1 AddHom endpoint supplied by225 is enough:
its nonzero value is converted through native Ext.mk0 bijectivity. -/
theorem actualUnitCokernel_cohomologyOne_subsingleton_of_rankOne_boundaryNonzero226
    (pi : X ⟶ Spec (.of K)) (M : X.Modules)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M)
    (hphi : (ShortComplex.cokernelSequence (C := X.Modules) phi).ShortExact)
    (hBoundary : (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi).postcomp
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (zero_add 1) ≠ 0) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) →
    Module.finrank K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) = 1 →
    Subsingleton (schemeModuleCohomology X (cokernel (C := X.Modules) phi) 1) →
    Subsingleton (schemeModuleCohomology X M 1) := by
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hBoundary
  change z.comp (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi)
    (zero_add 1) ≠ 0 at hz
  apply actualUnitCokernel_cohomologyOne_subsingleton_of_rankOne_boundaryValue226
    pi M phi hphi (Ext.addEquiv₀ z)
  simpa only [Ext.mk₀_addEquiv₀_apply] using hz

end PfaffianDescent.Coray
