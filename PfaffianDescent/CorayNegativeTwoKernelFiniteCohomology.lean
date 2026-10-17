import PfaffianDescent.CorayNegativeFiniteCoproductCohomology
import PfaffianDescent.CorayFourAffineCoverCohomologicalDimension
import PfaffianDescent.CorayNativeTwoKernelFiniteCohomology

/-! SOURCE ONLY / UNVERIFIED downstream two-kernel theorem. Its generic
Ext and actual negative free-term prerequisites are imported, not redefined. -/
noncomputable section

namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Isolate the actual second-kernel-to-four-cover conversion. -/
private theorem actualP3_secondKernel_cohomology_four_subsingleton
    (K : Type u) [Field K]
    [hExt : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    {F₀ F₁ J : (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules}
    (a : F₀ ⟶ J) (r : F₁ ⟶ F₀) (hz : r ≫ a = 0)
    [(kernel (kernel.lift a r hz)).IsQuasicoherent] :
    Subsingleton (schemeModuleCohomology
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (kernel (kernel.lift a r hz)) 4) := by
  exact p3_quasicoherent_cohomology_subsingleton_ge_four K
    (kernel (kernel.lift a r hz)) 4 (by decide)

/-- Isolate the actual finite negative coproduct H3 projection, retaining
exactly the canonical original ambient base action. -/
private theorem actualP3_negativeFreeTerm_cohomology_three_finite
    (K : Type u) [Field K]
    [hExt : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    {κ : Type u} [Fintype κ] (e : κ → ℕ) :
    let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    letI : Linear K P.Modules := schemeModulesLinearOver
      (AllCharacteristics.HomogeneousProjective.ambientToBase (R := K) (σ := Fin 4))
    Module.Finite K (schemeModuleCohomology P
      (∐ fun j => sheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) (e j)) 3) := by
  exact (actualNegativeFiniteCoproduct_cohomology_two_zero_three_finite K e).2

/-- Isolate the actual negative coproduct H2 projection. -/
private theorem actualP3_negativeFreeTerm_cohomology_two_subsingleton
    (K : Type u) [Field K]
    [hExt : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    {ι : Type u} [Fintype ι] (d : ι → ℕ) :
    Subsingleton (schemeModuleCohomology
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (∐ fun i => sheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) (d i)) 2) := by
  exact (actualNegativeFiniteCoproduct_cohomology_two_zero_three_finite K d).1

/-- Isolate abstract native two-kernel assembly specialized to ACTUAL P3.
Natural H4/F1H3/F0H2 inputs are derived in the actual public caller. -/
private theorem actualP3_twoKernel_cohomology_two_finite_of_native_inputs
    (K : Type u) [Field K]
    [hExt : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    {F₀ F₁ J : (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules}
    (a : F₀ ⟶ J) (r : F₁ ⟶ F₀) (hz : r ≫ a = 0)
    (h₀ : (ShortComplex.mk (kernel.ι a) a (kernel.condition a)).ShortExact)
    (h₁ : (ShortComplex.mk (kernel.ι (kernel.lift a r hz))
      (kernel.lift a r hz) (kernel.condition (kernel.lift a r hz))).ShortExact) :
    let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    letI : Linear K P.Modules := schemeModulesLinearOver
      (AllCharacteristics.HomogeneousProjective.ambientToBase (R := K) (σ := Fin 4))
    Subsingleton (schemeModuleCohomology P (kernel (kernel.lift a r hz)) 4) →
      Module.Finite K (schemeModuleCohomology P F₁ 3) →
      Subsingleton (schemeModuleCohomology P F₀ 2) →
      Module.Finite K (schemeModuleCohomology P J 2) := by
  exact nativeTwoKernelPresentation_cohomology_two_finite
    (AllCharacteristics.HomogeneousProjective.ambientToBase (R := K) (σ := Fin 4)) a r hz h₀ h₁

/-- A native two-term negative weighted presentation has finite H2 over
ORIGINAL K. Its actual second kernel is only required to be QC, and P3's
actual four-affine cover derives H4=0 internally. No desired finite H2,
Serre/RR/duality theorem or numerical bound is an input. Geometric callers
must construct these literal maps, exactness and QC from their presentation. -/
theorem actualNegativeTwoKernelPresentation_cohomology_two_finite
    (K : Type u) [Field K]
    [hExt : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (e : κ → ℕ)
    (J : (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules)
    (a : (∐ fun i => sheafOfModules
        (MvPolynomial.homogeneousSubmodule (Fin 4) K) (d i)) ⟶ J)
    (r : (∐ fun j => sheafOfModules
        (MvPolynomial.homogeneousSubmodule (Fin 4) K) (e j)) ⟶
      (∐ fun i => sheafOfModules
        (MvPolynomial.homogeneousSubmodule (Fin 4) K) (d i)))
    (hz : r ≫ a = 0)
    (h₀ : (ShortComplex.mk (kernel.ι a) a (kernel.condition a)).ShortExact)
    (h₁ : (ShortComplex.mk (kernel.ι (kernel.lift a r hz))
      (kernel.lift a r hz) (kernel.condition (kernel.lift a r hz))).ShortExact)
    [(kernel (kernel.lift a r hz)).IsQuasicoherent] :
    let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    letI : Linear K P.Modules := schemeModulesLinearOver
      (AllCharacteristics.HomogeneousProjective.ambientToBase (R := K) (σ := Fin 4))
    Module.Finite K (schemeModuleCohomology P J 2) := by
  exact actualP3_twoKernel_cohomology_two_finite_of_native_inputs K a r hz h₀ h₁
    (actualP3_secondKernel_cohomology_four_subsingleton K a r hz)
    (actualP3_negativeFreeTerm_cohomology_three_finite K e)
    (actualP3_negativeFreeTerm_cohomology_two_subsingleton K d)

end PfaffianDescent.Coray
