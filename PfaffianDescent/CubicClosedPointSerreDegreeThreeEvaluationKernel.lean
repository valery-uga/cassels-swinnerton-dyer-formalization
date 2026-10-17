import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationDimension
import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationMap
import PfaffianDescent.VoisinSectionLinearAlgebra

/-! # A nonzero actual bundle section vanishing at the degree-three point -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Nine actual global sections leave a nonzero kernel in the actual
pullback evaluation at a degree-three field point. Target coordinates and
its dimension are constructed from the actual rank-two cover. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationKernel_exists_nonzero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {M : X.Modules} (base : X ⟶ Spec (.of K))
    (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (j : Spec (.of L) ⟶ X)
    (hj : j ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : Module.finrank K L = 3)
    (hsections : 9 ≤ Module.finrank K
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))) :
    ∃ s : SchemeModuleGlobalSectionsOver base (show X.Modules from e.E),
      s ≠ 0 ∧ cubicClosedPointSerreDegreeThreeEvaluationMap base j
        (show X.Modules from e.E) s = 0 := by
  let V := SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)
  let W := SchemeModuleGlobalSectionsOver (j ≫ base)
    ((Scheme.Modules.pullback j).obj (show X.Modules from e.E))
  letI : FiniteDimensional K V := Module.finite_of_finrank_pos (by
    change 0 < Module.finrank K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))
    omega)
  have htarget : Module.finrank K W = 6 :=
    cubicClosedPointSerreDegreeThreeEvaluationDimension_finrank_eq_six base e C j hj hL
  letI : FiniteDimensional K W := Module.finite_of_finrank_pos (by rw [htarget]; omega)
  exact exists_ne_zero_mem_ker_of_finrank_lt
    (cubicClosedPointSerreDegreeThreeEvaluationMap base j (show X.Modules from e.E)) (by
      change Module.finrank K W < Module.finrank K V
      change 9 ≤ Module.finrank K V at hsections
      omega)

/-- The kernel section is nonzero as an actual compatible family, and its
literal geometric pullback is the zero section on the actual point. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationKernel_exists_nonzero_section
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {M : X.Modules} (base : X ⟶ Spec (.of K))
    (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (j : Spec (.of L) ⟶ X)
    (hj : j ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : Module.finrank K L = 3)
    (hsections : 9 ≤ Module.finrank K
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))) :
    ∃ s : e.E.sections, s ≠ SerreExtensionData.zeroSection e.E ∧
      BundleSectionZeroLocus.pullbackSection j (show X.Modules from e.E)
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison j) s =
          SerreExtensionData.zeroSection
            ((Scheme.Modules.pullback j).obj (show X.Modules from e.E)) := by
  obtain ⟨s, hs, hzero⟩ := cubicClosedPointSerreDegreeThreeEvaluationKernel_exists_nonzero
    base e C j hj hL hsections
  refine ⟨e.E.unitHomEquiv s, ?_, ?_⟩
  · intro hz
    apply hs
    have h := congrArg e.E.unitHomEquiv.symm hz
    simpa only [Equiv.symm_apply_apply, SerreExtensionData.unitHomEquiv_symm_zeroSection] using h
  · apply ((Scheme.Modules.pullback j).obj (show X.Modules from e.E)).unitHomEquiv.symm.injective
    rw [BundleSectionZeroLocus.pullbackSection_unitHomEquiv_symm_eq_inv,
      Equiv.symm_apply_apply, SerreExtensionData.unitHomEquiv_symm_zeroSection]
    exact hzero

end PfaffianDescent
