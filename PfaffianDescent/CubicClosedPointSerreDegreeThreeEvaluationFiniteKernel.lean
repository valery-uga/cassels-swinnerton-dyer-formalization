import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationFiniteDimension
import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationKernel

/-! # A nonzero section vanishing on the actual rank-three finite datum -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Zero in the actual evaluation target means that the literal geometric
pullback of the original compatible section is the zero section. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationMap_eq_zero_iff_pullbackSection
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (j : Z ⟶ X) (E : X.Modules)
    (s : SchemeModuleGlobalSectionsOver base E) :
    cubicClosedPointSerreDegreeThreeEvaluationMap base j E s = 0 ↔
      BundleSectionZeroLocus.pullbackSection j E
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison j) (E.unitHomEquiv s) =
          SerreExtensionData.zeroSection ((Scheme.Modules.pullback j).obj E) := by
  let F := (Scheme.Modules.pullback j).obj E
  have h : F.unitHomEquiv.symm
      (BundleSectionZeroLocus.pullbackSection j E
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison j) (E.unitHomEquiv s)) =
      cubicClosedPointSerreDegreeThreeEvaluationMap base j E s := by
    rw [BundleSectionZeroLocus.pullbackSection_unitHomEquiv_symm_eq_inv,
      Equiv.symm_apply_apply]
    rfl
  constructor
  · intro hs
    apply F.unitHomEquiv.symm.injective
    rw [h, hs, SerreExtensionData.unitHomEquiv_symm_zeroSection]
  · intro hs
    have hh := congrArg F.unitHomEquiv.symm hs
    rw [h, SerreExtensionData.unitHomEquiv_symm_zeroSection] at hh
    exact hh

/-- The actual rank-three finite field datum imposes six conditions on
the actual rank-two bundle, so nine sections leave a nonzero actual kernel. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationFiniteKernel_exists_nonzero
    {K : Type u} [Field K] {X : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (D : FiniteSubschemeDatum base 3) (hField : IsField Γ(D.val.subscheme, ⊤))
    (hsections : 9 ≤ Module.finrank K
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))) :
    ∃ s : SchemeModuleGlobalSectionsOver base (show X.Modules from e.E),
      s ≠ 0 ∧ cubicClosedPointSerreDegreeThreeEvaluationMap base D.val.subschemeι
        (show X.Modules from e.E) s = 0 := by
  let V := SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)
  let W := SchemeModuleGlobalSectionsOver (D.val.subschemeι ≫ base)
    ((Scheme.Modules.pullback D.val.subschemeι).obj (show X.Modules from e.E))
  letI : FiniteDimensional K V := Module.finite_of_finrank_pos (by
    change 0 < Module.finrank K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))
    omega)
  have htarget : Module.finrank K W = 6 :=
    cubicClosedPointSerreDegreeThreeEvaluationFiniteDimension_finrank_eq_six base e C D hField
  letI : FiniteDimensional K W := Module.finite_of_finrank_pos (by rw [htarget]; omega)
  exact exists_ne_zero_mem_ker_of_finrank_lt
    (cubicClosedPointSerreDegreeThreeEvaluationMap base D.val.subschemeι
      (show X.Modules from e.E)) (by
        change Module.finrank K W < Module.finrank K V
        change 9 ≤ Module.finrank K V at hsections
        omega)

/-- This is an actual nonzero compatible section of the original bundle
whose actual pullback to the finite datum itself is zero. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationFiniteKernel_exists_nonzero_section
    {K : Type u} [Field K] {X : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (D : FiniteSubschemeDatum base 3) (hField : IsField Γ(D.val.subscheme, ⊤))
    (hsections : 9 ≤ Module.finrank K
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))) :
    ∃ s : e.E.sections, s ≠ SerreExtensionData.zeroSection e.E ∧
      BundleSectionZeroLocus.pullbackSection D.val.subschemeι (show X.Modules from e.E)
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison D.val.subschemeι) s =
          SerreExtensionData.zeroSection
            ((Scheme.Modules.pullback D.val.subschemeι).obj (show X.Modules from e.E)) := by
  obtain ⟨s, hs, hz⟩ := cubicClosedPointSerreDegreeThreeEvaluationFiniteKernel_exists_nonzero
    base e C D hField hsections
  refine ⟨e.E.unitHomEquiv s, ?_, ?_⟩
  · intro h
    apply hs
    have hh := congrArg e.E.unitHomEquiv.symm h
    simpa only [Equiv.symm_apply_apply, SerreExtensionData.unitHomEquiv_symm_zeroSection] using hh
  · exact (cubicClosedPointSerreDegreeThreeEvaluationMap_eq_zero_iff_pullbackSection
      base D.val.subschemeι (show X.Modules from e.E) s).mp hz

end PfaffianDescent
