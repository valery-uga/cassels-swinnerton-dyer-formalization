import PfaffianDescent.CubicClosedPointSerreQuotientSectionDimension
import PfaffianDescent.CubicSurfaceUnitSectionDimension
import PfaffianDescent.VoisinCubicSurfaceSerre

/-! # Nine actual global sections of the closed-point Serre sequence

The original ideal has at least eight cubic sections. Structure-sheaf Ext
vanishing makes projection on global sections surjective, and its kernel
is the actual one-dimensional space of constant sections. This calculation
does not assume that the middle sheaf is locally free.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- Every actual positive-three Serre extension at a degree-eleven field
point has at least nine global sections. Neither local freeness nor a
dimension/evaluation certificate is an input. -/
theorem cubicClosedPointSerreSection_finrank_ge_nine
    (K : Type u) [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (hypersurface p hp).Modules]
    (hL : Module.finrank K L = 11)
    (e : SerreExtensionSequenceData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3))) :
    9 ≤ Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E)) := by
  let X := hypersurface p hp
  let base := hypersurfaceToBase p hp
  let I := equationIdeal p hp
  let T := positiveSheafOfModules (grading I) 3
  let Q := closedImmersionIdealTwist i T
  let J := closedImmersionIdealTwistSequence i T
  letI : PreservesFiniteLimits (schemeModuleTensorRight T) :=
    quotientPositiveTwist_tensorRight_preservesFiniteLimits I 3
  let eC := cubicPositiveThreeGlobalSectionsLinearEquiv K p hp hp0
  let eM := cubicClosedPointSerreQuotientSection_globalSectionsIso base
    (closedImmersionIdealTwistSequence_middleIso i T)
  letI : Module.Finite K (grading I 3) := polynomialQuotientGrade_finite I 3
  letI : FiniteDimensional K (SchemeModuleGlobalSectionsOver base J.X₂) :=
    Module.Finite.of_surjective (eC.trans eM.symm).toLinearMap
      (eC.trans eM.symm).surjective
  have hJ : J.ShortExact :=
    quotientPositiveTwist_closedImmersionIdealTwistSequence_shortExact I i 3
  letI : Mono J.f := hJ.mono_f
  let G := schemeModuleGlobalSectionsMap base J.f
  letI : FiniteDimensional K (SchemeModuleGlobalSectionsOver base Q) :=
    FiniteDimensional.of_injective G (fun s t h => (cancel_mono J.f).mp h)
  let eO := cubicSurfaceUnitGlobalSectionsLinearEquiv K p hp hp0
  letI : FiniteDimensional K (SchemeModuleGlobalSectionsOver base (schemeModuleUnit X)) :=
    Module.Finite.of_surjective eO.toLinearMap eO.surjective
  let S : ShortComplex X.Modules := ShortComplex.mk e.inclusion e.projection e.zero
  have hS : S.ShortExact := e.shortExact
  letI : FiniteDimensional K (SchemeModuleGlobalSectionsOver base S.X₁) := by
    change FiniteDimensional K (SchemeModuleGlobalSectionsOver base (schemeModuleUnit X))
    infer_instance
  let P := schemeModuleGlobalSectionsMap base S.g
  let eK := schemeModuleGlobalSectionsKernelEquiv base S hS
  letI : FiniteDimensional K P.ker :=
    Module.Finite.of_surjective eK.toLinearMap eK.surjective
  letI : FiniteDimensional K (Submodule.comap P
      (⊤ : Submodule K (SchemeModuleGlobalSectionsOver base Q))) := inferInstance
  letI : FiniteDimensional K
      (⊤ : Submodule K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))) := by
    simpa only [Submodule.comap_top] using
      (inferInstance : FiniteDimensional K (Submodule.comap P
        (⊤ : Submodule K (SchemeModuleGlobalSectionsOver base Q))))
  letI : FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) :=
    Module.Finite.of_surjective (⊤ : Submodule K
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))).subtype
      (fun s => ⟨⟨s, trivial⟩, rfl⟩)
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
    ‹HasExt.{u} (hypersurface p hp).Modules›
  letI : Subsingleton (Ext.{u}
      (C := SheafOfModules.{u} (hypersurface p hp).ringCatSheaf)
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 1) :=
    cubicSurface_structure_ext_one_subsingleton_of_smooth K p hp hp0
  have hP : Function.Surjective P := by
    intro t
    obtain ⟨s, hs⟩ := e.projection_sections_surjective_of_ext_one_subsingleton
      (Q.unitHomEquiv t)
    refine ⟨e.E.unitHomEquiv.symm s, ?_⟩
    apply Q.unitHomEquiv.injective
    change Q.unitHomEquiv (e.E.unitHomEquiv.symm s ≫ e.projection) = Q.unitHomEquiv t
    rw [e.E.unitHomEquiv_comp_apply, e.E.unitHomEquiv.apply_symm_apply]
    exact hs
  have hrange : Module.finrank K P.range =
      Module.finrank K (SchemeModuleGlobalSectionsOver base Q) := by
    rw [LinearMap.range_eq_top.mpr hP, finrank_top]
  have hker : Module.finrank K P.ker = 1 :=
    eK.finrank_eq.symm.trans (cubicSurfaceUnitGlobalSections_finrank K p hp hp0)
  have hdim := P.finrank_range_add_finrank_ker
  rw [hrange, hker] at hdim
  change Module.finrank K (SchemeModuleGlobalSectionsOver base Q) + 1 =
    Module.finrank K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) at hdim
  have hQ := cubicClosedPointSerreQuotientSection_finrank_ge_eight K p hp hp0 i hi hL
  change 9 ≤ Module.finrank K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))
  change 8 ≤ Module.finrank K (SchemeModuleGlobalSectionsOver base Q) at hQ
  omega

end PfaffianDescent.ProjectiveNegativeTwist
