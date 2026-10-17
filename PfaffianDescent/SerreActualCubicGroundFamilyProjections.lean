import PfaffianDescent.SerreActualCubicGroundFamilyAmbient

/-! The two actual universal-family maps retain their actual surface and
kernel-plane parameter projections. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
variable {N : (hypersurface p hp).Modules}
variable (e : SerreExtensionData (hypersurface p hp) N)
variable (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
variable (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
variable (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
variable (hHG : H * G = 1)

@[reassoc]
theorem serreActualCubicGroundFamilyToOriginal_surface :
    serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG ≫
      pullback.fst (hypersurfaceToBase p hp)
        (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E) =
    pullback.fst
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F))) ≫
      cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp :=
  serreActualSurfaceParameterMap_surface _ _ _ _ _ _
    (Spec.map (CommRingCat.ofHom (algebraMap K F)))
    (serreActualCubicCoefficientMap_toBase p hp)
    (serreActualGroundPlaneOriginalParameters_toBase (hypersurfaceToBase p hp) e.E h9 G H hHG)

@[reassoc]
theorem serreActualCubicGroundFamilyToOriginal_parameters :
    serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG ≫
      pullback.snd (hypersurfaceToBase p hp)
        (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E) =
    pullback.snd
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F))) ≫
      serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG :=
  serreActualSurfaceParameterMap_parameters _ _ _ _ _ _
    (Spec.map (CommRingCat.ofHom (algebraMap K F)))
    (serreActualCubicCoefficientMap_toBase p hp)
    (serreActualGroundPlaneOriginalParameters_toBase (hypersurfaceToBase p hp) e.E h9 G H hHG)

@[reassoc]
theorem serreActualCubicGroundFamilyToNew_surface :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
    serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG ≫
      pullback.fst
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (schemeModuleGlobalSectionsProjectiveParametersToBase
          (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
          ((Scheme.Modules.pullback
            (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)) =
    pullback.fst
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F))) := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  calc
    _ = pullback.fst
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F))) ≫ 𝟙 _ :=
      serreActualSurfaceParameterMap_surface _ _ _ _ _ _ (𝟙 (Spec (.of F)))
        (by simp only [Category.id_comp, Category.comp_id] :
          (𝟙 _) ≫ hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)) =
            hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)) ≫ 𝟙 _)
        ((serreActualCubicGroundKernelParameters_toBase p hp e C h9 G H hHG).trans
          (Category.comp_id
            (toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F)))).symm)
    _ = _ := Category.comp_id _

@[reassoc]
theorem serreActualCubicGroundFamilyToNew_parameters :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
    serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG ≫
      pullback.snd
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (schemeModuleGlobalSectionsProjectiveParametersToBase
          (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
          ((Scheme.Modules.pullback
            (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)) =
    pullback.snd
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F))) ≫
      serreActualCubicGroundKernelParameters p hp e C h9 G H hHG := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  exact serreActualSurfaceParameterMap_parameters _ _ _ _ _ _ (𝟙 (Spec (.of F)))
    (by simp only [Category.id_comp, Category.comp_id] :
      (𝟙 _) ≫ hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)) =
        hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)) ≫ 𝟙 _)
    ((serreActualCubicGroundKernelParameters_toBase p hp e C h9 G H hHG).trans
      (Category.comp_id
        (toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F)))).symm)

end PfaffianDescent
