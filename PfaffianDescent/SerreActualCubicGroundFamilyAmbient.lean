import PfaffianDescent.SerreActualCubicGroundKernelParameters
import PfaffianDescent.SerreActualGroundPlaneOriginalParameters
import PfaffianDescent.SerreActualSurfaceParameterMap

/-! The actual common surface--kernel-plane family and its two maps to the
original and coefficient-cubic universal-section ambient schemes. -/
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

abbrev serreActualCubicGroundFamilyAmbient : Scheme.{u} :=
  pullback
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    (toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F)))

theorem serreActualCubicCoefficientMap_toBase :
    cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp ≫
      hypersurfaceToBase p hp =
    hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K F)) :=
  projectiveCoefficientMap_toBase (algebraMap K F) (equationIdeal p hp)
    (equationIdeal (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    (equationIdeal_map (algebraMap K F) p hp)

variable {N : (hypersurface p hp).Modules}
variable (e : SerreExtensionData (hypersurface p hp) N)
variable (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
variable (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)

def serreActualCubicGroundFamilyToOriginal
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) :
    serreActualCubicGroundFamilyAmbient (F := F) p hp ⟶
      pullback (hypersurfaceToBase p hp)
        (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E) := by
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let t := toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F))
  let param := serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG
  exact serreActualSurfaceParameterMap x t (hypersurfaceToBase p hp)
    (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
    param (Spec.map (CommRingCat.ofHom (algebraMap K F)))
    (serreActualCubicCoefficientMap_toBase p hp)
    (serreActualGroundPlaneOriginalParameters_toBase (hypersurfaceToBase p hp) e.E h9 G H hHG)

def serreActualCubicGroundFamilyToNew
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
    serreActualCubicGroundFamilyAmbient (F := F) p hp ⟶
      pullback
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (schemeModuleGlobalSectionsProjectiveParametersToBase
          (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
          ((Scheme.Modules.pullback
            (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)) := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let t := toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F))
  exact serreActualSurfaceParameterMap x t x
    (schemeModuleGlobalSectionsProjectiveParametersToBase x
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E))
    (𝟙 _) (serreActualCubicGroundKernelParameters p hp e C h9 G H hHG) (𝟙 _)
    (by simp only [Category.id_comp, Category.comp_id])
    ((serreActualCubicGroundKernelParameters_toBase p hp e C h9 G H hHG).trans
      (Category.comp_id t).symm)

end PfaffianDescent
