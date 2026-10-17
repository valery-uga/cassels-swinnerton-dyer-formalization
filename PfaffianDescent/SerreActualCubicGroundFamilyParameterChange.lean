import PfaffianDescent.SerreActualCubicGroundFamilyGlobalZeroComparison
import PfaffianDescent.SerreActualClosedPullbackZeroParameterChange

/-! Actual restriction of the old/new cubic zero-family comparison to a
parameter open or point.  The native global ideal equality is supplied
internally, so no extra compatibility of zero families is required. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
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
variable {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (A : SchemeModuleFiniteFreeAffineCover e.E I)
variable (B : SchemeModuleFiniteFreeAffineCover
  ((Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) J)
variable (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
variable (hHG : H * G = 1)
variable {U : Scheme.{u}}
variable (b : U ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))

def serreActualCubicGroundFamily_parameterChangeIso :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    ((Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)
    let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
    let M := (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
    let a := pullback.snd x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    pullback b
        (pullback.fst (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
          (B.projectiveSectionLocalZeroGluedToAmbient x M) ≫ a) ≅
      pullback b
        (pullback.fst (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
          (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) ≫ a) := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    ((Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)
  exact serreActualClosedPullbackZero_parameterChangeIso _ _ _ _
    (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG) _ b

/-- Finiteness of the actual old family on this chosen parameter open or point
implies finiteness of the literal coefficient-cubic family on the same base. -/
theorem serreActualCubicGroundFamily_parameterChange_isFinite :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    ((Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)
    let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
    let M := (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
    let a := pullback.snd x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    IsFinite (pullback.fst b
        (pullback.fst (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
          (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) ≫ a)) →
      IsFinite (pullback.fst b
        (pullback.fst (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
          (B.projectiveSectionLocalZeroGluedToAmbient x M) ≫ a)) := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    ((Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)
  dsimp only
  intro hfinite
  letI := hfinite
  exact serreActualClosedPullbackZero_parameterChange_isFinite _ _ _ _
    (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG) _ b

/-- Flatness on the same chosen parameter base transfers through the actual
zero-family isomorphism; no assertion is made about etaleness of the residual. -/
theorem serreActualCubicGroundFamily_parameterChange_flat :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    ((Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)
    let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
    let M := (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
    let a := pullback.snd x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    Flat (pullback.fst b
        (pullback.fst (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
          (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) ≫ a)) →
      Flat (pullback.fst b
        (pullback.fst (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
          (B.projectiveSectionLocalZeroGluedToAmbient x M) ≫ a)) := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    ((Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)
  dsimp only
  intro hflat
  letI := hflat
  exact serreActualClosedPullbackZero_parameterChange_flat _ _ _ _
    (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG) _ b

/-- The actual fibre comparison preserves its map to the common cubic family,
so subsequent marked-point comparisons concern the same geometric points. -/
@[irreducible]
def serreActualCubicGroundFamily_parameterChange_hom_ambient :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  serreActualClosedPullbackZero_parameterChangeIso_hom_ambient
    (B.projectiveSectionLocalZeroGluedToAmbient x M)
    (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)
    (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
    (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
    (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG)
    (pullback.snd x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))) b

end PfaffianDescent
