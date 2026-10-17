import PfaffianDescent.SerreActualCubicGroundFamilyOldSeedNewMarkedSeed

/-! The actual new marked cubic surface point, followed by the coefficient
map, is the actual original old incidence-marked point at the same parameter. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

private theorem serreActualMarkedSurface_comp_coefficient
    {U V W Z Y X : Scheme.{u}}
    {new : U ⟶ Y} {m : U ⟶ V} {a : V ⟶ W} {b : W ⟶ Z} {c : Z ⟶ Y}
    (f : Y ⟶ X) {old : U ⟶ X}
    (hnew : new = m ≫ a ≫ b ≫ c)
    (hold : m ≫ a ≫ b ≫ c ≫ f = old) : new ≫ f = old := by
  rw [hnew]
  simpa only [Category.assoc] using hold

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
variable {U Cfg : Scheme.{u}}
variable (b : U ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))

/-- Compose the checked new marked-surface identity with the checked old
common marked-section identity. The rich native proposition is inferred;
all marked lifts and coefficient compatibilities are constructed internally. -/
@[irreducible]
def serreActualCubicGroundFamily_oldSeed_toNewMarkedSeed_surface_toOriginal :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  fun (cfg : Cfg ⟶ Spec (.of K))
    (marked : Fin 3 → (Cfg ⟶ hypersurface p hp))
    (hm : ∀ i, marked i ≫ hypersurfaceToBase p hp = cfg)
    (s : U ⟶ serreThreePointSectionIncidence cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E))
    (hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) =
      b ≫ serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
    (i : Fin 3) =>
    serreActualMarkedSurface_comp_coefficient
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
      (serreActualCubicGroundFamily_oldSeed_toNewMarkedSeed_surface
        p hp e C h9 A B G H hHG b cfg marked hm s hsp i)
      (serreActualGroundFamily_oldSeed_commonMarkedSection_surface
        (hypersurfaceToBase p hp)
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
        (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
        (Spec.map (CommRingCat.ofHom (algebraMap K F)))
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
        (isPullback_projectiveCoefficientMap (algebraMap K F) (equationIdeal p hp)
          (equationIdeal (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
          (equationIdeal_map (algebraMap K F) p hp))
        (serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
        (serreActualGroundPlaneOriginalParameters_toBase (hypersurfaceToBase p hp) e.E h9 G H hHG)
        (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
        (serreActualCubicGroundFamilyToOriginal_surface p hp e h9 G H hHG)
        (serreActualCubicGroundFamilyToOriginal_parameters p hp e h9 G H hHG)
        (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)
        b cfg marked hm s hsp i)

end PfaffianDescent
