import PfaffianDescent.SerreActualParameterizedPulledSections
import PfaffianDescent.SerreActualParameterizedSectionNormalization
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionBasis

/-! Native comparison of the actual coefficient-cubic linear family with
the original family. The transported section identities are proved by the
actual coefficient frame, not supplied as a comparison certificate. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist BundleSectionZeroLocus
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreActualCubicNormalizedSectionFamily
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {κ : Type v} [Fintype κ]
    (c : Basis κ F (SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)))
    {T : Scheme.{u}}
    (r : T ⟶ hypersurface (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    (q : T ⟶ hypersurface p hp)
    (h : r ≫ cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp = q)
    (coeff : Fin 9 → Γ(T, ⊤)) (a : Γ(T, ⊤)) :
    let baseF := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
    let f := cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp
    let M := (Scheme.Modules.pullback f).obj e.E
    let b := serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9
    SheafOfModules.sectionsMap
        (((Scheme.Modules.pullbackComp r f).app e.E ≪≫
          (Scheme.Modules.pullbackCongr h).app e.E).hom)
        (parameterizedSchemeModuleSection baseF M r
          (fun i => a * (((c.toMatrix b).map (affineFunctionHom (r ≫ baseF))).mulVec coeff) i) c) =
      scaleSection (unitEndomorphismOfRegularFunction a)
        (parameterizedSchemeModuleSection (hypersurfaceToBase p hp) e.E q coeff
          (finBasisOfFinrankEq K
            (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9)) := by
  let baseF := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let f := cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp
  let M : (hypersurface (p.map (algebraMap K F)) (hp.map (algebraMap K F))).Modules :=
    (Scheme.Modules.pullback f).obj e.E
  let b := serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9
  let bK := finBasisOfFinrankEq K
    (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9
  change SheafOfModules.sectionsMap
      (((Scheme.Modules.pullbackComp r f).app e.E ≪≫
        (Scheme.Modules.pullbackCongr h).app e.E).hom)
      (parameterizedSchemeModuleSection baseF M r
        (fun i => a * (((c.toMatrix b).map (affineFunctionHom (r ≫ baseF))).mulVec coeff) i) c) =
    scaleSection (unitEndomorphismOfRegularFunction a)
      (parameterizedSchemeModuleSection (hypersurfaceToBase p hp) e.E q coeff bK)
  rw [serreActualParameterizedBasis_normalized, sectionsMap_scaleSection]
  apply congrArg (scaleSection (unitEndomorphismOfRegularFunction a))
  have hb : (b : Fin 9 → SchemeModuleGlobalSectionsOver baseF M) =
      (fun j => serreActualPulledGlobalSection (hypersurfaceToBase p hp) baseF f e.E (bK j)) :=
    funext (fun j => pointSplittingCubicSerreGroundChosenSection_coefficientBasis_apply p hp e C h9 j)
  rw [hb]
  exact serreActualParameterizedPulledSections_comp
    (hypersurfaceToBase p hp) baseF f e.E r q h coeff bK

end PfaffianDescent
