import PfaffianDescent.SerreActualCubicLocalUniversalModuleIso
import PfaffianDescent.SerreActualLocalUniversalSectionTransport

/-! The literal new local universal section compares with the original
canonical nine-section family under its actual composition isomorphism.
The remaining hypothesis is the explicit equality of regular coefficient
functions, not an assumed section or zero-scheme comparison. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
variable {N : (hypersurface p hp).Modules}
variable (e : SerreExtensionData (hypersurface p hp) N)
variable (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
variable [FiniteDimensional F (SchemeModuleGlobalSectionsOver
  (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
  ((Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E))]
variable (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
variable {ι : Type u}
variable (D : SchemeModuleFiniteFreeAffineCover
  ((Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) ι)
variable (kl : (D.projectiveSectionOpenCover
  (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
  ((Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)).I₀)

theorem serreActualCubicLocalUniversalSection_compare_factored
    {T : Scheme.{u}}
    (g : T ⟶ (D.projectiveSectionOpenCover
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)).X kl)
    (r : T ⟶ hypersurface (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    (q : T ⟶ hypersurface p hp)
    (hg : g ≫ D.projectiveSectionOpenCoverToSurface
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) kl = r)
    (hc : r ≫ cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp = q)
    (coeff : Fin 9 → Γ(T, ⊤)) (a : Γ(T, ⊤))
    (hcoeff :
      let baseF := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
      let MF := (Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
      let b := serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9
      let c := Module.finBasis F (SchemeModuleGlobalSectionsOver baseF MF)
      ∀ i, g.appTop (D.projectiveSectionLocalCoefficient baseF MF kl i) =
        a * (((c.toMatrix b).map (affineFunctionHom (r ≫ baseF))).mulVec coeff) i) :
    SheafOfModules.sectionsMap
        (serreActualCubicLocalUniversalToOriginalIso p hp e D kl g r q hg hc).hom
        (pullbackSection g (D.projectiveSectionLocalModule
          (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
          ((Scheme.Modules.pullback
            (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) kl)
          (isIso_pullbackUnitComparison g)
          (D.projectiveSectionLocalUniversalSection
            (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
            ((Scheme.Modules.pullback
              (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) kl)) =
      scaleSection (unitEndomorphismOfRegularFunction a)
        (parameterizedSchemeModuleSection (hypersurfaceToBase p hp) e.E q coeff
          (finBasisOfFinrankEq K
            (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9)) := by
  let baseF := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let MF : (hypersurface (p.map (algebraMap K F)) (hp.map (algebraMap K F))).Modules :=
    (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  let b := serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9
  let c := Module.finBasis F (SchemeModuleGlobalSectionsOver baseF MF)
  let d := (Scheme.Modules.pullbackComp r
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).app e.E ≪≫
    (Scheme.Modules.pullbackCongr hc).app e.E
  exact serreActualLocalUniversalSection_afterModuleIso baseF MF D kl g r hg d
    (fun i => a * (((c.toMatrix b).map (affineFunctionHom (r ≫ baseF))).mulVec coeff) i)
    (scaleSection (unitEndomorphismOfRegularFunction a)
      (parameterizedSchemeModuleSection (hypersurfaceToBase p hp) e.E q coeff
        (finBasisOfFinrankEq K
          (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9)))
    hcoeff (serreActualCubicNormalizedSectionFamily p hp e C h9 c r q hc coeff a)

end PfaffianDescent
