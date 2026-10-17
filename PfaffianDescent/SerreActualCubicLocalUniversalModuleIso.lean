import PfaffianDescent.SerreActualLocalUniversalSectionPullback
import PfaffianDescent.SerreActualCubicNormalizedSectionFamily

/-! The actual composition isomorphism from a coefficient-cubic universal
chart module to the original bundle on the common source. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module
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
variable [FiniteDimensional F (SchemeModuleGlobalSectionsOver
  (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
  ((Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E))]
variable {ι : Type u}
variable (D : SchemeModuleFiniteFreeAffineCover
  ((Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) ι)
variable (kl : (D.projectiveSectionOpenCover
  (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
  ((Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)).I₀)

def serreActualCubicLocalUniversalToOriginalIso
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
    (hc : r ≫ cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp = q) :
    (Scheme.Modules.pullback g).obj (D.projectiveSectionLocalModule
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) kl) ≅
      (Scheme.Modules.pullback q).obj e.E :=
  ((Scheme.Modules.pullbackComp g (D.projectiveSectionOpenCoverToSurface
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) kl)).app
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) ≪≫
    (Scheme.Modules.pullbackCongr hg).app
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)) ≪≫
    ((Scheme.Modules.pullbackComp r
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).app e.E ≪≫
      (Scheme.Modules.pullbackCongr hc).app e.E)

end PfaffianDescent
