import PfaffianDescent.SerreActualGroundKernelChartComparison
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionParameterRankCoefficients
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionNaturalRankCoefficients

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Genuine old and new product-chart projection factorizations through the same
ground plane give the actual regular local-coefficient comparison. -/
theorem pointSplittingCubicSerreGroundChosenSection_groundParameter_coefficients
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    {X Y T : Scheme.{u}}
    (baseK : X ⟶ Spec (.of K)) (MK : X.Modules)
    (baseF : Y ⟶ Spec (.of F)) (MF : Y.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver baseK MK)]
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver baseF MF)]
    (hK : finrank K (SchemeModuleGlobalSectionsOver baseK MK) = 9)
    (hF : finrank F (SchemeModuleGlobalSectionsOver baseF MF) = 9)
    {I J : Type u} (A : SchemeModuleFiniteFreeAffineCover MK I)
    (B : SchemeModuleFiniteFreeAffineCover MF J)
    (ij : (A.projectiveSectionOpenCover baseK MK).I₀)
    (kl : (B.projectiveSectionOpenCover baseF MF).I₀)
    (b : Basis (Fin 9) F (SchemeModuleGlobalSectionsOver baseF MF))
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1)
    (s : T ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    (f : T ⟶ (A.projectiveSectionOpenCover baseK MK).X ij)
    (g : T ⟶ (B.projectiveSectionOpenCover baseF MF).X kl)
    (hf : f ≫ (A.projectiveSectionOpenCover baseK MK).f ij ≫
      pullback.snd baseK (schemeModuleGlobalSectionsProjectiveParametersToBase baseK MK) =
      s ≫ serreActualGroundPlaneOriginalParameters baseK MK hK G H hHG)
    (hg : g ≫ (B.projectiveSectionOpenCover baseF MF).f kl ≫
      pullback.snd baseF (schemeModuleGlobalSectionsProjectiveParametersToBase baseF MF) =
      s ≫ serreActualGroundKernelCanonicalParameters baseF MF hF b G H hHG) :
    let β := affineFunctionHom (s ≫ serreKernelFrameProjectiveEmbedding G H hHG ≫
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F)))
    ∃ u : Γ(T, ⊤), IsUnit u ∧ ∀ i,
      g.appTop (B.projectiveSectionLocalCoefficient baseF MF kl i) =
        u * ((((finBasis F (SchemeModuleGlobalSectionsOver baseF MF)).toMatrix b).map β).mulVec
          (fun j => f.appTop (A.projectiveSectionLocalCoefficient baseK MK ij
            ((finCongr hK).symm j)))) i := by
  let a := pointSplittingCubicSerreGroundChosenSection_parameterRankChartMap baseK MK A ij hK f
  let d := pointSplittingCubicSerreGroundChosenSection_parameterRankChartMap baseF MF B kl hF g
  have ha : a ≫ chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
      ((finCongr hK) ij.2) =
      s ≫ serreActualGroundPlaneOriginalParameters baseK MK hK G H hHG ≫
        (serreIncidenceNineParameterIso baseK MK hK).hom := by
    have hh := congrArg (fun q => q ≫ (serreIncidenceNineParameterIso baseK MK hK).hom) hf
    exact (pointSplittingCubicSerreGroundChosenSection_parameterRankChartMap_chartι
      baseK MK A ij hK f).trans (by
        simpa only [serreIncidenceNineParameterIso, serreIncidenceParameterRankIso,
          Category.assoc] using hh)
  have hd : d ≫ chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F))
      ((finCongr hF) kl.2) =
      s ≫ serreActualGroundKernelCanonicalParameters baseF MF hF b G H hHG ≫
        (serreIncidenceNineParameterIso baseF MF hF).hom := by
    have hh := congrArg (fun q => q ≫ (serreIncidenceNineParameterIso baseF MF hF).hom) hg
    exact (pointSplittingCubicSerreGroundChosenSection_parameterRankChartMap_chartι
      baseF MF B kl hF g).trans (by
        simpa only [serreIncidenceNineParameterIso, serreIncidenceParameterRankIso,
          Category.assoc] using hh)
  obtain ⟨u, hu, hc⟩ := serreActualGroundKernelChartComparison baseK MK baseF MF
    hK hF b G H hHG s ((finCongr hK) ij.2) ((finCongr hF) kl.2) a d ha hd
  have hold : (fun j => affineFunctionHom a
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
        ((finCongr hK) ij.2) j)) =
      (fun j => f.appTop (A.projectiveSectionLocalCoefficient baseK MK ij
        ((finCongr hK).symm j))) := by
    funext j
    exact (pointSplittingCubicSerreGroundChosenSection_parameterRankChart_coefficient
      baseK MK A ij hK f j).symm
  rw [hold] at hc
  refine ⟨u, hu, ?_⟩
  apply pointSplittingCubicSerreGroundChosenSection_naturalRank_coefficients hF b
  intro j
  exact (pointSplittingCubicSerreGroundChosenSection_parameterRankChart_coefficient
    baseF MF B kl hF g j).trans (hc j)

end PfaffianDescent
