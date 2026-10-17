import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionGroundParameterCoefficients
import PfaffianDescent.SerreActualMatrixCoefficientBaseChange
import PfaffianDescent.SerreActualChartProjectionFactor

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Actual paired ambient-chart factorizations imply the coefficient formula.
All projection and scalar-map identities are checked at the ambient level;
the section, coordinate and zero-family comparisons are conclusions. -/
theorem pointSplittingSerreGroundFamily_chart_coefficients
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    {X Y S T : Scheme.{u}}
    (baseK : X ⟶ Spec (.of K)) (MK : X.Modules)
    (baseF : Y ⟶ Spec (.of F)) (MF : Y.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver baseK MK)]
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver baseF MF)]
    (hK : finrank K (SchemeModuleGlobalSectionsOver baseK MK) = 9)
    (hF : finrank F (SchemeModuleGlobalSectionsOver baseF MF) = 9)
    {I J : Type u} (A : SchemeModuleFiniteFreeAffineCover MK I)
    (B : SchemeModuleFiniteFreeAffineCover MF J)
    (b : Basis (Fin 9) F (SchemeModuleGlobalSectionsOver baseF MF))
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) (t : T ⟶ S)
    (s : S ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    (o : S ⟶ pullback baseK (schemeModuleGlobalSectionsProjectiveParametersToBase baseK MK))
    (n : S ⟶ pullback baseF (schemeModuleGlobalSectionsProjectiveParametersToBase baseF MF))
    (ho : o ≫ pullback.snd baseK
        (schemeModuleGlobalSectionsProjectiveParametersToBase baseK MK) =
      s ≫ serreActualGroundPlaneOriginalParameters baseK MK hK G H hHG)
    (hn : n ≫ pullback.snd baseF
        (schemeModuleGlobalSectionsProjectiveParametersToBase baseF MF) =
      s ≫ serreActualGroundKernelCanonicalParameters baseF MF hF b G H hHG)
    (β : F →+* Γ(T, ⊤))
    (hβ : affineFunctionHom (t ≫ s ≫ serreKernelFrameProjectiveEmbedding G H hHG ≫
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F))) = β)
    (ij : (A.projectiveSectionOpenCover baseK MK).I₀)
    (kl : (B.projectiveSectionOpenCover baseF MF).I₀)
    (f : T ⟶ (A.projectiveSectionOpenCover baseK MK).X ij)
    (g : T ⟶ (B.projectiveSectionOpenCover baseF MF).X kl)
    (hf : f ≫ (A.projectiveSectionOpenCover baseK MK).f ij = t ≫ o)
    (hg : g ≫ (B.projectiveSectionOpenCover baseF MF).f kl = t ≫ n) :
    ∃ a : Γ(T, ⊤), IsUnit a ∧ ∀ i,
      g.appTop (B.projectiveSectionLocalCoefficient baseF MF kl i) =
        a * ((((finBasis F (SchemeModuleGlobalSectionsOver baseF MF)).toMatrix b).map β).mulVec
          (fun j => f.appTop (A.projectiveSectionLocalCoefficient baseK MK ij
            ((finCongr hK).symm j)))) i := by
  have hfp := serreActualChartProjectionFactor f
    ((A.projectiveSectionOpenCover baseK MK).f ij) t o _ s _ hf ho
  have hgp := serreActualChartProjectionFactor g
    ((B.projectiveSectionOpenCover baseF MF).f kl) t n _ s _ hg hn
  have hc := pointSplittingCubicSerreGroundChosenSection_groundParameter_coefficients
    baseK MK baseF MF hK hF A B ij kl b G H hHG (t ≫ s) f g hfp hgp
  exact serreActualMatrixCoefficientComparison_changeBase
    ((finBasis F (SchemeModuleGlobalSectionsOver baseF MF)).toMatrix b)
    (fun j => f.appTop (A.projectiveSectionLocalCoefficient baseK MK ij
      ((finCongr hK).symm j)))
    (fun i => g.appTop (B.projectiveSectionLocalCoefficient baseF MF kl i))
    (affineFunctionHom ((t ≫ s) ≫ serreKernelFrameProjectiveEmbedding G H hHG ≫
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F)))) β
    (by simpa only [Category.assoc] using hβ) hc

end PfaffianDescent
