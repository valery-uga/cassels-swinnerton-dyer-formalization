import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionGroundParameterCoefficients
import PfaffianDescent.SerreActualCubicGroundFamilyProjections
import PfaffianDescent.SerreActualGroundFamilyBaseMap
import PfaffianDescent.SerreActualMatrixCoefficientBaseChange
import PfaffianDescent.SerreActualChartProjectionFactor
import PfaffianDescent.CubicClosedPointSerreGroundFamilyChartCoefficients

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Actual paired affine charts of the same cubic ground family give the literal
old/new local-coefficient square, with the actual surface base coefficient map. -/
theorem pointSplittingCubicSerreGroundChosenSection_cubicGroundParameter_coefficients
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {I J : Type u} (A : SchemeModuleFiniteFreeAffineCover e.E I)
    (B : SchemeModuleFiniteFreeAffineCover
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) J)
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) {T : Scheme.{u}}
    (t : T ⟶ serreActualCubicGroundFamilyAmbient (F := F) p hp) :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
    let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
    let M := (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
    ∀ (ij : (A.projectiveSectionOpenCover (hypersurfaceToBase p hp) e.E).I₀)
      (kl : (B.projectiveSectionOpenCover x M).I₀)
      (f : T ⟶ (A.projectiveSectionOpenCover (hypersurfaceToBase p hp) e.E).X ij)
      (g : T ⟶ (B.projectiveSectionOpenCover x M).X kl),
      f ≫ (A.projectiveSectionOpenCover (hypersurfaceToBase p hp) e.E).f ij =
        t ≫ serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG →
      g ≫ (B.projectiveSectionOpenCover x M).f kl =
        t ≫ serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG →
      let β := affineFunctionHom (t ≫ pullback.fst x
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F))) ≫ x)
      ∃ u : Γ(T, ⊤), IsUnit u ∧ ∀ i,
        g.appTop (B.projectiveSectionLocalCoefficient x M kl i) =
          u * ((((finBasis F (SchemeModuleGlobalSectionsOver x M)).toMatrix
            (serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9)).map β).mulVec
            (fun j => f.appTop (A.projectiveSectionLocalCoefficient
              (hypersurfaceToBase p hp) e.E ij ((finCongr h9).symm j)))) i := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  dsimp only
  intro ij kl f g hf hg
  have hnew : finrank F (SchemeModuleGlobalSectionsOver x M) = 9 :=
    (serreIncidenceCubicCoefficientGlobalSections_finrank (F := F) p hp e C).trans h9
  exact pointSplittingSerreGroundFamily_chart_coefficients
    (hypersurfaceToBase p hp) e.E x M h9 hnew A B
    (serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9)
    G H hHG t (pullback.snd x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F))))
    (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
    (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
    (serreActualCubicGroundFamilyToOriginal_parameters p hp e h9 G H hHG)
    (serreActualCubicGroundFamilyToNew_parameters p hp e C h9 G H hHG)
    (affineFunctionHom (t ≫ pullback.fst x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F))) ≫ x))
    (serreActualGroundFamily_kernel_baseMap x G H hHG t) ij kl f g hf hg

end PfaffianDescent
