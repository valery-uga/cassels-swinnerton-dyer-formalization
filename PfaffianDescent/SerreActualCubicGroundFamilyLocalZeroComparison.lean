import PfaffianDescent.CubicClosedPointSerreGroundFamilyChartCoefficientsInferred
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionLocalUniversalPullbackReindex
import PfaffianDescent.SerreActualCubicLocalUniversalSectionFactored
import PfaffianDescent.SerreActualUniversalZeroCommonModule

/-! The actual old and new cubic universal zero ideals coincide on paired
affine charts of the same ground-kernel family. The regular coefficient and
section comparisons are derived internally from that family. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def serreActualCubicGroundFamily_local_zero_comparison
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : SchemeModuleFiniteFreeAffineCover e.E I)
    (B : SchemeModuleFiniteFreeAffineCover
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) J)
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ serreActualCubicGroundFamilyAmbient (F := F) p hp) :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M : (hypersurface (p.map (algebraMap K F)) (hp.map (algebraMap K F))).Modules :=
    (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  fun (ij : (A.projectiveSectionOpenCover (hypersurfaceToBase p hp) e.E).I₀)
      (kl : (B.projectiveSectionOpenCover x M).I₀)
      (f : T ⟶ (A.projectiveSectionOpenCover (hypersurfaceToBase p hp) e.E).X ij)
      (g : T ⟶ (B.projectiveSectionOpenCover x M).X kl)
      (hf : f ≫ (A.projectiveSectionOpenCover (hypersurfaceToBase p hp) e.E).f ij =
        t ≫ serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (hg : g ≫ (B.projectiveSectionOpenCover x M).f kl =
        t ≫ serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG) => by
    let r := t ≫ pullback.fst x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    let q := r ≫ cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp
    have hfSurface : f ≫ A.projectiveSectionOpenCoverToSurface
        (hypersurfaceToBase p hp) e.E ij = q := by
      calc
        _ = f ≫ (A.projectiveSectionOpenCover (hypersurfaceToBase p hp) e.E).f ij ≫
            pullback.fst (hypersurfaceToBase p hp)
              (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E) :=
          congrArg (fun m => f ≫ m)
            (A.projectiveSectionOpenCover_f_comp_ambientFst (hypersurfaceToBase p hp) e.E ij).symm
        _ = (t ≫ serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG) ≫ _ := by
          rw [← Category.assoc, hf]
        _ = q := by
          rw [Category.assoc, serreActualCubicGroundFamilyToOriginal_surface]
          simp only [q, r, x, Category.assoc]
    have hgSurface : g ≫ B.projectiveSectionOpenCoverToSurface x M kl = r := by
      calc
        _ = g ≫ (B.projectiveSectionOpenCover x M).f kl ≫
            pullback.fst x (schemeModuleGlobalSectionsProjectiveParametersToBase x M) :=
          congrArg (fun m => g ≫ m)
            (B.projectiveSectionOpenCover_f_comp_ambientFst x M kl).symm
        _ = (t ≫ serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG) ≫ _ := by
          rw [← Category.assoc, hg]
        _ = r := by
          rw [Category.assoc, serreActualCubicGroundFamilyToNew_surface]
    let hc :=
      pointSplittingCubicSerreGroundChosenSection_cubicGroundParameter_coefficients_inferred
        p hp e C h9 A B G H hHG t ij kl f g hf hg
    let u := Classical.choose hc
    have hu := (Classical.choose_spec hc).1
    have hcoeff := (Classical.choose_spec hc).2
    let coeff : Fin 9 → Γ(T, ⊤) := fun j =>
      f.appTop (A.projectiveSectionLocalCoefficient (hypersurfaceToBase p hp) e.E ij
        ((finCongr h9).symm j))
    let eOld := (Scheme.Modules.pullbackComp f
        (A.projectiveSectionOpenCoverToSurface (hypersurfaceToBase p hp) e.E ij)).app e.E ≪≫
      (Scheme.Modules.pullbackCongr hfSurface).app e.E
    let eNew := serreActualCubicLocalUniversalToOriginalIso p hp e B kl g r q hgSurface rfl
    have hold := pointSplittingCubicSerreGroundChosenSection_localUniversalSection_pullback_reindex
      (hypersurfaceToBase p hp) e.E A ij h9 f q hfSurface
    have hnew := serreActualCubicLocalUniversalSection_compare_factored
      p hp e C h9 B kl g r q hgSurface rfl coeff u hcoeff
    have hcommon := hnew.trans
      (congrArg (scaleSection (unitEndomorphismOfRegularFunction u)) hold.symm)
    exact serreActualUniversalZero_commonModule_comap_chart_eq
      x M (hypersurfaceToBase p hp) e.E B A kl ij g f eNew eOld u hu hcommon

end PfaffianDescent
