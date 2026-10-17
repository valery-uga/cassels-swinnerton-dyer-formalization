import PfaffianDescent.SerreActualCoefficientChartLift
import PfaffianDescent.SerreActualGroundKernelNineParameters
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionProjectiveBasisChartCoordinates

/-! Actual old and new ground-kernel parameter maps determine the regular
coefficient comparison on their common charts. The change-of-basis square,
its normalization unit, and the coefficient-chart lift are proved internally. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreActualGroundKernelChartComparison
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    {X Y T : Scheme.{u}}
    (baseK : X ⟶ Spec (.of K)) (MK : X.Modules)
    (baseF : Y ⟶ Spec (.of F)) (MF : Y.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver baseK MK)]
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver baseF MF)]
    (hK : finrank K (SchemeModuleGlobalSectionsOver baseK MK) = 9)
    (hF : finrank F (SchemeModuleGlobalSectionsOver baseF MF) = 9)
    (b : Basis (Fin 9) F (SchemeModuleGlobalSectionsOver baseF MF))
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1)
    (s : T ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    (j l : Fin 9)
    (a : T ⟶ Spec (.of (ChartRing (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 9) K)) j)))
    (d : T ⟶ Spec (.of (ChartRing (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 9) F)) l)))
    (ha : a ≫ chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) j =
      s ≫ serreActualGroundPlaneOriginalParameters baseK MK hK G H hHG ≫
        (serreIncidenceNineParameterIso baseK MK hK).hom)
    (hd : d ≫ chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F)) l =
      s ≫ serreActualGroundKernelCanonicalParameters baseF MF hF b G H hHG ≫
        (serreIncidenceNineParameterIso baseF MF hF).hom) :
    let IF : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F) := ⊥
    let IK : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K) := ⊥
    let c := finBasisOfFinrankEq F (SchemeModuleGlobalSectionsOver baseF MF) hF
    let β := affineFunctionHom (s ≫ serreKernelFrameProjectiveEmbedding G H hHG ≫ toBase IF)
    ∃ u : Γ(T, ⊤), IsUnit u ∧ ∀ i,
      affineFunctionHom d (chartCoordinate IF l i) =
        u * (((c.toMatrix b).map β).mulVec
          (fun q => affineFunctionHom a (chartCoordinate IK j q))) i := by
  let IF : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F) := ⊥
  let IK : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K) := ⊥
  let c := finBasisOfFinrankEq F (SchemeModuleGlobalSectionsOver baseF MF) hF
  let k := s ≫ serreKernelFrameProjectiveEmbedding G H hHG
  have hIJ : IK.toIdeal.map (MvPolynomial.map (algebraMap K F)) = IF.toIdeal := by
    dsimp only [IK, IF]
    simp
  have ha' : a ≫ chartι IK j =
      k ≫ projectiveCoefficientMap (algebraMap K F) IK IF hIJ := by
    simpa only [serreActualGroundPlaneOriginalParameters_nine,
      projectiveFrameCoordinateCoefficientMap, Category.assoc, k] using ha
  let aF := serreActualCoefficientChartLift (algebraMap K F) IK IF hIJ j a k ha'
  have hdiagram : aF ≫ chartι IF j ≫ (projectiveBasisCoordinateIso b c).hom =
      d ≫ chartι IF l := by
    calc
      _ = k ≫ (projectiveBasisCoordinateIso b c).hom := by
        rw [← Category.assoc,
          serreActualCoefficientChartLift_toProjective]
      _ = _ := by
        simpa only [serreActualGroundKernelCanonicalParameters_nine,
          Category.assoc, k, c] using hd.symm
  obtain ⟨u, hu, hcoord⟩ :=
    pointSplittingCubicSerreGroundChosenSection_basisCoordinateChart_regular_coordinates
      b c j l aF d hdiagram
  have hbase : (affineFunctionHom aF).comp (chartBaseMap IF j) =
      affineFunctionHom (k ≫ toBase IF) :=
    serreActualCoefficientChartLift_baseMap (algebraMap K F) IK IF hIJ j a k ha'
  have hcoords : (fun q => affineFunctionHom aF (chartCoordinate IF j q)) =
      (fun q => affineFunctionHom a (chartCoordinate IK j q)) := by
    funext q
    exact (serreActualCoefficientChartLift_coordinate
      (algebraMap K F) IK IF hIJ j a k ha' q).symm
  dsimp only [IF, IK] at hbase hcoords
  rw [hbase, hcoords] at hcoord
  refine ⟨u, hu, ?_⟩
  intro i
  simpa only [k, c, Category.assoc] using hcoord i

end PfaffianDescent
