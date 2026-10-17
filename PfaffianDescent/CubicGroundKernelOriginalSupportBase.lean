import PfaffianDescent.CubicGroundKernelJetPointBase

/-! The original chart support has its literal coefficient-field structure. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicGroundKernelOriginalSupport_toBase
    {F L : Type u} [Field F] [Field L] [Algebra F L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap F L) :
    cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g ≫
      toBase I = Spec.map (CommRingCat.ofHom (algebraMap F L)) := by
  let η := AllCharacteristics.GradedChart.baseMap (grading I)
    (z := (ell : CoordinateRing I))
  have hc : cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell ≫ toBase I =
      Spec.map (CommRingCat.ofHom η) :=
    homogeneousChart_toBase I (ell : CoordinateRing I) ell.2 Nat.zero_lt_one
  calc
    _ = Spec.map (CommRingCat.ofHom g) ≫
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell ≫ toBase I) := by
      simp only [cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion,
        cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom η) :=
      congrArg (fun q => Spec.map (CommRingCat.ofHom g) ≫ q) hc
    _ = Spec.map (CommRingCat.ofHom (g.comp η)) := (Spec.map_comp _ _).symm
    _ = _ := congrArg (fun q => Spec.map (CommRingCat.ofHom q)) hbase

end PfaffianDescent
