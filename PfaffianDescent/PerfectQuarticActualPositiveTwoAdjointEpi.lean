import PfaffianDescent.ActualCubicPositiveTwoNativeChartTildeIso
import PfaffianDescent.ActualAffineChartGlobalPointAdjointSurjective
import PfaffianDescent.ActualFieldPointLineAdjointCongruence
import PfaffianDescent.ActualFieldPointPushforwardGlobalEpi
import PfaffianDescent.ActualOriginalQuarticCotangentChartChoice
import PfaffianDescent.ActualPositiveTwoGlobalLineEquiv

/- SOURCE ONLY / UNVERIFIED. Genuine GLOBAL Omega(2) quotient at SAME
original closed quartic P. All chart/twist/point and adjunction comparisons,
chart surjectivity and complement vanishing are internally derived. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- EVERY surjective genuine Omega(2) fiber line gives the actual global
sheaf adjoint Epi. No desired sheaf square/Epi/trivialization certificate,
smoothness, fiber dimension or H0>=3 premise is added. -/
theorem perfectField_originalQuarticPositiveTwoLineAdjoint_epi
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualCubicPositiveTwoPointDifferentialFiber p hp
      ((hypersurface p hp).fromSpecResidueField P.1) →ₗ[(hypersurface p hp).residueField P.1]
        (hypersurface p hp).residueField P.1)
    (hell : Function.Surjective ell) :
    Epi (actualFieldPointLineAdjoint ((hypersurface p hp).fromSpecResidueField P.1)
      (actualCubicPositiveTwoDifferentials p hp) ell) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let R := ChartRing I C.index
  let L := (hypersurface p hp).residueField P.1
  let i := chartι I C.index
  let qU := Spec.map (CommRingCat.ofHom C.residue)
  let qP := (hypersurface p hp).fromSpecResidueField P.1
  let M := actualCubicPositiveTwoDifferentials p hp
  letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
  let A := ModuleCat.of R (KaehlerDifferential K R)
  let e : (Scheme.Modules.pullback i).obj M ≅ (tilde.functor (.of R)).obj A :=
    actualCubicPositiveTwoNativeChartTildeIso p hp C.index
  let eQ := (Scheme.Modules.pullbackCongr C.factorization).app M
  let ellC := ell.comp ((moduleSpecΓFunctor (R := .of L)).map eQ.hom).hom
  have hellC : Function.Surjective ellC :=
    hell.comp (ConcreteCategory.bijective_of_isIso _).2
  let V := i ''ᵁ ⊤
  have hChartComp : Function.Surjective ((actualFieldPointLineAdjoint (qU ≫ i) M ellC).app V) :=
    actualAffineChartGlobalPointLineAdjoint_app_surjective i C.residue C.residue_surjective
      M A e ellC hellC
  have hPointSquare : actualFieldPointLineAdjoint (qU ≫ i) M ellC ≫
      (Scheme.Modules.pushforwardCongr C.factorization).hom.app
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) =
      actualFieldPointLineAdjoint qP M ell :=
    actualFieldPointLineAdjoint_morphism_congr C.factorization M ell
  have hChart : Function.Surjective ((actualFieldPointLineAdjoint qP M ell).app V) := by
    rw [← hPointSquare, Scheme.Modules.Hom.comp_app]
    exact (ConcreteCategory.bijective_of_isIso _).2.comp hChartComp
  have hPV : P.1 ∈ V := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    change P.1 ∈ Set.range i
    exact actualOriginalQuarticCotangentChartChoice_contains_original_point p hp P hP
  exact actualFieldPointPushforward_map_epi_of_chart qP P.1
    (fun z => (hypersurface p hp).fromSpecResidueField_apply P.1 z)
      P.2 M (actualFieldPointLineAdjoint qP M ell) V hPV hChart

end PfaffianDescent
