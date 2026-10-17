import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveGlobalChartRestriction
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointChartUnitCoordinate

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

private theorem regularSectionValue {X : Scheme.{u}} (a : Γ(X, ⊤)) :
    ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
      (unitEndomorphismOfRegularFunction a)).val (op ⊤) = a :=
  (SheafOfModules.unitHomEquiv_apply_coe _ _ (op ⊤)).trans
    (unitEndomorphismValue_ofRegularFunction a)

/-- The actual global O(3) restriction is the ACTUAL point pullback, under
its internally constructed native positive-three point-unit isomorphism. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveGlobalPointRestriction_coordinate
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap K L)
    (e : grading I 3 ≃ₗ[K] SchemeModuleGlobalSectionsOver (toBase I)
      (positiveSheafOfModules (grading I) 3))
    (he : ∀ q, e q = (positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading I) 3 q))
    (s : SchemeModuleGlobalSectionsOver (toBase I) (positiveSheafOfModules (grading I) 3)) :
    (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom
      ((SheafOfModules.sectionsMap
        (cubicClosedPointSerreSurfaceJetCotangent_pointChartUnitIso
          (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)
          (Spec.map (CommRingCat.ofHom g)) (positiveSheafOfModules (grading I) 3)
          (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeLinearChartUnitIso I ell)).hom
        (pullbackSection (Spec.map (CommRingCat.ofHom g) ≫
          cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)
          (positiveSheafOfModules (grading I) 3) (isIso_pullbackUnitComparison _)
          ((positiveSheafOfModules (grading I) 3).unitHomEquiv s))).val (op ⊤)) =
      cubicClosedPointSerreSurfaceJetCotangent_positiveGlobalChartRestriction I ell g hbase e s := by
  let A := Away (grading I) (ell : CoordinateRing I)
  let T := positiveSheafOfModules (grading I) 3
  let f := cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell
  let j := Spec.map (CommRingCat.ofHom g)
  let p := cubicClosedPointSerreSurfaceJetCotangent_positiveThreeLinearChartUnitIso I ell
  let r := unitEndomorphismValue ((Scheme.Modules.restrictUnitIso f).inv ≫
    (Scheme.Modules.restrictFunctor f).map s ≫ p.hom)
  have hpoint := cubicClosedPointSerreSurfaceJetCotangent_pointChartUnitIso_sectionCoordinate
    f j T p (T.unitHomEquiv s)
  erw [T.unitHomEquiv.symm_apply_apply] at hpoint
  have hvalue := congrArg (fun t : (SheafOfModules.unit (Spec (CommRingCat.of L)).ringCatSheaf).sections =>
    (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom (t.val (op ⊤))) hpoint
  rw [regularSectionValue] at hvalue
  have hn := congrArg (fun m : CommRingCat.of Γ(Spec (CommRingCat.of A), ⊤) ⟶ CommRingCat.of L =>
    m.hom r) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g))
  exact hvalue.trans (hn.trans
    (cubicClosedPointSerreSurfaceJetCotangent_positiveGlobalChartRestriction_coordinate
      I ell g hbase e he s).symm)

end PfaffianDescent
