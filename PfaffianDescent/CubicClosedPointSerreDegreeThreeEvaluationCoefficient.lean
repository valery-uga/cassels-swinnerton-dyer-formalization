import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationBaseChange
import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationSchemeIso
import AllCharacteristics.HypersurfaceCoefficientNaturality

/-! # Literal coefficient pullback of the original Serre extension -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual coefficient morphism of the original cubic. -/
def cubicClosedPointSerreDegreeThreeEvaluationCoefficientMap
    {K F : Type u} [Field K] [Field F] (b : K →+* F)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    hypersurface (p.map b) (hp.map b) ⟶ hypersurface p hp :=
  projectiveCoefficientMap b (equationIdeal p hp)
    (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp)

/-- The actual coefficient-surface pullback has the same global sections
as the actual categorical field pullback, through the proved geometric
base-change isomorphism and the actual module pullback comparison. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationCoefficient_finrank_eq_pullback
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (E : (hypersurface p hp).Modules) :
    Module.finrank F (SchemeModuleGlobalSectionsOver
      (schemeFieldBaseChangeToField (L := F) (hypersurfaceToBase p hp))
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := F) (hypersurfaceToBase p hp))).obj E)) =
    Module.finrank F (SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicClosedPointSerreDegreeThreeEvaluationCoefficientMap (algebraMap K F) p hp)).obj E)) := by
  let t := hypersurfaceBaseChangeIso (algebraMap K F) p hp
  let pr := schemeFieldBaseChangeToOriginal (L := F) (hypersurfaceToBase p hp)
  let base := schemeFieldBaseChangeToField (L := F) (hypersurfaceToBase p hp)
  let f := cubicClosedPointSerreDegreeThreeEvaluationCoefficientMap (algebraMap K F) p hp
  have hsnd : t.hom ≫ base =
      hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)) :=
    hypersurfaceBaseChangeIso_hom_snd (algebraMap K F) p hp
  have hfst : t.hom ≫ pr = f :=
    hypersurfaceBaseChangeIso_hom_fst (algebraMap K F) p hp
  let q₁ := cubicClosedPointSerreDegreeThreeEvaluationSchemeIsoLinearEquiv base t
    ((Scheme.Modules.pullback pr).obj E)
  let a := (Scheme.Modules.pullbackComp t.hom pr).app E ≪≫
    (Scheme.Modules.pullbackCongr hfst).app E
  let q₂ := cubicClosedPointSerreDegreeThreeEvaluationModuleIsoLinearEquiv (t.hom ≫ base) a
  have h := q₁.finrank_eq.trans q₂.finrank_eq
  rw [hsnd] at h
  exact h

end PfaffianDescent.ProjectiveNegativeTwist
