import PfaffianDescent.CubicPointTraceFieldBaseChangeNegativeTwist
import AllCharacteristics.ProjectiveBaseChangeNaturality
import AllCharacteristics.HypersurfaceCoefficientNaturality

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Literal twice coefficient cubic is canonically the direct coefficient cubic. -/
def pointSplittingCubicSerreGroundChosenSection_coefficientCompIso
    {K F E : Type u} [Field K] [Field F] [Field E]
    (a : K →+* F) (β : F →+* E)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    hypersurface ((p.map a).map β) ((hp.map a).map β) ≅
      hypersurface (p.map (β.comp a)) (hp.map (β.comp a)) :=
  eqToIso (congrArg scheme (equationIdeal_congr
    ((p.map a).map β) (p.map (β.comp a)) ((hp.map a).map β) (hp.map (β.comp a))
    (MvPolynomial.map_map a β p)))

/-- The actual coefficient comparison identifies the literal composite map
with the direct original-cubic coefficient projection. -/
theorem pointSplittingCubicSerreGroundChosenSection_coefficientCompIso_hom
    {K F E : Type u} [Field K] [Field F] [Field E]
    (a : K →+* F) (β : F →+* E)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (pointSplittingCubicSerreGroundChosenSection_coefficientCompIso a β p hp).hom ≫
      cubicPointTraceFieldBaseChangeCubicCoefficientMap (β.comp a) p hp =
    cubicPointTraceFieldBaseChangeCubicCoefficientMap β (p.map a) (hp.map a) ≫
      cubicPointTraceFieldBaseChangeCubicCoefficientMap a p hp := by
  let I := equationIdeal p hp
  let J := equationIdeal (p.map a) (hp.map a)
  let H := equationIdeal ((p.map a).map β) ((hp.map a).map β)
  let H' := equationIdeal (p.map (β.comp a)) (hp.map (β.comp a))
  have hH : H = H' := equationIdeal_congr _ _ _ _ (MvPolynomial.map_map a β p)
  have h := projectiveCoefficientMap_transport (β.comp a) I I H H'
    (coefficientIdeal_comp a β I J H (equationIdeal_map a p hp)
      (equationIdeal_map β (p.map a) (hp.map a)))
    (equationIdeal_map (β.comp a) p hp) rfl hH
  simp only [eqToHom_refl, Category.comp_id] at h
  exact h.trans (projectiveCoefficientMap_comp a β I J H
    (equationIdeal_map a p hp) (equationIdeal_map β (p.map a) (hp.map a))).symm

end PfaffianDescent
