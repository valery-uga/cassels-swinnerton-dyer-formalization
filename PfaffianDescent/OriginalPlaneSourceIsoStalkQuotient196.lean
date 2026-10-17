import PfaffianDescent.OriginalPlaneSectionNativeStalk196
import PfaffianDescent.CorayActualGenericPlaneSectionSchemeIso
import PfaffianDescent.CorayActualGenericPlaneCubicSmooth

/-! The principal quotient is transferred to the SAME original source
stalk through the genuine geometric Scheme Iso. Actual original substitution
and immersion factorization, rather than an assumed stalk equivalence, supply
the generic-plane specialization. No separability is claimed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine source Scheme Iso transports the quotient to the ORIGINAL
source stalk by its actual scheme stalk map. -/
def originalPlaneSourceIsoStalkQuotientEquiv196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    (x : X) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x) ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    ((hypersurface p hp).presheaf.stalk
      (cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x)) ⧸
      Ideal.span ({originalPlaneSectionStalkScalar196 p l hp hl (e.hom x) j hx} : Set _)) ≃+*
      X.presheaf.stalk x :=
  (originalPlaneSectionStalkQuotientEquiv196 p l hp hp0 hl hl0 (e.hom x) j hx).trans
    (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv

/-- The quotient map to the ORIGINAL source is precisely the literal
composition of the original immersion's stalk map and the genuine source
Iso's stalk map. These maps are constructed, not comparison premises. -/
theorem originalPlaneSourceIsoStalkQuotientEquiv_mk196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    (x : X) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x) ∈
      quotientCoordinateOpen (equationIdeal p hp) j)
    (r : (hypersurface p hp).presheaf.stalk
      (cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x))) :
    originalPlaneSourceIsoStalkQuotientEquiv196 p l hp hp0 hl hl0 X e x j hx
      (Ideal.Quotient.mk _ r) =
      (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl).stalkMap x r := by
  rw [originalPlaneSourceIsoStalkQuotientEquiv196, RingEquiv.trans_apply,
    originalPlaneSectionStalkQuotientEquiv_mk196, Scheme.Hom.stalkMap_comp]
  rfl

/-- The genuine literal generic-plane cubic Iso recovers the original
restricted polynomial immersion, with no assumed immersion square. -/
theorem genericPlaneCubicOriginalSurfaceImmersion_factorization196
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (genericPlaneCubicPairSchemeIso p hp).hom ≫
      cubicSecondEquationCurveImmersion (p.map (algebraMap K (GenericHyperplaneField K)))
        (genericHyperplaneEquation (K := K)) (hp.map _) 1
        genericHyperplaneEquation_isHomogeneous =
      planeSectionRestrictionImmersion (genericHyperplaneCoefficient (K := K))
        (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _) :=
  planeSectionSchemeIso_hom_immersion _ _ _

/-- The SAME original generic-plane cubic stalk is a principal quotient
of the original surface stalk. Only original cubic data and an ordinary
standard coordinate neighborhood are supplied; quotient/regularity/stalk
comparison data are constructed internally, over any original field. -/
def genericPlaneCubicOriginalStalkQuotientEquiv196
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp))
    (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion (p.map (algebraMap K (GenericHyperplaneField K)))
      (genericHyperplaneEquation (K := K)) (hp.map _) 1
      genericHyperplaneEquation_isHomogeneous ((genericPlaneCubicPairSchemeIso p hp).hom x) ∈
        quotientCoordinateOpen (equationIdeal (p.map (algebraMap K (GenericHyperplaneField K)))
          (hp.map _)) j) :
    let L := GenericHyperplaneField K
    let pL := p.map (algebraMap K L)
    let hpL := hp.map (algebraMap K L)
    let l := genericHyperplaneEquation (K := K)
    let hl := genericHyperplaneEquation_isHomogeneous (K := K)
    let y := (genericPlaneCubicPairSchemeIso p hp).hom x
    ((hypersurface pL hpL).presheaf.stalk (cubicSecondEquationCurveImmersion pL l hpL 1 hl y) ⧸
      Ideal.span ({originalPlaneSectionStalkScalar196 pL l hpL hl y j hx} : Set _)) ≃+*
      (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)).presheaf.stalk x := by
  let L := GenericHyperplaneField K
  let pL := p.map (algebraMap K L)
  let hpL := hp.map (algebraMap K L)
  have hpL0 : pL ≠ 0 := by
    intro hz
    apply hp0
    apply MvPolynomial.map_injective (algebraMap K L) (algebraMap K L).injective
    simpa only [map_zero] using hz
  letI : Smooth (hypersurfaceToBase pL hpL) :=
    smooth_hypersurfaceToBase_map (algebraMap K L) p hp
  exact originalPlaneSourceIsoStalkQuotientEquiv196 pL (genericHyperplaneEquation (K := K))
    hpL hpL0 genericHyperplaneEquation_isHomogeneous genericHyperplaneEquation_ne_zero
    _ (genericPlaneCubicPairSchemeIso p hp) x j hx

end PfaffianDescent.Coray
