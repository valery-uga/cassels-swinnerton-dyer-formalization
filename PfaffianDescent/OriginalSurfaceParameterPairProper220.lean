import PfaffianDescent.LocalParameterPairProper220
import PfaffianDescent.OriginalSurfaceTargetQuotientCoordinate212

/-! The actual original curve stalkMap derives properness of its lifted
point pair. Neither generator membership nor properness is a premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial IsLocalRing
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original plane scalar maps to zero by196's actual quotient. A
lift of the original maximal-ideal point parameter is also in the original
surface maximal ideal, because the literal stalkMap is a local hom. -/
theorem originalSurfaceParameterPair_mem_maximal220
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    (x : X) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x) ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    let s := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
    let R := (hypersurface p hp).presheaf.stalk (s x)
    let B := X.presheaf.stalk x
    let f := originalPlaneSectionStalkScalar196 p l hp hl (e.hom x) j hx
    ∀ (t : B) (hspan : maximalIdeal B = Ideal.span {t}) (g : R),
      s.stalkMap x g = t →
      f ∈ maximalIdeal R ∧ g ∈ maximalIdeal R ∧
        (1 : R) ∉ Ideal.span ({f, g} : Set R) := by
  dsimp only
  intro t hspan g hgt
  let s := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
  let f := originalPlaneSectionStalkScalar196 p l hp hl (e.hom x) j hx
  let eR := originalPlaneSourceIsoStalkQuotientEquiv196 p l hp hp0 hl hl0 X e x j hx
  have hphi := originalSurfaceSource_stalkMap_quotient212 p l hp hp0 hl hl0 X e x j hx
  have hfzero : s.stalkMap x f = 0 := by
    have hq : Ideal.Quotient.mk (Ideal.span {f}) f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
    change (s.stalkMap x).hom f = 0
    erw [hphi, RingHom.comp_apply, hq, map_zero]
  have htm : t ∈ maximalIdeal (X.presheaf.stalk x) := by
    rw [hspan]
    exact Ideal.mem_span_singleton_self t
  exact localParameterPair_mem_maximal220 (s.stalkMap x).hom f g t hfzero htm hgt

end PfaffianDescent.Coray
