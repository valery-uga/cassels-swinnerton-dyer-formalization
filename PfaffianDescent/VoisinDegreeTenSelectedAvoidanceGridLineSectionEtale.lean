import PfaffianDescent.CubicLineFiniteSubscheme
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceRankThreeEtale
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_lineSectionDatum_etale_of_no_section
    {K : Type u} [Field K] [CharZero K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    let D := cubicLineSectionDatum (by decide : 2 ≤ 4) p hp hp0
    Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  let D := cubicLineSectionDatum (by decide : 2 ≤ 4) p hp hp0
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  exact voisinDegreeTenSelectedAvoidance_rankThree_etale p hp hno D.val.subschemeι
    (D.property.2.2.2 (IsLocalRing.closedPoint K))
end PfaffianDescent
