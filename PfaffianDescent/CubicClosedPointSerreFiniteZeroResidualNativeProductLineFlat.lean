import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeProductZeroFlat
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualProjectiveLineLocal

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreFiniteZeroResidual_projectiveLine_openImmersion_stalk_regular_dim_le_one
    {K : Type u} [Field K] {E : Scheme.{u}}
    (r : E ⟶ projectiveLineProj K) [IsOpenImmersion r] (y : E) :
    IsRegularLocalRing (E.presheaf.stalk y) ∧ ringKrullDim (E.presheaf.stalk y) ≤ 1 := by
  let e := (asIso (r.stalkMap y)).commRingCatIsoToRingEquiv
  constructor
  · letI := cubicClosedPointSerreFiniteZeroResidual_projectiveLine_stalk_regular K (r y)
    exact IsRegularLocalRing.of_ringEquiv e
  · rw [← ringKrullDim_eq_of_ringEquiv e]
    exact cubicClosedPointSerreFiniteZeroResidual_projectiveLine_stalk_dim_le_one K (r y)

theorem cubicClosedPointSerreFiniteZeroResidual_nativeProduct_pair_zero_flat_over_projectiveLine
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (U : (hypersurface p hp).affineOpens)
    {E : Scheme.{u}} [IsAffine E] [IsDomain Γ(E, ⊤)] [IsPrincipalIdealRing Γ(E, ⊤)]
    (r : E ⟶ projectiveLineProj K) [IsOpenImmersion r]
    [IsNoetherianRing Γ(pullback (U.1.ι ≫ hypersurfaceToBase p hp)
      (r ≫ projectiveLineProjToBase K), ⊤)]
    (I : (pullback (U.1.ι ≫ hypersurfaceToBase p hp)
      (r ≫ projectiveLineProjToBase K)).IdealSheafData)
    (a b : Γ(pullback (U.1.ι ≫ hypersurfaceToBase p hp)
      (r ≫ projectiveLineProjToBase K), ⊤))
    (hI : I.ideal ⟨⊤, by
      letI : IsAffine (U.1 : Scheme.{u}) := U.2
      exact isAffineOpen_top _⟩ = Ideal.span ({a, b} : Set _))
    [LocallyQuasiFinite (I.subschemeι ≫ pullback.snd (U.1.ι ≫ hypersurfaceToBase p hp)
      (r ≫ projectiveLineProjToBase K))] :
    Flat (I.subschemeι ≫ pullback.snd (U.1.ι ≫ hypersurfaceToBase p hp)
      (r ≫ projectiveLineProjToBase K)) := by
  apply cubicClosedPointSerreFiniteZeroResidual_nativeProduct_pair_zero_flat
    p hp hp0 U (r ≫ projectiveLineProjToBase K) I a b hI
  · intro y
    exact (cubicClosedPointSerreFiniteZeroResidual_projectiveLine_openImmersion_stalk_regular_dim_le_one r y).1
  · intro y
    exact (cubicClosedPointSerreFiniteZeroResidual_projectiveLine_openImmersion_stalk_regular_dim_le_one r y).2

end PfaffianDescent
