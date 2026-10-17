import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The native spectrum of an actual affine product chart maps openly into
the original constant family over the native spectrum of the base chart. -/
def cubicClosedPointSerreFiniteZeroResidual_affineProductOpenChart
    {X E S : Scheme.{u}} [IsAffine E] [IsAffine S]
    (f : X ⟶ S) (U : X.affineOpens) (k : E ⟶ S) :
    Spec Γ(pullback (U.1.ι ≫ f) k, ⊤) ⟶ pullback f (E.isoSpec.inv ≫ k) := by
  letI : IsAffine (U.1 : Scheme.{u}) := U.2
  let T := pullback (U.1.ι ≫ f) k
  exact T.isoSpec.inv ≫ pullback.map (U.1.ι ≫ f) k f (E.isoSpec.inv ≫ k)
    U.1.ι E.isoSpec.hom (𝟙 _) (by simp) (by simp)

instance cubicClosedPointSerreFiniteZeroResidual_affineProductOpenChart_isOpenImmersion
    {X E S : Scheme.{u}} [IsAffine E] [IsAffine S]
    (f : X ⟶ S) (U : X.affineOpens) (k : E ⟶ S) :
    IsOpenImmersion (cubicClosedPointSerreFiniteZeroResidual_affineProductOpenChart f U k) := by
  dsimp [cubicClosedPointSerreFiniteZeroResidual_affineProductOpenChart]
  infer_instance

theorem cubicClosedPointSerreFiniteZeroResidual_affineProductOpenChart_comp
    {X E S : Scheme.{u}} [IsAffine E] [IsAffine S]
    (f : X ⟶ S) (U : X.affineOpens) (k : E ⟶ S) :
    cubicClosedPointSerreFiniteZeroResidual_affineProductOpenChart f U k ≫
      pullback.snd f (E.isoSpec.inv ≫ k) =
        Spec.map ((pullback.snd (U.1.ι ≫ f) k).appTop) := by
  letI : IsAffine (U.1 : Scheme.{u}) := U.2
  let T := pullback (U.1.ι ≫ f) k
  change T.isoSpec.inv ≫ _ ≫ _ = _
  simp only [Category.assoc, pullback.map, pullback.lift_snd]
  rw [← Scheme.isoSpec_hom_naturality]
  simp

end PfaffianDescent
