import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeEtaleOpen
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualEtaleFibreStalkField
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFlatFieldStalk

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_etaleOpen_fibre_stalk_isField
    {E : Type u} [Field E] {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) (s : Spec (.of E) ⟶ Y) (z : (pullback g s : Scheme))
    (hz : pullback.fst g s z ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen g) :
    IsField ((pullback g s).presheaf.stalk z) := by
  let W := cubicClosedPointSerreFiniteZeroResidual_etaleOpen g
  let e := pullbackRightPullbackFstIso g s W.ι
  let a : pullback (W.ι ≫ g) s ⟶ pullback g s :=
    e.inv ≫ pullback.snd W.ι (pullback.fst g s)
  have ha : IsOpenImmersion a := by dsimp [a]; infer_instance
  letI : IsOpenImmersion a := ha
  letI : Etale (W.ι ≫ g) := cubicClosedPointSerreFiniteZeroResidual_etaleOpen_etale g
  have hr : z ∈ Set.range (pullback.snd W.ι (pullback.fst g s)) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    change pullback.fst g s z ∈ W.ι.opensRange
    simpa only [Scheme.Opens.opensRange_ι] using hz
  obtain ⟨u, hu⟩ := hr
  let v := e.hom u
  have hv : a v = z := by
    change (e.hom ≫ e.inv ≫ pullback.snd W.ι (pullback.fst g s)) u = z
    simpa only [Iso.hom_inv_id_assoc] using hu
  have hf := cubicClosedPointSerreFiniteZeroResidual_unramifiedField_stalk_isField
    (pullback.snd (W.ι ≫ g) s) v
  have ht := cubicClosedPointSerreFiniteZeroResidual_flat_stalk_isField a v hf
  exact hv ▸ ht

end PfaffianDescent
