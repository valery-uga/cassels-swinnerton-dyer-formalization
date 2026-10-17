import PfaffianDescent.CubicClosedPointSerreZeroIdealStalk
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Literal open-pullback point ideals and their localizations -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual ideal of the actual open pullback localizes by the literal
open-immersion stalk map from the original affine ideal localization.
No identification of the pullback point scheme is supplied or used. -/
theorem cubicClosedPointSerreZeroIdealStalkPullback_map_eq_map
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (y : U.1) :
    letI : IsAffine (U.1 : Scheme.{u}) := U.2
    let Y := (U.1 : Scheme.{u})
    let j := pullback.snd i U.1.ι
    let W : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
    let A : X.affineOpens := ⟨U.1.ι ''ᵁ (⊤ : Y.Opens),
      (isAffineOpen_top Y).image_of_isOpenImmersion U.1.ι⟩
    (j.ker.ideal W).map (Y.presheaf.germ ⊤ y trivial).hom =
      ((i.ker.ideal A).map
        (X.presheaf.germ A.1 (U.1.ι y) ⟨y, trivial, rfl⟩).hom).map
          (U.1.ι.stalkMap y).hom := by
  letI : IsAffine (U.1 : Scheme.{u}) := U.2
  let Y := (U.1 : Scheme.{u})
  let j := pullback.snd i U.1.ι
  let W : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let A : X.affineOpens := ⟨U.1.ι ''ᵁ (⊤ : Y.Opens),
    (isAffineOpen_top Y).image_of_isOpenImmersion U.1.ι⟩
  have H : IsPullback j (pullback.fst i U.1.ι) U.1.ι i :=
    (IsPullback.of_hasPullback i U.1.ι).flip
  have hk : j.ker.ideal W = i.ker.ideal A := by
    have hk₀ := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i j
      (pullback.fst i U.1.ι) U.1.ι H W
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv] at hk₀
    change j.ker.ideal W = (i.ker.ideal A).comap (RingHom.id _) at hk₀
    simpa only [Ideal.comap_id] using hk₀
  have hg : X.presheaf.germ A.1 (U.1.ι y) ⟨y, trivial, rfl⟩ ≫ U.1.ι.stalkMap y =
      Y.presheaf.germ ⊤ y trivial := by
    rw [← U.1.stalkIso_inv y]
    exact U.1.germ_stalkIso_inv ⊤ y trivial
  change (j.ker.ideal W).map (Y.presheaf.germ ⊤ y trivial).hom = _
  rw [hk, Ideal.map_map, ← CommRingCat.hom_comp, hg]

/-- At the literal original point of the affine open, the actual pullback
point ideal localizes to the actual open scheme's maximal ideal. -/
theorem cubicClosedPointSerreZeroIdealStalkPullback_map_eq_maximal
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (hx : i default ∈ U.1) :
    letI : IsAffine (U.1 : Scheme.{u}) := U.2
    let Y := (U.1 : Scheme.{u})
    let y : Y := ⟨i default, hx⟩
    let j := pullback.snd i U.1.ι
    let W : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
    (j.ker.ideal W).map (Y.presheaf.germ ⊤ y trivial).hom =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  dsimp only
  letI : IsAffine (U.1 : Scheme.{u}) := U.2
  let Y := (U.1 : Scheme.{u})
  let y : Y := ⟨i default, hx⟩
  let A : X.affineOpens := ⟨U.1.ι ''ᵁ (⊤ : Y.Opens),
    (isAffineOpen_top Y).image_of_isOpenImmersion U.1.ι⟩
  have hm : (i.ker.ideal A).map (X.presheaf.germ A.1 (U.1.ι y) ⟨y, trivial, rfl⟩).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (U.1.ι y)) :=
    cubicClosedPointSerreZeroIdealStalk_map_eq_maximal i A default ⟨y, trivial, rfl⟩
  calc
    _ = ((i.ker.ideal A).map
        (X.presheaf.germ A.1 (U.1.ι y) ⟨y, trivial, rfl⟩).hom).map
          (U.1.ι.stalkMap y).hom :=
      cubicClosedPointSerreZeroIdealStalkPullback_map_eq_map i U y
    _ = (IsLocalRing.maximalIdeal (X.presheaf.stalk (U.1.ι y))).map
          (U.1.ι.stalkMap y).hom := congrArg (Ideal.map (U.1.ι.stalkMap y).hom) hm
    _ = _ := IsLocalRing.map_maximalIdeal_of_surjective (U.1.ι.stalkMap y).hom
      (ConcreteCategory.bijective_of_isIso (U.1.ι.stalkMap y)).2

/-- Away from the literal original point, the actual open-pullback point
ideal localizes to the unit ideal. -/
theorem cubicClosedPointSerreZeroIdealStalkPullback_map_eq_top_off_point
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (y : U.1) (hy : U.1.ι y ≠ i default) :
    letI : IsAffine (U.1 : Scheme.{u}) := U.2
    let Y := (U.1 : Scheme.{u})
    let j := pullback.snd i U.1.ι
    let W : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
    (j.ker.ideal W).map (Y.presheaf.germ ⊤ y trivial).hom = ⊤ := by
  dsimp only
  letI : IsAffine (U.1 : Scheme.{u}) := U.2
  let Y := (U.1 : Scheme.{u})
  let A : X.affineOpens := ⟨U.1.ι ''ᵁ (⊤ : Y.Opens),
    (isAffineOpen_top Y).image_of_isOpenImmersion U.1.ι⟩
  rw [cubicClosedPointSerreZeroIdealStalkPullback_map_eq_map i U y,
    cubicClosedPointSerreZeroIdealStalk_map_eq_top_off_point i A (U.1.ι y) ⟨y, trivial, rfl⟩ hy,
    Ideal.map_top]

end PfaffianDescent
