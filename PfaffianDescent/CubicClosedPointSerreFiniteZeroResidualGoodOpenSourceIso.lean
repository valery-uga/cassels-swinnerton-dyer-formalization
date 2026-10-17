import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpen

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_goodOpen_comp_iso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : Z ≅ X) :
    cubicClosedPointSerreFiniteZeroResidual_goodOpen (e.hom ≫ f) =
      cubicClosedPointSerreFiniteZeroResidual_goodOpen f := by
  ext y
  constructor
  · intro h x hx
    have hinv : e.hom (e.inv x) = x := by
      change (e.inv ≫ e.hom) x = x
      rw [Iso.inv_hom_id]
      rfl
    have hx' : (e.hom ≫ f) (e.inv x) = y := by
      change f (e.hom (e.inv x)) = y
      rw [hinv]
      exact hx
    have hq := Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mp (h _ hx')
    rw [hinv] at hq
    exact hq
  · intro h x hx
    exact Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mpr (h _ hx)

theorem cubicClosedPointSerreFiniteZeroResidual_flat_restrict_comp_iso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Z ≅ X) (V : Y.Opens)
    [Flat (f ∣_ V)] : Flat ((e.hom ≫ f) ∣_ V) := by
  have h0 : Flat (f ∣_ V.ι.opensRange) := by
    rw [Scheme.Opens.opensRange_ι]
    infer_instance
  letI : Flat (pullback.snd f V.ι) :=
    (MorphismProperty.arrow_mk_iso_iff @Flat (morphismRestrictOpensRange f V.ι)).mp h0
  let j := pullback.map (e.hom ≫ f) V.ι f V.ι e.hom (𝟙 _) (𝟙 _) (by simp) (by simp)
  letI : IsIso j := by dsimp [j]; infer_instance
  have hj : j ≫ pullback.snd f V.ι = pullback.snd (e.hom ≫ f) V.ι := by
    simp [j, pullback.map]
  letI : Flat (pullback.snd (e.hom ≫ f) V.ι) := by
    rw [← hj]
    infer_instance
  have h1 : Flat ((e.hom ≫ f) ∣_ V.ι.opensRange) :=
    (MorphismProperty.arrow_mk_iso_iff @Flat
      (morphismRestrictOpensRange (e.hom ≫ f) V.ι)).mpr inferInstance
  rw [Scheme.Opens.opensRange_ι] at h1
  exact h1

end PfaffianDescent
