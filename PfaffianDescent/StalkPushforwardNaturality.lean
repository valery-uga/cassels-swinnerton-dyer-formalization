import Mathlib.Topology.Sheaves.Stalks

/-!
# Naturality of the pushforward-stalk comparison

For a continuous map `f : X ⟶ Y` and `x : X`, Mathlib provides the
comparison from the stalk at `f x` of a pushforward presheaf to the original
stalk at `x`.  This file packages those component maps into a natural
transformation and, when `f` is inducing, into a natural isomorphism.
-/

noncomputable section

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u v

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison from a pushforward stalk at an image point to the
original stalk, naturally in the presheaf. -/
def presheafStalkPushforwardNatTrans
    {C : Type u} [Category.{v} C] [HasColimits.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (x : X) :
    TopCat.Presheaf.pushforward C f ⋙ TopCat.Presheaf.stalkFunctor C (f x) ⟶
      TopCat.Presheaf.stalkFunctor C x where
  app F := F.stalkPushforward C f x
  naturality F G η := by
    apply TopCat.Presheaf.stalk_hom_ext _
    intro U hU
    change ((TopCat.Presheaf.pushforward C f).obj F).germ U (f x) hU ≫
        ((TopCat.Presheaf.stalkFunctor C (f x)).map
            ((TopCat.Presheaf.pushforward C f).map η) ≫
          G.stalkPushforward C f x) =
      ((TopCat.Presheaf.pushforward C f).obj F).germ U (f x) hU ≫
        (F.stalkPushforward C f x ≫
          (TopCat.Presheaf.stalkFunctor C x).map η)
    rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ,
      Category.assoc, TopCat.Presheaf.stalkPushforward_germ]
    have hxU : x ∈ (Opens.map f).obj U := hU
    change η.app (Opposite.op ((Opens.map f).obj U)) ≫
        G.germ ((Opens.map f).obj U) x hxU = _
    rw [← Category.assoc, TopCat.Presheaf.stalkPushforward_germ,
      TopCat.Presheaf.stalkFunctor_map_germ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For an inducing map, the pushforward-stalk comparison is a natural
isomorphism. -/
def presheafStalkPushforwardNatIso
    {C : Type u} [Category.{v} C] [HasColimits.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (hf : IsInducing f) (x : X) :
    TopCat.Presheaf.pushforward C f ⋙ TopCat.Presheaf.stalkFunctor C (f x) ≅
      TopCat.Presheaf.stalkFunctor C x := by
  refine NatIso.ofComponents (fun F ↦ ?_) ?_
  · letI : IsIso (F.stalkPushforward C f x) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        C hf F x
    exact asIso (F.stalkPushforward C f x)
  · intro F G η
    exact (presheafStalkPushforwardNatTrans (C := C) f x).naturality η

end PfaffianDescent
