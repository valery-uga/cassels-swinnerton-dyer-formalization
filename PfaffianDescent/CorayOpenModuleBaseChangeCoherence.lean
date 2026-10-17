import PfaffianDescent.CorayOpenModuleBaseChange

/-!
Canonical open base change is natural and is the actual mate of the two
pushforward-composition comparisons. These laws use only actual open
restriction adjunctions and presheaf maps; no projection-formula, dualizing
identification or map invertibility is supplied.
SOURCE ONLY / UNVERIFIED; root owns compiler and acceptance checks.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary functor composition on abelian-group maps, before any native
section carrier or open-restriction substitutions. -/
private theorem openBaseChangeTwoStepMapApply
    {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{u})
    {A B B' D : C} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ B') (d : B' ⟶ D) (h : a ≫ b = c ≫ d) (s : F.obj A) :
    (F.map b).hom ((F.map a).hom s) =
      (F.map d).hom ((F.map c).hom s) := by
  calc
    _ = (F.map (a ≫ b)).hom s := by
      rw [F.map_comp] <;> rfl
    _ = (F.map (c ≫ d)).hom s :=
      congrArg (fun k : A ⟶ D => (F.map k).hom s) h
    _ = _ := by
      rw [F.map_comp] <;> rfl

/-- The actual section transport is natural in the original module map. -/
theorem schemeModuleOpenPushforwardBaseChange_naturality
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    {M N : Y.Modules} (a : M ⟶ N) :
    (Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pushforward f).map a) ≫
      (schemeModuleOpenPushforwardBaseChangeIso f U N).hom =
    (schemeModuleOpenPushforwardBaseChangeIso f U M).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map a) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change N.presheaf.map
      (eqToHom (image_morphismRestrict_preimage f U V.unop)).op
      (a.app (f ⁻¹ᵁ (U.ι ''ᵁ V.unop)) s) =
    a.app ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V.unop))
      (M.presheaf.map
        (eqToHom (image_morphismRestrict_preimage f U V.unop)).op s)
  exact (PresheafOfModules.naturality_apply a.val
    (eqToHom (image_morphismRestrict_preimage f U V.unop)).op s).symm

/-- The original Cartesian open square gives its actual pushforward
composition comparison, before any restriction-adjunction mate. -/
def schemeModuleOpenPushforwardCompositionIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (N : (f ⁻¹ᵁ U).toScheme.Modules) :
    (Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj N) ≅
    (Scheme.Modules.pushforward U.ι).obj
        ((Scheme.Modules.pushforward (f ∣_ U)).obj N) :=
  (Scheme.Modules.pushforwardComp (f ⁻¹ᵁ U).ι f).app N ≪≫
    (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm).app N ≪≫
    ((Scheme.Modules.pushforwardComp (f ∣_ U) U.ι).app N).symm

/-- The actual open base change intertwines the TWO actual restriction
counits. Every section map is a restriction along an equality of opens. -/
theorem schemeModuleOpenPushforwardBaseChange_counit_square
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (N : (f ⁻¹ᵁ U).toScheme.Modules) :
    (schemeModuleOpenPushforwardBaseChangeIso f U
        ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj N)).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).counit.app N) =
    (Scheme.Modules.restrictFunctor U.ι).map
        (schemeModuleOpenPushforwardCompositionIso f U N).hom ≫
      (Scheme.Modules.restrictAdjunction U.ι).counit.app
        ((Scheme.Modules.pushforward (f ∣_ U)).obj N) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let j := f ∣_ U
  let v := (f ⁻¹ᵁ U).ι
  change Γ(N, (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ (U.ι ''ᵁ V.unop))) at s
  let h := image_morphismRestrict_preimage f U V.unop
  let hc : (j ≫ U.ι) ⁻¹ᵁ (U.ι ''ᵁ V.unop) =
      (v ≫ f) ⁻¹ᵁ (U.ι ''ᵁ V.unop) :=
    congrArg (fun g : (f ⁻¹ᵁ U).toScheme ⟶ X => g ⁻¹ᵁ (U.ι ''ᵁ V.unop))
      (morphismRestrict_ι f U)
  change N.presheaf.map (eqToHom (v.preimage_image_eq (j ⁻¹ᵁ V.unop)).symm).op
      (N.presheaf.map ((Opens.map v.base).map (eqToHom h)).op s) =
    N.presheaf.map
      ((Opens.map j.base).map (eqToHom (U.ι.preimage_image_eq V.unop).symm)).op
      (N.presheaf.map (eqToHom hc).op s)
  exact openBaseChangeTwoStepMapApply N.presheaf
    ((Opens.map v.base).map (eqToHom h)).op
    (eqToHom (v.preimage_image_eq (j ⁻¹ᵁ V.unop)).symm).op
    (eqToHom hc).op
    ((Opens.map j.base).map (eqToHom (U.ι.preimage_image_eq V.unop).symm)).op
    (Subsingleton.elim _ _) s

/-- The section-defined comparison IS the canonical restriction-adjunction
mate of the genuine pushforward composition square. This preserves the
actual map, rather than choosing an arbitrary base-change equivalence. -/
theorem schemeModuleOpenPushforwardBaseChange_mate
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (M : Y.Modules) :
    (schemeModuleOpenPushforwardBaseChangeIso f U M).hom =
    (Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M)) ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (schemeModuleOpenPushforwardCompositionIso f U
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)).hom ≫
      (Scheme.Modules.restrictAdjunction U.ι).counit.app
        ((Scheme.Modules.pushforward (f ∣_ U)).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let G := Scheme.Modules.pushforward f
  let V := Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let J := Scheme.Modules.pushforward (f ∣_ U)
  let A := Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι
  have hn := schemeModuleOpenPushforwardBaseChange_naturality f U (A.unit.app M)
  change R.map (G.map (A.unit.app M)) ≫
      (schemeModuleOpenPushforwardBaseChangeIso f U
        ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj (V.obj M))).hom =
    (schemeModuleOpenPushforwardBaseChangeIso f U M).hom ≫
      J.map (V.map (A.unit.app M)) at hn
  have hc := schemeModuleOpenPushforwardBaseChange_counit_square f U (V.obj M)
  change (schemeModuleOpenPushforwardBaseChangeIso f U
      ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj (V.obj M))).hom ≫
      J.map (A.counit.app (V.obj M)) =
    R.map (schemeModuleOpenPushforwardCompositionIso f U (V.obj M)).hom ≫
      (Scheme.Modules.restrictAdjunction U.ι).counit.app (J.obj (V.obj M)) at hc
  symm
  calc
    _ = R.map (G.map (A.unit.app M)) ≫
        ((schemeModuleOpenPushforwardBaseChangeIso f U
          ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj (V.obj M))).hom ≫
          J.map (A.counit.app (V.obj M))) := by
      rw [← hc]
    _ = (schemeModuleOpenPushforwardBaseChangeIso f U M).hom ≫
        J.map (V.map (A.unit.app M) ≫ A.counit.app (V.obj M)) := by
      rw [← Category.assoc, hn, Category.assoc, ← J.map_comp]
    _ = _ := by
      rw [A.left_triangle_components M, J.map_id, Category.comp_id]

end PfaffianDescent
end
