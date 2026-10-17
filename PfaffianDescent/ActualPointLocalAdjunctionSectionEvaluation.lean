import PfaffianDescent.ActualGlobalPointAdjunctionSectionEvaluation

/- SOURCE ONLY / UNVERIFIED. A LOCAL ideal/module section is evaluated
at the SAME original field point using the genuine adjunction unit at U.
Only the actual preimage-top transport is used; global sections need not
span the point fiber. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u

def actualPointLocalSectionClass
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules)
    (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤) (z : M.val.obj (op U)) :
    (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M) :=
  ((Scheme.Modules.pullback q).obj M).val.map (eqToHom (congrArg op hU))
    (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app M).val.app (op U) z)

lemma actualPointLocalAdjunctionSectionEvaluation
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules) (N : (Spec (.of L)).Modules)
    (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤) (z : M.val.obj (op U))
    (d : (Scheme.Modules.pullback q).obj M ⟶ N) :
    (moduleSpecΓFunctor (R := .of L)).map d (actualPointLocalSectionClass q M U hU z) =
    N.val.map (eqToHom (congrArg op hU))
      ((((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _) d).val.app
        (op U) z) := by
  let P := Scheme.Modules.pullback q
  let Q := Scheme.Modules.pushforward q
  let adj := Scheme.Modules.pullbackPushforwardAdjunction q
  let t := eqToHom (congrArg op hU)
  have hn := ConcreteCategory.congr_hom (d.mapPresheaf.naturality t)
    ((adj.unit.app M).val.app (op U) z)
  have hd : adj.unit.app M ≫ Q.map d = (adj.homEquiv _ _) d := by
    rw [Adjunction.homEquiv_unit]
  have hdz := congrArg (fun m => m.val.app (op U) z) hd
  change d.val.app (op ⊤)
    ((P.obj M).val.map t ((adj.unit.app M).val.app (op U) z)) = _
  exact hn.trans (congrArg (fun w => N.val.map t w) hdz)

lemma actualFieldPointFactor_preimage_image_top
    {L : Type u} [Field L] {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (j : Spec (.of L) ⟶ Y)
    (q : Spec (.of L) ⟶ X) (hfac : j ≫ f = q) :
    q ⁻¹ᵁ (f ''ᵁ (⊤ : Y.Opens)) = ⊤ := by
  rw [← hfac, Scheme.Hom.comp_preimage, f.preimage_image_eq]
  rfl

end PfaffianDescent
