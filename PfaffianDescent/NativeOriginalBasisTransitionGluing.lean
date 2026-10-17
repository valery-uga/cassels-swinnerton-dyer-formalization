import PfaffianDescent.SchemeModuleActualLocalIsoGluing

/-! SOURCE ONLY. Whole original basis-map transitions imply genuine local
Hom compatibility. All actual transition/basis data are internally derived
in the geometric caller; this is the bounded descent calculation. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open SchemeModuleInternalHom
universe u v u₁ u₂ v₁ v₂
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Whole framed scalar action determines the actual basis-transition map. -/
theorem nativeFramedOriginalBasisTransition
    {C : Type u₁} [Category.{v₁} C] {O M Q : C}
    (s₀ s₁ : O ⟶ M) [IsIso s₀] (e : M ≅ Q) (w : O ≅ Q) (q : Q ⟶ Q)
    (h₀ : s₀ ≫ e.hom = w.hom) (h₁ : s₁ ≫ e.hom = w.hom ≫ q) :
    s₁ ≫ inv s₀ = w.hom ≫ q ≫ w.inv := by
  have hi : inv s₀ = e.hom ≫ w.inv := by
    apply (IsIso.eq_inv_of_hom_inv_id (by
      rw [← Category.assoc, h₀, w.hom_inv_id])).symm
  rw [hi, ← Category.assoc, h₁]
  simp only [Category.assoc]

/-- An actual faithful chart comparison detects equality of WHOLE original
basis transitions when both native actions have the same actual scalar. -/
theorem nativeOriginalBasisTransitions_eq_of_chartActions
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ≌ D) {O M N : C} {Q : D}
    (s₀ s₁ : O ⟶ M) (t₀ t₁ : O ⟶ N) [IsIso s₀] [IsIso t₀]
    (eM : F.functor.obj M ≅ Q) (eN : F.functor.obj N ≅ Q)
    (w : F.functor.obj O ≅ Q) (q : Q ⟶ Q)
    (hs₀ : F.functor.map s₀ ≫ eM.hom = w.hom)
    (hs₁ : F.functor.map s₁ ≫ eM.hom = w.hom ≫ q)
    (ht₀ : F.functor.map t₀ ≫ eN.hom = w.hom)
    (ht₁ : F.functor.map t₁ ≫ eN.hom = w.hom ≫ q) :
    s₁ ≫ inv s₀ = t₁ ≫ inv t₀ := by
  apply F.functor.map_injective
  simp only [Functor.map_comp, Functor.map_inv]
  exact (nativeFramedOriginalBasisTransition (F.functor.map s₀)
    (F.functor.map s₁) eM w q hs₀ hs₁).trans
      (nativeFramedOriginalBasisTransition (F.functor.map t₀)
        (F.functor.map t₁) eN w q ht₀ ht₁).symm

/-- Equality of original basis transitions forces the original local
comparison map to carry the other original basis to its original target. -/
theorem nativeOriginalOtherBasis_comp_comparison
    {C : Type u₁} [Category.{v₁} C] {O M N : C}
    (s₀ s₁ : O ⟶ M) (t₀ t₁ : O ⟶ N) [IsIso s₀] [IsIso t₀]
    (h : s₁ ≫ inv s₀ = t₁ ≫ inv t₀) :
    s₁ ≫ inv s₀ ≫ t₀ = t₁ := by
  rw [← Category.assoc, h, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- WHOLE Hom sections agree on the original overlap if they carry the
same original basis to the same original target. The invertible common
basis is an ordinary original local geometry input to this generic lemma. -/
theorem nativeHomSections_compatible_of_commonOriginalBasis
    {X : Scheme.{u}} {M N : X.Modules} (U V : X.Opens)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ N)
    [IsIso (a.over V)]
    (f : M.over U ⟶ N.over U) (g : M.over V ⟶ N.over V)
    (hf : a.over U ≫ f = b.over U) (hg : a.over V ≫ g = b.over V) :
    (SchemeModuleInternalHom.sheaf M N).val.map
        (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op
        ((sectionsEquivOver M N U).symm f) =
      (SchemeModuleInternalHom.sheaf M N).val.map
        (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op
        ((sectionsEquivOver M N V).symm g) := by
  apply Subtype.ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  ext m
  let WU : Over U := Over.mk (W.unop.hom ≫ homOfLE (show U ⊓ V ≤ U from inf_le_left))
  let WV : Over V := Over.mk (W.unop.hom ≫ homOfLE (show U ⊓ V ≤ V from inf_le_right))
  change f.val.app (op WU) m = g.val.app (op WV) m
  let r : Γ(X, W.unop.left) := (inv (a.over V)).val.app (op WV) m
  have har : a.val.app (op W.unop.left) r = m := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun z : M.over V ⟶ M.over V => z.val.app (op WV))
        (IsIso.inv_hom_id (a.over V))) m
  have hfr : f.val.app (op WU) (a.val.app (op W.unop.left) r) =
      b.val.app (op W.unop.left) r :=
    ConcreteCategory.congr_hom
      (congrArg (fun z : (SheafOfModules.unit X.ringCatSheaf).over U ⟶ N.over U =>
        z.val.app (op WU)) hf) r
  have hgr : g.val.app (op WV) (a.val.app (op W.unop.left) r) =
      b.val.app (op W.unop.left) r :=
    ConcreteCategory.congr_hom
      (congrArg (fun z : (SheafOfModules.unit X.ringCatSheaf).over V ⟶ N.over V =>
        z.val.app (op WV)) hg) r
  exact (congrArg (fun z => f.val.app (op WU) z) har.symm).trans
    (hfr.trans (hgr.symm.trans (congrArg (fun z => g.val.app (op WV) z) har)))

end PfaffianDescent
