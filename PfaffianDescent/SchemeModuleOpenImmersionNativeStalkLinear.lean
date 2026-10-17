import PfaffianDescent.SchemeModuleRestrictStalkLinear

/-! Native module actions under an ACTUAL open-immersion stalk comparison.
SOURCE ONLY / UNVERIFIED. Root alone checks Lean. No scalar action is transported.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual scalar germ square on an open immersion's image neighborhood. -/
theorem openImmersion_stalkMap_image_germ
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) (V : X.Opens) (hx : x ∈ V) (a : Γ(Y, f ''ᵁ V)) :
    f.stalkMap x (Y.presheaf.germ (f ''ᵁ V) (f x) (by simpa using hx) a) =
      X.presheaf.germ V x hx ((f.appIso V).hom a) := by
  rw [f.germ_stalkMap_apply]
  have hres := X.presheaf.germ_res_apply
    (eqToHom (f.preimage_image_eq V).symm) x hx (f.app (f ''ᵁ V) a)
  simpa only [Scheme.Hom.appIso_hom, ConcreteCategory.comp_apply] using hres.symm

/-- The inverse actual restriction stalk map is semilinear for the ACTUAL
stalk ring homomorphism, with both independently native module actions. -/
theorem openImmersion_moduleRestrictStalk_inv_smul
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) (M : Y.Modules)
    (a : Y.presheaf.stalk (f x)) (y : M.presheaf.stalk (f x)) :
    letI := schemeModuleStalkModule M (f x)
    letI := schemeModuleStalkModule (M.restrict f) x
    (Scheme.Modules.restrictStalkNatIso f x).inv.app M (a • y) =
      f.stalkMap x a •
        (show (M.restrict f).presheaf.stalk x from
          (Scheme.Modules.restrictStalkNatIso f x).inv.app M y) := by
  dsimp only
  letI := schemeModuleStalkModule M (f x)
  letI := schemeModuleStalkModule (M.restrict f) x
  have hxRange : f x ∈ f.opensRange := ⟨x, rfl⟩
  obtain ⟨V, hVR, hxV, aV, rfl⟩ := Y.presheaf.exists_le_germ_eq a hxRange
  obtain ⟨W, hWV, hxW, m, rfl⟩ := M.presheaf.exists_le_germ_eq y hxV
  erw [← Y.presheaf.germ_res_apply (homOfLE hWV) _ hxW aV]
  erw [← PresheafOfModules.germ_smul M.val (f x) W hxW]
  let Wf : X.Opens := f ⁻¹ᵁ W
  have hWR : W ≤ f.opensRange := hWV.trans hVR
  have hImage : f ''ᵁ Wf = W :=
    (f.image_preimage_eq_opensRange_inf W).trans (inf_eq_right.mpr hWR)
  have hxWf : x ∈ Wf := hxW
  let j : f ''ᵁ Wf ⟶ W := eqToHom hImage
  let aW : Γ(Y, W) := Y.presheaf.map (homOfLE hWV).op aV
  let a' : Γ(Y, f ''ᵁ Wf) := Y.presheaf.map j.op aW
  let m' : Γ(M, f ''ᵁ Wf) := M.presheaf.map j.op m
  have hga : Y.presheaf.germ (f ''ᵁ Wf) (f x)
      (by simpa [hImage] using hxW) a' = Y.presheaf.germ W (f x) hxW aW :=
    Y.presheaf.germ_res_apply j (f x) (by simpa [hImage] using hxW) aW
  have hgm : M.presheaf.germ (f ''ᵁ Wf) (f x)
      (by simpa [hImage] using hxW) m' = M.presheaf.germ W (f x) hxW m :=
    M.presheaf.germ_res_apply j (f x) (by simpa [hImage] using hxW) m
  have hgam : M.presheaf.germ (f ''ᵁ Wf) (f x)
      (by simpa [hImage] using hxW) (a' • m') =
        M.presheaf.germ W (f x) hxW (aW • m) := by
    erw [PresheafOfModules.germ_smul M.val, hga, hgm,
      PresheafOfModules.germ_smul M.val]
    rfl
  have hn := Scheme.Modules.germ_restrictStalkNatIso_inv_app f x M
    (U := Wf) hxWf
  have hn_apply (v : Γ(M, f ''ᵁ Wf)) := congrArg (fun q ↦ q.hom v) hn
  change (Scheme.Modules.restrictStalkNatIso f x).inv.app M
      (M.presheaf.germ W (f x) hxW (aW • m)) =
    f.stalkMap x (Y.presheaf.germ W (f x) hxW aW) •
      (show (M.restrict f).presheaf.stalk x from
        (Scheme.Modules.restrictStalkNatIso f x).inv.app M
          (M.presheaf.germ W (f x) hxW m))
  rw [← hgam, ← hga, ← hgm]
  erw [hn_apply, hn_apply]
  rw [openImmersion_stalkMap_image_germ f x Wf hxWf a']
  have hsec := Scheme.Modules.smul_restrictAppIso_inv_apply f M Wf a' m'
  have hsec_germ := congrArg
    (fun v ↦ (M.restrict f).presheaf.germ Wf x hxWf v) hsec
  erw [hsec_germ]
  exact PresheafOfModules.germ_smul (M.restrict f).val x Wf hxWf _ _

/-- The forward actual restriction stalk map has the same semilinearity. -/
theorem openImmersion_moduleRestrictStalk_hom_smul
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) (M : Y.Modules) (a : Y.presheaf.stalk (f x))
    (y : (M.restrict f).presheaf.stalk x) :
    letI := schemeModuleStalkModule M (f x)
    letI := schemeModuleStalkModule (M.restrict f) x
    (Scheme.Modules.restrictStalkNatIso f x).hom.app M (f.stalkMap x a • y) =
      a • (show M.presheaf.stalk (f x) from
        (Scheme.Modules.restrictStalkNatIso f x).hom.app M y) := by
  dsimp only
  letI := schemeModuleStalkModule M (f x)
  letI := schemeModuleStalkModule (M.restrict f) x
  let e : (M.restrict f).presheaf.stalk x ≅ M.presheaf.stalk (f x) :=
    (Scheme.Modules.restrictStalkNatIso f x).app M
  apply (ConcreteCategory.bijective_of_isIso e.inv).injective
  have h := openImmersion_moduleRestrictStalk_inv_smul f x M a (e.hom y)
  change e.inv (e.hom (f.stalkMap x a • y)) = e.inv (a • e.hom y)
  change e.inv (a • e.hom y) = f.stalkMap x a • e.inv (e.hom y) at h
  simpa only [Iso.hom_inv_id_apply] using h.symm

end PfaffianDescent.Coray
