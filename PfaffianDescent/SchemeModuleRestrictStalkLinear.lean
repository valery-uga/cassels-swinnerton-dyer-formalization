import PfaffianDescent.VoisinSheafStalk
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option linter.style.haveILetI false in
/-- Restriction of module stalks is semilinear for the open immersion stalk map. -/
theorem schemeModuleRestrictStalk_inv_smul
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M : X.Modules)
    (a : X.presheaf.stalk (U.ι x)) (y : M.presheaf.stalk (U.ι x)) :
    letI : Module (X.presheaf.stalk (U.ι x)) (M.presheaf.stalk (U.ι x)) :=
      schemeModuleStalkModule M _
    letI : Module ((U : Scheme).presheaf.stalk x)
        (((Scheme.Modules.restrictFunctor U.ι).obj M).presheaf.stalk x) :=
      schemeModuleStalkModule _ _
    let z : ((Scheme.Modules.restrictFunctor U.ι).obj M).presheaf.stalk x :=
      (Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M y
    (Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M (a • y) =
      U.ι.stalkMap x a • z := by
  dsimp
  letI : Module (X.presheaf.stalk (U.ι x)) (M.presheaf.stalk (U.ι x)) :=
    schemeModuleStalkModule M _
  letI : Module ((U : Scheme).presheaf.stalk x)
      (((Scheme.Modules.restrictFunctor U.ι).obj M).presheaf.stalk x) :=
    schemeModuleStalkModule _ _
  obtain ⟨V, hVU, hxV, r, rfl⟩ := X.presheaf.exists_le_germ_eq a (show U.ι x ∈ U from x.2)
  obtain ⟨W, hWV, hxW, m, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq M.presheaf y hxV
  erw [← X.presheaf.germ_res_apply (homOfLE hWV) _ hxW r]
  erw [← PresheafOfModules.germ_smul M.val (U.ι x) W hxW]
  let WU : (U : Scheme).Opens := (TopologicalSpace.Opens.map U.ι.base).obj W
  have hWU : W ≤ U := hWV.trans hVU
  have hImage : U.ι ''ᵁ WU = W := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, hWU hz⟩, hz, rfl⟩
  have hxWU : x ∈ WU := hxW
  let iW : U.ι ''ᵁ WU ⟶ W := eqToHom hImage
  let m' : Γ(M, U.ι ''ᵁ WU) := M.presheaf.map iW.op m
  let rW : X.presheaf.obj (Opposite.op W) := X.presheaf.map (homOfLE hWV).op r
  let r' : X.presheaf.obj (Opposite.op (U.ι ''ᵁ WU)) := X.presheaf.map iW.op rW
  have hgm : M.presheaf.germ (U.ι ''ᵁ WU) (U.ι x) (by simpa [hImage] using hxW) m' =
      M.presheaf.germ W (U.ι x) hxW m := by
    exact M.presheaf.germ_res_apply iW (U.ι x) (by simpa [hImage] using hxW) m
  have hgr : X.presheaf.germ (U.ι ''ᵁ WU) (U.ι x) (by simpa [hImage] using hxW) r' =
      X.presheaf.germ W (U.ι x) hxW rW := by
    exact X.presheaf.germ_res_apply iW (U.ι x) (by simpa [hImage] using hxW) rW
  have hgrm :
      M.presheaf.germ (U.ι ''ᵁ WU) (U.ι x) (by simpa [hImage] using hxW) (r' • m') =
        M.presheaf.germ W (U.ι x) hxW (rW • m) := by
    erw [PresheafOfModules.germ_smul M.val]
    erw [hgr, hgm]
    erw [PresheafOfModules.germ_smul M.val]
    rfl
  have hnM := Scheme.Modules.germ_restrictStalkNatIso_inv_app
    U.ι x M (U := WU) hxWU
  have hnM_apply (v : Γ(M, U.ι ''ᵁ WU)) :=
    congrArg (fun q ↦ q.hom v) hnM
  have hr := LocallyRingedSpace.stalkMap_germ_apply U.ι.toLRSHom
    W x hxW rW
  have hrsec :
      (show (U : Scheme).presheaf.obj (Opposite.op WU) from r') =
        U.ι.toLRSHom.c.app (Opposite.op W) rW := by
    rfl
  let z : ((Scheme.Modules.restrictFunctor U.ι).obj M).presheaf.stalk x :=
    (Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M
      (M.presheaf.germ W (U.ι x) hxW m)
  change (Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M
      (M.presheaf.germ W (U.ι x) hxW (rW • m)) =
    U.ι.stalkMap x (X.presheaf.germ W (U.ι x) hxW rW) • z
  dsimp only [z]
  rw [← hgrm, ← hgm]
  erw [hnM_apply]
  erw [hr]
  erw [hnM_apply]
  have hsmulsec :=
    Scheme.Modules.smul_restrictAppIso_inv_apply U.ι M WU r' m'
  have hscalarSec :
      (U.ι.appIso WU).hom r' = U.ι.toLRSHom.c.app (Opposite.op W) rW := by
    change ((X.ofRestrict U.isOpenEmbedding).appIso WU).hom r' = _
    have he := Scheme.ofRestrict_appIso X U.isOpenEmbedding WU
    have hh := congrArg (fun e ↦ e.hom r') he
    exact hh.trans hrsec
  have hgsmul := congrArg
    (fun v ↦ ((Scheme.Modules.restrictFunctor U.ι).obj M).presheaf.germ
      WU x hxWU v) hsmulsec
  erw [hgsmul, hscalarSec]
  exact PresheafOfModules.germ_smul
    ((Scheme.Modules.restrictFunctor U.ι).obj M).val x WU hxWU _ _

set_option linter.style.haveILetI false in
/-- The inverse direction of the restriction stalk comparison respects the
same transported local-ring action. -/
theorem schemeModuleRestrictStalk_hom_smul
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M : X.Modules)
    (a : X.presheaf.stalk (U.ι x))
    (y : ((Scheme.Modules.restrictFunctor U.ι).obj M).presheaf.stalk x) :
    letI : Module (X.presheaf.stalk (U.ι x)) (M.presheaf.stalk (U.ι x)) :=
      schemeModuleStalkModule M _
    letI : Module ((U : Scheme).presheaf.stalk x)
        (((Scheme.Modules.restrictFunctor U.ι).obj M).presheaf.stalk x) :=
      schemeModuleStalkModule _ _
    let z : M.presheaf.stalk (U.ι x) :=
      (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M y
    (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M
        (U.ι.stalkMap x a • y) = a • z := by
  dsimp
  letI := schemeModuleStalkModule M (U.ι x)
  letI := schemeModuleStalkModule ((Scheme.Modules.restrictFunctor U.ι).obj M) x
  let e : ((Scheme.Modules.restrictFunctor U.ι).obj M).presheaf.stalk x ≅
      M.presheaf.stalk (U.ι x) :=
    (Scheme.Modules.restrictStalkNatIso U.ι x).app M
  apply (ConcreteCategory.bijective_of_isIso e.inv).injective
  have h := schemeModuleRestrictStalk_inv_smul U x M a (e.hom y)
  change e.inv (e.hom (U.ι.stalkMap x a • y)) = e.inv (a • e.hom y)
  change e.inv (a • e.hom y) = U.ι.stalkMap x a • e.inv (e.hom y) at h
  simpa only [Iso.hom_inv_id_apply] using h.symm

set_option linter.style.haveILetI false in
/-- Trivializing a tensor factor near a point gives an ambient-local-ring
linear stalk isomorphism. -/
theorem schemeModuleTensorStalkIsoOfLocalTrivialization_smul
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M T : X.Modules)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (a : X.presheaf.stalk (U.ι x))
    (y : (schemeModuleTensor M T).presheaf.stalk (U.ι x)) :
    letI : Module (X.presheaf.stalk (U.ι x))
        ((schemeModuleTensor M T).presheaf.stalk (U.ι x)) :=
      schemeModuleStalkModule _ _
    letI : Module (X.presheaf.stalk (U.ι x)) (M.presheaf.stalk (U.ι x)) :=
      schemeModuleStalkModule _ _
    let t : (schemeModuleTensor M T).presheaf.stalk (U.ι x) →+
        M.presheaf.stalk (U.ι x) :=
      (schemeModuleTensorStalkIsoOfLocalTrivialization U x M T eT).hom.hom
    t (a • y) = a • t y := by
  dsimp
  letI := schemeModuleStalkModule (schemeModuleTensor M T) (U.ι x)
  letI := schemeModuleStalkModule M (U.ι x)
  let R := Scheme.Modules.restrictFunctor U.ι
  letI := schemeModuleStalkModule (R.obj (schemeModuleTensor M T)) x
  letI := schemeModuleStalkModule (R.obj M) x
  let e := schemeModuleTensorRestrictIsoOfLocalTrivialization U M T eT
  let z : (R.obj (schemeModuleTensor M T)).presheaf.stalk x :=
    (Scheme.Modules.restrictStalkNatIso U.ι x).inv.app (schemeModuleTensor M T) y
  have h₁ := schemeModuleRestrictStalk_inv_smul U x (schemeModuleTensor M T) a y
  have h₂ := (schemeModuleStalkLinearMap e.hom x).map_smul (U.ι.stalkMap x a) z
  have h₃ := schemeModuleRestrictStalk_hom_smul U x M a
    (schemeModuleStalkLinearMap e.hom x z)
  simp only [schemeModuleTensorStalkIsoOfLocalTrivialization,
    schemeModuleTensorStalkNatIsoOfLocalTrivialization]
  change (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M
      (schemeModuleStalkLinearMap e.hom x
        ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app (schemeModuleTensor M T)
          (a • y))) = _
  rw [h₁]
  change (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M
      (schemeModuleStalkLinearMap e.hom x (U.ι.stalkMap x a • z)) = _
  rw [h₂]
  exact h₃

set_option backward.isDefEq.respectTransparency false in
/-- The local tensor stalk comparison, now as an isomorphism of modules
over the ambient local ring. -/
noncomputable def schemeModuleTensorStalkModuleIsoOfLocalTrivialization
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M T : X.Modules)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj (schemeModuleTensor M T) ≅
      (schemeModuleStalkModuleFunctor X (U.ι x)).obj M := by
  letI := schemeModuleStalkModule (schemeModuleTensor M T) (U.ι x)
  letI := schemeModuleStalkModule M (U.ι x)
  let e := (schemeModuleTensorStalkIsoOfLocalTrivialization U x M T eT).addCommGroupIsoToAddEquiv
  let l : (schemeModuleTensor M T).presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      M.presheaf.stalk (U.ι x) :=
    { toAddEquiv := e
      map_smul' := fun a y ↦
        schemeModuleTensorStalkIsoOfLocalTrivialization_smul U x M T eT a y }
  exact LinearEquiv.toModuleIso l

end PfaffianDescent
