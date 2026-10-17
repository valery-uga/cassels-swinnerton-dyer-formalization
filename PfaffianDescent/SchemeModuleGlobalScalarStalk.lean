import PfaffianDescent.SchemeModuleRestrictStalkLinear
import PfaffianDescent.SchemeModuleCoverEqualizer

/-! # Global regular-function scalar actions on actual module stalks -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
/-- A morphism acting on every section by a global regular function acts on the
actual stalk by the germ of that function. -/
theorem schemeModuleStalkLinearMap_eq_germ_smul_of_app
    {X : Scheme.{u}} (M : X.Modules) (phi : M ⟶ M) (r : Γ(X, ⊤))
    (hphi : ∀ (U : X.Opens) (y : M.val.obj (op U)),
      phi.val.app (op U) y =
        X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • y)
    (x : X) (y : M.presheaf.stalk x) :
    letI := schemeModuleStalkModule M x
    schemeModuleStalkLinearMap phi x y =
      X.presheaf.germ ⊤ x trivial r • y := by
  letI := schemeModuleStalkModule M x
  obtain ⟨U, hx, m, rfl⟩ := M.presheaf.exists_germ_eq y
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
    (X := X.toTopCat) x).map
      ((PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map phi.val)
      (M.presheaf.germ U x hx m) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change M.presheaf.germ U x hx (phi.val.app (op U) m) = _
  erw [hphi]
  erw [PresheafOfModules.germ_smul M.val]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Any local-ring-linear coordinate transports the same actual scalar stalk
action to multiplication on the free rank-one target. -/
theorem schemeModuleStalk_conjugate_eq_germ_smul_of_app
    {X : Scheme.{u}} (M : X.Modules) (phi : M ⟶ M) (r : Γ(X, ⊤))
    (hphi : ∀ (U : X.Opens) (y : M.val.obj (op U)),
      phi.val.app (op U) y =
        X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • y)
    (x : X)
    (qN : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    qN.inv ≫ (schemeModuleStalkModuleFunctor X x).map phi ≫ qN.hom =
      X.presheaf.germ ⊤ x trivial r • 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change qN.hom
    (schemeModuleStalkLinearMap phi x (qN.inv a)) =
      X.presheaf.germ ⊤ x trivial r • a
  rw [schemeModuleStalkLinearMap_eq_germ_smul_of_app M phi r hphi,
    map_smul, qN.inv_hom_id_apply]

end PfaffianDescent
