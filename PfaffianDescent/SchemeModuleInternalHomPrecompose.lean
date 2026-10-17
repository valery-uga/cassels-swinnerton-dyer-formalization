import PfaffianDescent.SchemeModuleInternalHomTensorCurry

/-! Native internalHom precomposition and literal tensor-curry naturality.
SOURCE ONLY / UNVERIFIED. No duality or compatibility premise. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
universe u
variable {X : Scheme.{u}}

private instance nativeSectionModule (A : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (A.val.obj (op U)) := (A.val.obj (op U)).isModule
private instance nativeOpSectionModule (A : X.Modules) (U : X.Opensᵒᵖ) :
    Module Γ(X, U.unop) (A.val.obj U) := (A.val.obj U).isModule

/-- Literal precomposition of actual over-site module morphisms. -/
def precomposeSection {M M' : X.Modules} (g : M' ⟶ M) (N : X.Modules)
    (U : X.Opens) (a : (sheaf M N).val.obj (op U)) :
    (sheaf M' N).val.obj (op U) :=
  (sectionsEquivOver M' N U).symm (g.over U ≫ sectionsEquivOver M N U a)

/-- The actual smaller-open precomposition value. -/
theorem precomposeSection_apply {M M' : X.Modules} (g : M' ⟶ M) (N : X.Modules)
    (U : X.Opens) (a : (sheaf M N).val.obj (op U)) (V : Over U)
    (m : M'.val.obj (op V.left)) :
    (precomposeSection g N U a).1.app (op V) m =
      a.1.app (op V) (g.val.app (op V.left) m) := rfl

/-- Genuine native internalHom map attached to the SAME original g. -/
def precompose {M M' : X.Modules} (g : M' ⟶ M) (N : X.Modules) :
    sheaf M N ⟶ sheaf M' N where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := precomposeSection g N U.unop
          map_add' := by
            intro a b
            apply Subtype.ext
            apply NatTrans.ext
            funext V
            apply AddCommGrpCat.hom_ext
            ext m
            rfl
          map_smul' := by
            intro r a
            apply Subtype.ext
            apply NatTrans.ext
            funext V
            apply AddCommGrpCat.hom_ext
            ext m
            rfl }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        apply Subtype.ext
        apply NatTrans.ext
        funext W
        apply AddCommGrpCat.hom_ext
        ext m
        rfl }

/-- Exact original raw adjunction naturality in the first tensor factor. -/
theorem tensorPairingRaw_map_left {M M' : X.Modules} (g : M' ⟶ M)
    (B N : X.Modules) (p : schemeModuleTensor M B ⟶ N) :
    tensorPairingRaw M' B N (schemeModuleTensorMap g (𝟙 B) ≫ p) =
      PresheafOfModules.Monoidal.tensorHom g.val (𝟙 B.val) ≫ tensorPairingRaw M B N p := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  exact A.homEquiv_naturality_left
    (PresheafOfModules.Monoidal.tensorHom g.val (𝟙 B.val)) p

/-- Exact original raw adjunction naturality in the second tensor factor. -/
theorem tensorPairingRaw_map_right (M : X.Modules) {B B' : X.Modules}
    (g : B' ⟶ B) (N : X.Modules) (p : schemeModuleTensor M B ⟶ N) :
    tensorPairingRaw M B' N (schemeModuleTensorMap (𝟙 M) g ≫ p) =
      PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) g.val ≫ tensorPairingRaw M B N p := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  exact A.homEquiv_naturality_left
    (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) g.val) p

/-- Curry of first-factor precomposition is the literal internalHom map. -/
theorem tensorCurry_precompose {M M' : X.Modules} (g : M' ⟶ M)
    (B N : X.Modules) (p : schemeModuleTensor M B ⟶ N) :
    tensorCurry M' B N (schemeModuleTensorMap g (𝟙 B) ≫ p) =
      tensorCurry M B N p ≫ precompose g N := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  ext m
  have h := ConcreteCategory.congr_hom
    (congrArg (fun a : PresheafOfModules.Monoidal.tensorObj M'.val B.val ⟶ N.val =>
      a.app (op V.unop.left)) (tensorPairingRaw_map_left g B N p))
    (m ⊗ₜ[Γ(X, V.unop.left)] (show B.val.obj (op V.unop.left) from B.val.map V.unop.hom.op b))
  change (tensorPairingRaw M' B N (schemeModuleTensorMap g (𝟙 B) ≫ p)).app
      (op V.unop.left) (m ⊗ₜ[Γ(X, V.unop.left)] (show B.val.obj (op V.unop.left) from B.val.map V.unop.hom.op b)) =
    (tensorPairingRaw M B N p).app (op V.unop.left)
      (g.val.app (op V.unop.left) m ⊗ₜ[Γ(X, V.unop.left)] (show B.val.obj (op V.unop.left) from B.val.map V.unop.hom.op b)) at h
  exact h

/-- Curry in the second factor is the SAME original module-map composition. -/
theorem tensorCurry_map_right (M : X.Modules) {B B' : X.Modules}
    (g : B' ⟶ B) (N : X.Modules) (p : schemeModuleTensor M B ⟶ N) :
    tensorCurry M B' N (schemeModuleTensorMap (𝟙 M) g ≫ p) =
      g ≫ tensorCurry M B N p := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  ext m
  have h := ConcreteCategory.congr_hom
    (congrArg (fun a : PresheafOfModules.Monoidal.tensorObj M.val B'.val ⟶ N.val =>
      a.app (op V.unop.left)) (tensorPairingRaw_map_right M g N p))
    (m ⊗ₜ[Γ(X, V.unop.left)] (show B'.val.obj (op V.unop.left) from B'.val.map V.unop.hom.op b))
  change (tensorPairingRaw M B' N (schemeModuleTensorMap (𝟙 M) g ≫ p)).app
      (op V.unop.left) (m ⊗ₜ[Γ(X, V.unop.left)] (show B'.val.obj (op V.unop.left) from B'.val.map V.unop.hom.op b)) =
    (tensorPairingRaw M B N p).app (op V.unop.left)
      (m ⊗ₜ[Γ(X, V.unop.left)] g.val.app (op V.unop.left)
        ((show B'.val.obj (op V.unop.left) from B'.val.map V.unop.hom.op b))) at h
  have hg : g.val.app (op V.unop.left) ((show B'.val.obj (op V.unop.left) from B'.val.map V.unop.hom.op b)) =
      (show B.val.obj (op V.unop.left) from B.val.map V.unop.hom.op (g.val.app U b)) :=
    PresheafOfModules.naturality_apply g.val V.unop.hom.op b
  exact h.trans (congrArg (fun c : B.val.obj (op V.unop.left) => ((tensorPairingRaw M B N p).app
    (op V.unop.left)).hom (m ⊗ₜ[Γ(X, V.unop.left)] c)) hg)

end PfaffianDescent.SchemeModuleInternalHom
end
