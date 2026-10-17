import PfaffianDescent.SchemeModuleInternalHomEvaluation

/-! Native currying of an actual sheafified tensor pairing. Every section
is an original O-linear over-site morphism. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
universe u
variable {X : Scheme.{u}} (M B N : X.Modules)

/-- Expose exactly the original section-module action to instance search. -/
private instance nativeSectionModule (A : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (A.val.obj (op U)) :=
  (A.val.obj (op U)).isModule

/-- The identical native action, for an already opposite open object. -/
private instance nativeOpSectionModule (A : X.Modules) (U : X.Opensᵒᵖ) :
    Module Γ(X, U.unop) (A.val.obj U) :=
  (A.val.obj U).isModule

/-- The raw pairing is the actual sheafification adjunction image. -/
def tensorPairingRaw (p : schemeModuleTensor M B ⟶ N) :
    PresheafOfModules.Monoidal.tensorObj M.val B.val ⟶ N.val :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _) p

/-- Actual restriction of the same raw pairing on pure tensors. -/
theorem tensorPairingRaw_restrict (p : schemeModuleTensor M B ⟶ N)
    {U V : X.Opens} (f : V ⟶ U)
    (m : M.val.obj (op U)) (b : B.val.obj (op U)) :
    (tensorPairingRaw M B N p).app (op V)
        (M.val.map f.op m ⊗ₜ[Γ(X, V)] B.val.map f.op b) =
      N.val.map f.op ((tensorPairingRaw M B N p).app (op U)
        (m ⊗ₜ[Γ(X, U)] b)) := by
  have h := ConcreteCategory.congr_hom
    ((tensorPairingRaw M B N p).naturality f.op) (m ⊗ₜ[Γ(X, U)] b)
  change ((tensorPairingRaw M B N p).app (op V)).hom
      (((PresheafOfModules.Monoidal.tensorObj M.val B.val).map f.op).hom
        (m ⊗ₜ[Γ(X, U)] b)) =
    (N.val.map f.op).hom (((tensorPairingRaw M B N p).app (op U)).hom
      (m ⊗ₜ[Γ(X, U)] b)) at h
  have ht := PresheafOfModules.Monoidal.tensorObj_map_tmul
    (R := X.presheaf) (M₁ := M.val) (M₂ := B.val) f.op m b
  exact (congrArg ((tensorPairingRaw M B N p).app (op V)).hom ht).symm.trans h

/-- An original section of B gives the actual additive over-site map. -/
def tensorCurryRawSection (p : schemeModuleTensor M B ⟶ N)
    (U : X.Opens) (b : B.val.obj (op U)) : Raw M N U where
  app V := AddCommGrpCat.ofHom
    { toFun := fun m => (tensorPairingRaw M B N p).app (op V.unop.left)
        (m ⊗ₜ[Γ(X, V.unop.left)] B.val.map V.unop.hom.op b)
      map_zero' := by
        exact ((TensorProduct.curry
          ((tensorPairingRaw M B N p).app (op V.unop.left)).hom).flip
          (B.val.map V.unop.hom.op b)).map_zero
      map_add' := by
        intro m n
        exact ((TensorProduct.curry
          ((tensorPairingRaw M B N p).app (op V.unop.left)).hom).flip
          (B.val.map V.unop.hom.op b)).map_add m n }
  naturality := by
    intro V W f
    apply AddCommGrpCat.hom_ext
    ext m
    change (tensorPairingRaw M B N p).app (op W.unop.left)
        (M.val.map f.unop.left.op m ⊗ₜ[Γ(X, W.unop.left)]
          B.val.map W.unop.hom.op b) =
      N.val.map f.unop.left.op
        ((tensorPairingRaw M B N p).app (op V.unop.left)
          (m ⊗ₜ[Γ(X, V.unop.left)] B.val.map V.unop.hom.op b))
    have hb : B.val.map f.unop.left.op (B.val.map V.unop.hom.op b) =
        B.val.map W.unop.hom.op b := by
      rw [← B.val.map_comp_apply]
      rw [← op_comp, Over.w f.unop]
    rw [← hb]
    exact tensorPairingRaw_restrict M B N p f.unop.left m _

/-- The actual curried section is linear over every smaller original ring. -/
def tensorCurrySection (p : schemeModuleTensor M B ⟶ N)
    (U : X.Opens) (b : B.val.obj (op U)) : (sheaf M N).val.obj (op U) :=
  ⟨tensorCurryRawSection M B N p U b, by
    intro V r m
    change (tensorPairingRaw M B N p).app (op V.left)
        ((r • m) ⊗ₜ[Γ(X, V.left)] B.val.map V.hom.op b) =
      r • (tensorPairingRaw M B N p).app (op V.left)
        (m ⊗ₜ[Γ(X, V.left)] B.val.map V.hom.op b)
    exact ((TensorProduct.curry
      ((tensorPairingRaw M B N p).app (op V.left)).hom).flip
      (B.val.map V.hom.op b)).map_smul r m⟩

/-- Literal smaller-open component of the actual curried section. -/
theorem tensorCurrySection_apply (p : schemeModuleTensor M B ⟶ N)
    (U : X.Opens) (b : B.val.obj (op U)) (V : Over U)
    (m : M.val.obj (op V.left)) :
    (tensorCurrySection M B N p U b).1.app (op V) m =
      (tensorPairingRaw M B N p).app (op V.left)
        (m ⊗ₜ[Γ(X, V.left)] B.val.map V.hom.op b) := rfl

/-- Currying retains the actual Hom restriction maps. -/
theorem tensorCurrySection_restrict (p : schemeModuleTensor M B ⟶ N)
    {U V : X.Opens} (f : V ⟶ U) (b : B.val.obj (op U)) :
    (sheaf M N).val.map f.op (tensorCurrySection M B N p U b) =
      tensorCurrySection M B N p V (B.val.map f.op b) := by
  apply Subtype.ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  ext m
  change (tensorPairingRaw M B N p).app (op W.unop.left)
      (m ⊗ₜ[Γ(X, W.unop.left)] B.val.map (W.unop.hom ≫ f).op b) =
    (tensorPairingRaw M B N p).app (op W.unop.left)
      (m ⊗ₜ[Γ(X, W.unop.left)] B.val.map W.unop.hom.op (B.val.map f.op b))
  rw [op_comp, B.val.map_comp_apply]

/-- Native tensor-Hom curry, with independently original scalar actions. -/
def tensorCurry (p : schemeModuleTensor M B ⟶ N) : B ⟶ sheaf M N where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := tensorCurrySection M B N p U.unop
          map_add' := by
            intro b c
            apply Subtype.ext
            apply NatTrans.ext
            funext V
            apply AddCommGrpCat.hom_ext
            ext m
            change (tensorPairingRaw M B N p).app (op V.unop.left)
                (m ⊗ₜ[Γ(X, V.unop.left)] B.val.map V.unop.hom.op (b + c)) = _
            let q := TensorProduct.curry
              ((tensorPairingRaw M B N p).app (op V.unop.left)).hom
            exact (congrArg (q m) ((B.val.map V.unop.hom.op).hom.map_add b c)).trans
              ((q m).map_add (B.val.map V.unop.hom.op b) (B.val.map V.unop.hom.op c))
          map_smul' := by
            intro r b
            apply Subtype.ext
            apply NatTrans.ext
            funext V
            apply AddCommGrpCat.hom_ext
            ext m
            change (tensorPairingRaw M B N p).app (op V.unop.left)
                (m ⊗ₜ[Γ(X, V.unop.left)] B.val.map V.unop.hom.op (r • b)) =
              X.presheaf.map V.unop.hom.op r •
                (tensorPairingRaw M B N p).app (op V.unop.left)
                  (m ⊗ₜ[Γ(X, V.unop.left)] B.val.map V.unop.hom.op b)
            let q := TensorProduct.curry
              ((tensorPairingRaw M B N p).app (op V.unop.left)).hom
            exact (congrArg (q m) (B.val.map_smul V.unop.hom.op r b)).trans
              ((q m).map_smul (X.presheaf.map V.unop.hom.op r)
                (B.val.map V.unop.hom.op b)) }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        exact (tensorCurrySection_restrict M B N p f.unop b).symm }

/-- The SAME global evaluation recovers the original pairing. -/
theorem tensorCurry_evaluation (p : schemeModuleTensor M B ⟶ N) :
    schemeModuleTensorMap (𝟙 M) (tensorCurry M B N p) ≫ evaluation M N = p := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let t : PresheafOfModules.Monoidal.tensorObj M.val B.val ⟶
      PresheafOfModules.Monoidal.tensorObj M.val (sheaf M N).val :=
    PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) (tensorCurry M B N p).val
  have hnat : (A.homEquiv _ _)
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map t ≫ evaluation M N) =
      t ≫ (A.homEquiv _ _) (evaluation M N) :=
    A.homEquiv_naturality_left t (evaluation M N)
  have hev : (A.homEquiv _ _) (evaluation M N) = evaluationPresheaf M N :=
    evaluation_raw M N
  have hraw : t ≫ evaluationPresheaf M N = tensorPairingRaw M B N p := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m b
    change (tensorPairingRaw M B N p).app U
        (m ⊗ₜ[Γ(X, U.unop)] B.val.map (𝟙 U.unop).op b) =
      (tensorPairingRaw M B N p).app U (m ⊗ₜ[Γ(X, U.unop)] b)
    have hb : B.val.map (𝟙 U.unop).op b = b := by
      change B.presheaf.map (𝟙 U) b = b
      exact ConcreteCategory.congr_hom (B.presheaf.map_id U) b
    exact congrArg (fun c => ((tensorPairingRaw M B N p).app U).hom
      (m ⊗ₜ[Γ(X, U.unop)] c)) hb
  apply (A.homEquiv _ _).injective
  exact hnat.trans ((congrArg (fun a => t ≫ a) hev).trans hraw)

end PfaffianDescent.SchemeModuleInternalHom
end
