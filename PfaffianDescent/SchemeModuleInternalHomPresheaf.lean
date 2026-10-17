import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! Actual local O-linear Hom presheaf. Scalars are ORIGINAL sections of
the scheme structure sheaf, acting by their actual restrictions on target
values. No scalar action is transported through a comparison. The next
module proves the genuine sheaf condition. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (M N : X.Modules)

/-- The over-site component carries the SAME original section module.
This exposes its actual carrier to instance search through the whiskering. -/
private instance originalOverSectionModule (A : X.Modules) (U : X.Opens)
    (V : (Over U)ᵒᵖ) :
    Module Γ(X, V.unop.left) (((Over.forget U).op ⋙ A.presheaf).obj V) :=
  inferInstanceAs (Module Γ(X, V.unop.left) Γ(A, V.unop.left))

/-- The same original section module with the explicit op-wrapper
needed when the test open is given as an object of Over U. -/
private instance originalOverOpSectionModule (A : X.Modules) (U : X.Opens)
    (V : Over U) :
    Module Γ(X, V.left) (((Over.forget U).op ⋙ A.presheaf).obj (op V)) :=
  inferInstanceAs (Module Γ(X, V.left) Γ(A, V.left))

/-- Ordinary additive natural transformations on the ACTUAL over-site. -/
abbrev Raw (U : X.Opens) :=
  (CategoryTheory.presheafHom M.presheaf N.presheaf).obj (op U)

/-- The SAME natural-transformation group, explicitly exposing its
actual functor-category Hom type instead of an opaque presheaf value. -/
private instance rawAddCommGroup (U : X.Opens) : AddCommGroup (Raw M N U) :=
  inferInstanceAs (AddCommGroup
    (((Over.forget U).op ⋙ M.presheaf) ⟶ ((Over.forget U).op ⋙ N.presheaf)))

/-- Actual restriction composition, stated by VALUES to avoid replacing
the original section ring maps by abstract scalar transports. -/
theorem restriction_comp {U V W : X.Opens} (f : V ⟶ U) (g : W ⟶ V)
    (r : Γ(X, U)) :
    X.presheaf.map g.op (X.presheaf.map f.op r) =
      X.presheaf.map (g ≫ f).op r := by
  exact (ConcreteCategory.congr_hom (X.presheaf.map_comp f.op g.op) r).symm

/-- Scalar multiplication on local additive Hom: actual restrictions of
r act on the original target module, on EVERY smaller open. -/
def rawSmul (U : X.Opens) (r : Γ(X, U)) (a : Raw M N U) : Raw M N U where
  app V := AddCommGrpCat.ofHom
    { toFun := fun m => X.presheaf.map V.unop.hom.op r • a.app V m
      map_zero' := by rw [map_zero, smul_zero]
      map_add' := by intro m n; rw [map_add, smul_add] }
  naturality := by
    intro V W f
    apply AddCommGrpCat.hom_ext
    ext m
    change X.presheaf.map W.unop.hom.op r • a.app W
        (M.val.map f.unop.left.op m) =
      N.val.map f.unop.left.op
        (X.presheaf.map V.unop.hom.op r • a.app V m)
    rw [N.val.map_smul]
    have hcoef : X.presheaf.map f.unop.left.op
        (X.presheaf.map V.unop.hom.op r) = X.presheaf.map W.unop.hom.op r := by
      rw [restriction_comp, Over.w f.unop]
    change X.presheaf.map W.unop.hom.op r • a.app W
        (M.val.map f.unop.left.op m) =
      X.presheaf.map f.unop.left.op (X.presheaf.map V.unop.hom.op r) •
        N.val.map f.unop.left.op (a.app V m)
    rw [hcoef]
    exact congrArg (X.presheaf.map W.unop.hom.op r • ·)
      (ConcreteCategory.congr_hom (a.naturality f) m)

/-- Literal value formula for the independent original scalar action. -/
theorem rawSmul_apply (U : X.Opens) (r : Γ(X, U)) (a : Raw M N U)
    (V : Over U) (m : M.val.obj (op V.left)) :
    (rawSmul M N U r a).app (op V) m =
      X.presheaf.map V.hom.op r • a.app (op V) m := rfl

/-- The original affine/open coefficient ring acts on local additive Hom.
Module laws follow pointwise from the ORIGINAL restriction ring hom. -/
instance rawModule (U : X.Opens) : Module (Γ(X, U)) (Raw M N U) where
  smul := rawSmul M N U
  one_smul a := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext m
    change X.presheaf.map V.unop.hom.op 1 • a.app V m = a.app V m
    rw [map_one, one_smul]
  mul_smul r s a := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext m
    change X.presheaf.map V.unop.hom.op (r * s) • a.app V m =
      X.presheaf.map V.unop.hom.op r • (X.presheaf.map V.unop.hom.op s • a.app V m)
    rw [map_mul, mul_smul]
  smul_zero r := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext m
    change X.presheaf.map V.unop.hom.op r • (0 : N.val.obj (op V.unop.left)) = 0
    exact smul_zero _
  smul_add r a b := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext m
    change X.presheaf.map V.unop.hom.op r • (a.app V m + b.app V m) =
      X.presheaf.map V.unop.hom.op r • a.app V m +
        X.presheaf.map V.unop.hom.op r • b.app V m
    exact smul_add _ _ _
  add_smul r s a := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext m
    change X.presheaf.map V.unop.hom.op (r + s) • a.app V m =
      X.presheaf.map V.unop.hom.op r • a.app V m +
        X.presheaf.map V.unop.hom.op s • a.app V m
    rw [map_add, add_smul]
  zero_smul a := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext m
    change X.presheaf.map V.unop.hom.op 0 • a.app V m = 0
    rw [map_zero, zero_smul]

/-- The genuine local O-linear maps form a submodule: linearity is required
over EVERY actual smaller section ring, not just over Γ(X,U). -/
def linearSubmodule (U : X.Opens) : Submodule (Γ(X, U)) (Raw M N U) where
  carrier := {a | ∀ (V : Over U) (r : Γ(X, V.left)) (m : M.val.obj (op V.left)),
    a.app (op V) (r • m) = r • a.app (op V) m}
  zero_mem' := by intro V r m; change 0 = r • (0 : N.val.obj (op V.left)); simp
  add_mem' := by
    intro a b ha hb V r m
    change a.app (op V) (r • m) + b.app (op V) (r • m) =
      r • (a.app (op V) m + b.app (op V) m)
    rw [ha, hb, smul_add]
  smul_mem' := by
    intro c a ha V r m
    change X.presheaf.map V.hom.op c • a.app (op V) (r • m) =
      r • (X.presheaf.map V.hom.op c • a.app (op V) m)
    rw [ha]
    exact @smul_comm Γ(X, V.left) Γ(X, V.left) Γ(N, V.left) _ _
      (smulCommClass_self Γ(X, V.left) Γ(N, V.left))
      (X.presheaf.map V.hom.op c) r
      (show Γ(N, V.left) from a.app (op V) m)

/-- O-linearity restricts along the ACTUAL Over.map functor. -/
def linearSubfunctor : Subfunctor (CategoryTheory.presheafHom M.presheaf N.presheaf) where
  obj U := linearSubmodule M N U.unop
  map := by
    intro U V f a ha W r m
    exact ha ((Over.map f.unop).obj W) r m

/-- Actual underlying additive presheaf of local O-linear Hom. Its maps
are the genuine restriction of natural transformations, with linearity
preserved internally. -/
def additivePresheaf : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (linearSubmodule M N U.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := fun a => ⟨(CategoryTheory.presheafHom M.presheaf N.presheaf).map f a.1,
        (linearSubfunctor M N).map f a.2⟩
      map_zero' := by apply Subtype.ext; rfl
      map_add' := by intro a b; apply Subtype.ext; rfl }
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((CategoryTheory.presheafHom M.presheaf N.presheaf).map_id U) a.1
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((CategoryTheory.presheafHom M.presheaf N.presheaf).map_comp f g) a.1

/-- The actual additive-presheaf component carries the SAME native
submodule action of the original open section ring. -/
private instance additivePresheafOriginalModule (U : X.Opensᵒᵖ) :
    Module Γ(X, U.unop) ((additivePresheaf M N).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (linearSubmodule M N U.unop))

/-- Expose the SAME native submodule action at the exact original
ring-category carrier required by ofPresheaf. -/
private instance additivePresheafRingModule (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((additivePresheaf M N).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (linearSubmodule M N U.unop))

/-- The original commutative-ring presheaf carrier carries the same
native submodule action used by restriction coefficients. -/
private instance additivePresheafCommRingModule (U : X.Opensᵒᵖ) :
    Module (X.presheaf.obj U) ((additivePresheaf M N).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (linearSubmodule M N U.unop))

/-- The actual Hom restriction is semilinear for the ORIGINAL structure
restriction ring map, proved on every component. -/
theorem additivePresheaf_map_smul {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (r : Γ(X, U.unop)) (a : (additivePresheaf M N).obj U) :
    (additivePresheaf M N).map f (r • a) =
      X.presheaf.map f r • (additivePresheaf M N).map f a := by
  apply Subtype.ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  ext m
  let s : Γ(N, W.unop.left) :=
    a.1.app (op ((Over.map f.unop).obj W.unop)) m
  change (X.presheaf.map (W.unop.hom ≫ f.unop).op r : Γ(X, W.unop.left)) • s =
    (X.presheaf.map W.unop.hom.op (X.presheaf.map f r) : Γ(X, W.unop.left)) • s
  exact congrArg (fun c : Γ(X, W.unop.left) => c • s)
    (restriction_comp (X := X) f.unop W.unop.hom r).symm

/-- The ACTUAL module presheaf of local O-linear Hom, with independent
original coefficients. The next module proves it is already a sheaf. -/
def modulePresheaf : PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (additivePresheaf M N)
    (fun _ _ f r a => additivePresheaf_map_smul M N f r a)

/-- The underlying additive presheaf really is the constructed Hom
presheaf. No comparison certificate or sheafification replacement. -/
theorem modulePresheaf_presheaf :
    (modulePresheaf M N).presheaf = additivePresheaf M N := rfl

end PfaffianDescent.SchemeModuleInternalHom
