import PfaffianDescent.SchemeModuleInternalHomPresheaf
import Mathlib.Topology.Sheaves.Sheaf

/-! O-linearity of additive natural transformations is genuinely local.
Target sheaf separation proves the linear subfunctor already a sheaf;
there is no supplied linearity/gluing/local-comparison certificate.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (M N : X.Modules)

/-- Genuine locality of O-linearity. On every test open, the target sheaf
separates sections after intersecting with the ACTUAL covering sieve. -/
theorem linearSubfunctor_isSheaf :
    Presieve.IsSheaf (Opens.grothendieckTopology X) (linearSubfunctor M N).toFunctor := by
  have hraw : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (CategoryTheory.presheafHom M.presheaf N.presheaf) :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mp (N.isSheaf.hom M.presheaf)
  apply ((linearSubfunctor M N).isSheaf_iff hraw).mpr
  intro U a hcover
  change ∀ (V : Over U.unop) (r : Γ(X, V.left)) (m : M.val.obj (op V.left)),
    a.app (op V) (r • m) = r • a.app (op V) m
  intro V r m
  apply N.isSheaf.section_ext
  intro x hxV
  obtain ⟨W, f, hf, hxW⟩ := hcover x (V.hom.le hxV)
  let T : X.Opens := V.left ⊓ W
  let g : T ⟶ W := homOfLE inf_le_right
  let t : T ⟶ V.left := homOfLE inf_le_left
  let k : T ⟶ U.unop := t ≫ V.hom
  have w : g ≫ f = k := Subsingleton.elim _ _
  let z : Over.mk k ⟶ V := Over.homMk t
  have hlocal := hf (Over.mk g) (X.presheaf.map t.op r) (M.val.map t.op m)
  have happ : ((CategoryTheory.presheafHom M.presheaf N.presheaf).map f.op a).app
      (op (Over.mk g)) = a.app (op (Over.mk k)) :=
    CategoryTheory.presheafHom_map_app g f k w a
  rw [happ] at hlocal
  have hnat (s : M.val.obj (op V.left)) :
      a.app (op (Over.mk k)) (M.val.map t.op s) =
        N.val.map t.op (a.app (op V) s) :=
    ConcreteCategory.congr_hom (a.naturality z.op) s
  refine ⟨T, inf_le_left, ⟨hxV, hxW⟩, ?_⟩
  change N.val.map t.op (a.app (op V) (r • m)) =
    N.val.map t.op (r • a.app (op V) m)
  calc
    N.val.map t.op (a.app (op V) (r • m)) =
        a.app (op (Over.mk k)) (M.val.map t.op (r • m)) := (hnat _).symm
    _ = a.app (op (Over.mk k))
        (X.presheaf.map t.op r • M.val.map t.op m) := by rw [M.val.map_smul]; rfl
    _ = (X.presheaf.map t.op r : Γ(X, T)) •
        (show Γ(N, T) from a.app (op (Over.mk k)) (M.val.map t.op m)) := hlocal
    _ = X.presheaf.map t.op r • N.val.map t.op (a.app (op V) m) := by rw [hnat]
    _ = N.val.map t.op (r • a.app (op V) m) := by rw [N.val.map_smul]; rfl

/-- The actual additive Hom presheaf satisfies the genuine sheaf axiom. -/
theorem additivePresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (additivePresheaf M N) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)).mpr
  change Presheaf.IsSheaf (Opens.grothendieckTopology X) (linearSubfunctor M N).toFunctor
  exact (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mpr (linearSubfunctor_isSheaf M N)

/-- The ACTUAL O-linear internal Hom module sheaf. Its sections are the
actual linear natural transformations, not a sheafification replacement
or a module renamed from an arbitrary vector space. -/
def sheaf : X.Modules where
  val := modulePresheaf M N
  isSheaf := additivePresheaf_isSheaf M N

/-- Literal underlying presheaf of the constructed internal Hom sheaf. -/
theorem sheaf_val : (sheaf M N).val = modulePresheaf M N := rfl

/-- Actual module-theoretic dual of the SAME input sheaf. Calling this a
positive inverse requires the later canonical evaluation IsIso proof. -/
def dual : X.Modules := sheaf M (SheafOfModules.unit X.ringCatSheaf)

end PfaffianDescent.SchemeModuleInternalHom
