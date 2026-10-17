import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Whiskering
import PfaffianDescent.IdealSheafModule
import PfaffianDescent.SheafModulePushforwardExact

/-!
# Tensor products of module sheaves on a scheme

Mathlib provides the pointwise tensor product of presheaves of modules and
the associated-sheaf functor, but it does not currently package their
composition as a tensor product on `X.Modules`.  Voisin's Serre construction
needs the concrete object `I_Z ⊗ L`.  This file supplies that object and its
functorial maps, using the commutative structure sheaf of the scheme.

For a twist supplied with local trivializations on an open cover, the file
also proves the resulting twisted ideal sequence short exact by local
detection.  Constructing the particular projective twist `O_X(3)` and its
standard trivializing cover remains geometric work.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IdealSheafDataModule MonoidalCategory

universe u

/-- Tensoring a presheaf morphism on the right is additive in that
morphism.  This is the pointwise module-tensor calculation needed to make
the sheafified tensor functor additive. -/
lemma presheafTensorHom_add_left
    {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    {M M' N : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (f g : M ⟶ M') :
    PresheafOfModules.Monoidal.tensorHom (f + g) (𝟙 N) =
      PresheafOfModules.Monoidal.tensorHom f (𝟙 N) +
        PresheafOfModules.Monoidal.tensorHom g (𝟙 N) := by
  ext U x
  induction x using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul m n => simp [PresheafOfModules.Monoidal.tensorHom]; rfl
  | add x y hx hy => simp; rfl

/-- Tensoring a presheaf morphism on the left is additive in the morphism
on the right. -/
lemma presheafTensorHom_add_right
    {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    {M N N' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (f g : N ⟶ N') :
    PresheafOfModules.Monoidal.tensorHom (𝟙 M) (f + g) =
      PresheafOfModules.Monoidal.tensorHom (𝟙 M) f +
        PresheafOfModules.Monoidal.tensorHom (𝟙 M) g := by
  ext U x
  induction x using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul m n => simp [PresheafOfModules.Monoidal.tensorHom]; rfl
  | add x y hx hy => simp; rfl

/-- An endomorphism of the unit presheaf can act on either tensor factor.
This is the balancing relation over the commutative coefficient sheaf. -/
lemma presheafTensorHom_unit_central
    {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    (a : PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat) ⟶
      PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.Monoidal.tensorHom a (𝟙 _) =
      PresheafOfModules.Monoidal.tensorHom (𝟙 _) a := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  let S := R.obj U
  change S at m n
  let a' : S →ₗ[S] S := (a.app U).hom
  have ha (z : S) : a' z = z * a' 1 := by
    calc
      a' z = a' (z • (1 : S)) := by rw [smul_eq_mul, mul_one]
      _ = z • a' 1 := a'.map_smul z 1
      _ = z * a' 1 := by rw [smul_eq_mul]
  change a' m ⊗ₜ[S] n = m ⊗ₜ[S] a' n
  rw [ha m, ha n]
  have hbase := TensorProduct.smul_tmul (R := S) (a' 1) m n
  change ((a' 1) * m) ⊗ₜ[S] n = m ⊗ₜ[S] ((a' 1) * n) at hbase
  calc
    (m * a' 1) ⊗ₜ[S] n = ((a' 1) * m) ⊗ₜ[S] n := by rw [mul_comm m]
    _ = m ⊗ₜ[S] ((a' 1) * n) := hbase
    _ = m ⊗ₜ[S] (n * a' 1) := by rw [mul_comm (a' 1)]

/-- Sheafification along the identity of a ring sheaf is additive.  Its
right adjoint is the additive forgetful/restriction functor, so additivity
transfers across the adjunction. -/
noncomputable instance sheafificationIdentity_additive
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).Additive :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).left_adjoint_additive

section

variable {X : Scheme.{u}}

/-- The tensor product of two `𝒪_X`-module sheaves, obtained by sheafifying
the pointwise tensor product of their underlying module presheaves. -/
noncomputable def schemeModuleTensor (M N : X.Modules) : X.Modules := by
  let M' : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := M.val
  let N' : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := N.val
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) M' N')

/-- Restriction to the site over an open commutes with the concrete tensor
product of scheme modules.  The target is written on the over-site before
transporting along the equivalence with modules on the open subscheme. -/
noncomputable def schemeModuleTensorOverIso (U : X.Opens) (M N : X.Modules) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).obj (schemeModuleTensor M N) ≅
    SheafOfModules.commRingSheafTensor (SheafOfModules.commRingSheafOver X.sheaf U)
      ((SheafOfModules.overFunctor X.ringCatSheaf U).obj M)
      ((SheafOfModules.overFunctor X.ringCatSheaf U).obj N) :=
  SheafOfModules.overFunctor_commRingSheafTensorIso X.sheaf U M N

/-- The tensor product restricts to an actual module on the open subscheme.
This transports the over-site tensor comparison through Mathlib's equivalence
between modules on the over-site of `U` and modules on `U` itself. -/
noncomputable def schemeModuleTensorRestrictOverIso (U : X.Opens) (M N : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).obj (schemeModuleTensor M N) ≅
      (Scheme.Modules.overEquiv U).functor.obj
        (SheafOfModules.commRingSheafTensor
          (SheafOfModules.commRingSheafOver X.sheaf U)
          ((SheafOfModules.overFunctor X.ringCatSheaf U).obj M)
          ((SheafOfModules.overFunctor X.ringCatSheaf U).obj N)) :=
  (Scheme.Modules.overFunctorEquiv U).symm.app (schemeModuleTensor M N) ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso (schemeModuleTensorOverIso U M N)

/-- Tensoring two maps of `𝒪_X`-module sheaves and then sheafifying. -/
noncomputable def schemeModuleTensorMap
    {M₁ M₂ N₁ N₂ : X.Modules} (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    schemeModuleTensor M₁ N₁ ⟶ schemeModuleTensor M₂ N₂ :=
  SheafOfModules.commRingSheafTensorMap X.sheaf f g

/-- The scheme-module tensor map is the sheafification of the corresponding
presheaf tensor map.  This presentation fixes the structure-ring sheaf of
the scheme and is convenient for sheafification-adjunction calculations. -/
theorem schemeModuleTensorMap_eq_sheafification
    {M₁ M₂ N₁ N₂ : X.Modules} (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    schemeModuleTensorMap f g =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom f.val g.val) := by
  rfl

/-- The canonical comparison from sheafifying a presheaf tensor product to
first sheafifying its left factor and then forming the concrete tensor
product. -/
noncomputable def schemeModuleTensorSheafificationRightComparison
    (P : PresheafOfModules X.ringCatSheaf.obj) (N : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModules.Monoidal.tensorObj P N.val) ⟶
    schemeModuleTensor
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) N := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  exact F.map (PresheafOfModules.Monoidal.tensorHom
    (adj.unit.app P) (𝟙 N.val))

/-- The sheafification--right-tensor comparison is natural in the right factor. -/
theorem schemeModuleTensorSheafificationRightComparison_naturality
    (P : PresheafOfModules X.ringCatSheaf.obj) {N N' : X.Modules} (f : N ⟶ N') :
    schemeModuleTensorSheafificationRightComparison P N ≫
      schemeModuleTensorMap (𝟙 _) f =
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (𝟙 P) f.val) ≫
      schemeModuleTensorSheafificationRightComparison P N' := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let P' : PresheafOfModules X.ringCatSheaf.obj := P
  let N₀ : PresheafOfModules X.ringCatSheaf.obj := N.val
  let N₁ : PresheafOfModules X.ringCatSheaf.obj := N'.val
  let f' : N₀ ⟶ N₁ := f.val
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  change F.map (PresheafOfModules.Monoidal.tensorHom
      (adj.unit.app P') (𝟙 N₀)) ≫
      F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 (F.obj P').val) f') =
    F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 P') f') ≫
      F.map (PresheafOfModules.Monoidal.tensorHom
        (adj.unit.app P') (𝟙 N₁))
  have hleft : PresheafOfModules.Monoidal.tensorHom
      (adj.unit.app P') (𝟙 N₀) ≫
      PresheafOfModules.Monoidal.tensorHom (𝟙 (F.obj P').val) f' =
      PresheafOfModules.Monoidal.tensorHom (adj.unit.app P') f' := by
    calc
      _ = PresheafOfModules.Monoidal.tensorHom
          (adj.unit.app P' ≫ 𝟙 (F.obj P').val) ((𝟙 N₀) ≫ f') :=
        tensorHom_comp_tensorHom (adj.unit.app P') (𝟙 N₀)
          (𝟙 (F.obj P').val) f'
      _ = _ := by
        exact congrArg₂ (fun a b => PresheafOfModules.Monoidal.tensorHom a b)
          (Category.comp_id _) (Category.id_comp _)
  have hright : PresheafOfModules.Monoidal.tensorHom (𝟙 P') f' ≫
      PresheafOfModules.Monoidal.tensorHom (adj.unit.app P') (𝟙 N₁) =
      PresheafOfModules.Monoidal.tensorHom (adj.unit.app P') f' := by
    calc
      _ = PresheafOfModules.Monoidal.tensorHom
          ((𝟙 P') ≫ adj.unit.app P') (f' ≫ (𝟙 N₁)) :=
        tensorHom_comp_tensorHom (𝟙 P') f' (adj.unit.app P') (𝟙 N₁)
      _ = _ := by
        exact congrArg₂ (fun a b => PresheafOfModules.Monoidal.tensorHom a b)
          (Category.id_comp _) (Category.comp_id _)
  have hmapleft : F.map (PresheafOfModules.Monoidal.tensorHom
      (adj.unit.app P') (𝟙 N₀) ≫
      PresheafOfModules.Monoidal.tensorHom (𝟙 (F.obj P').val) f') =
      F.map (PresheafOfModules.Monoidal.tensorHom (adj.unit.app P') f') :=
    congrArg F.map hleft
  have hmapright : F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 P') f' ≫
      PresheafOfModules.Monoidal.tensorHom (adj.unit.app P') (𝟙 N₁)) =
      F.map (PresheafOfModules.Monoidal.tensorHom (adj.unit.app P') f') :=
    congrArg F.map hright
  have hFleft : F.map (PresheafOfModules.Monoidal.tensorHom
      (adj.unit.app P') (𝟙 N₀)) ≫
      F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 (F.obj P').val) f') =
      F.map (PresheafOfModules.Monoidal.tensorHom
        (adj.unit.app P') (𝟙 N₀) ≫
        PresheafOfModules.Monoidal.tensorHom (𝟙 (F.obj P').val) f') :=
    (F.map_comp _ _).symm
  have hFright : F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 P') f') ≫
      F.map (PresheafOfModules.Monoidal.tensorHom
        (adj.unit.app P') (𝟙 N₁)) =
      F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 P') f' ≫
        PresheafOfModules.Monoidal.tensorHom (adj.unit.app P') (𝟙 N₁)) :=
    (F.map_comp _ _).symm
  exact hFleft.trans (hmapleft.trans (hmapright.symm.trans hFright.symm))

/-- Under the scheme-module sheafification adjunction, composing the counit
with a module morphism recovers its underlying presheaf morphism. -/
theorem schemeModuleSheafificationHomEquiv_counit_comp
    {M N : X.Modules} (f : M ⟶ N) :
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    adj.homEquiv M.val N (adj.counit.app M ≫ f) = f.val := by
  dsimp
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  apply (adj.homEquiv M.val N).symm.injective
  rw [(adj.homEquiv M.val N).symm_apply_apply,
    adj.homEquiv_counit M.val N f.val]
  exact (adj.counit.naturality f).symm

/-- Tensoring maps respects composition in both factors. -/
theorem schemeModuleTensorMap_comp
    {M₁ M₂ M₃ N₁ N₂ N₃ : X.Modules}
    (f₁ : M₁ ⟶ M₂) (g₁ : N₁ ⟶ N₂)
    (f₂ : M₂ ⟶ M₃) (g₂ : N₂ ⟶ N₃) :
    schemeModuleTensorMap f₁ g₁ ≫ schemeModuleTensorMap f₂ g₂ =
      schemeModuleTensorMap (f₁ ≫ f₂) (g₁ ≫ g₂) := by
  exact SheafOfModules.commRingSheafTensorMap_comp X.sheaf f₁ g₁ f₂ g₂

/-- Tensoring identity maps gives the identity map of the tensor product. -/
theorem schemeModuleTensorMap_id (M N : X.Modules) :
    schemeModuleTensorMap (𝟙 M) (𝟙 N) = 𝟙 (schemeModuleTensor M N) := by
  exact SheafOfModules.commRingSheafTensorMap_id X.sheaf M N

/-- Isomorphisms of both tensor factors induce an isomorphism of their
concrete module-sheaf tensor products. -/
noncomputable def schemeModuleTensorMapIso
    {M₁ M₂ N₁ N₂ : X.Modules} (eM : M₁ ≅ M₂) (eN : N₁ ≅ N₂) :
    schemeModuleTensor M₁ N₁ ≅ schemeModuleTensor M₂ N₂ where
  hom := schemeModuleTensorMap eM.hom eN.hom
  inv := schemeModuleTensorMap eM.inv eN.inv
  hom_inv_id := by
    rw [schemeModuleTensorMap_comp, eM.hom_inv_id, eN.hom_inv_id,
      schemeModuleTensorMap_id]
  inv_hom_id := by
    rw [schemeModuleTensorMap_comp, eM.inv_hom_id, eN.inv_hom_id,
      schemeModuleTensorMap_id]

/-- An isomorphism of right factors induces the corresponding isomorphism of
presheaf tensor products before sheafification. -/
noncomputable def schemeModuleTensorSheafificationRightComparisonSourceCongr
    (P : PresheafOfModules X.ringCatSheaf.obj) {N : X.Modules}
    (e : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    PresheafOfModules.Monoidal.tensorObj P N.val ≅
      PresheafOfModules.Monoidal.tensorObj P (SheafOfModules.unit X.ringCatSheaf).val := by
  let eVal : N.val ≅ (SheafOfModules.unit X.ringCatSheaf).val :=
    { hom := e.hom.val
      inv := e.inv.val
      hom_inv_id := by
        exact congrArg (fun q => q.val) e.hom_inv_id
      inv_hom_id := by
        exact congrArg (fun q => q.val) e.inv_hom_id }
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  exact tensorIso (Iso.refl P) eVal


/-- The concrete tensor product of scheme modules is symmetric.  This is the
sheafification of the pointwise symmetry of tensor products of modules. -/
noncomputable def schemeModuleTensorSymmetry (M N : X.Modules) :
    schemeModuleTensor M N ≅ schemeModuleTensor N M := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let M' : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := M.val
  let N' : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := N.val
  letI : MonoidalCategory
      (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.monoidalCategory
  letI : SymmetricCategory
      (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.symmetricCategory
  have e : PresheafOfModules.Monoidal.tensorObj M' N' ≅
      PresheafOfModules.Monoidal.tensorObj N' M' := by
    change M' ⊗ N' ≅ N' ⊗ M'
    exact β_ M' N'
  exact F.mapIso e

/-- Naturality of the concrete symmetry of scheme-module tensor products. -/
theorem schemeModuleTensorSymmetry_naturality
    {M₁ M₂ N₁ N₂ : X.Modules} (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    schemeModuleTensorMap f g ≫ (schemeModuleTensorSymmetry M₂ N₂).hom =
      (schemeModuleTensorSymmetry M₁ N₁).hom ≫ schemeModuleTensorMap g f := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let M₁' : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := M₁.val
  let M₂' : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := M₂.val
  let N₁' : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := N₁.val
  let N₂' : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := N₂.val
  let f' : M₁' ⟶ M₂' := f.val
  let g' : N₁' ⟶ N₂' := g.val
  letI : MonoidalCategory (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.monoidalCategory
  letI : SymmetricCategory (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.symmetricCategory
  change F.map (PresheafOfModules.Monoidal.tensorHom f' g') ≫
      F.map (β_ M₂' N₂').hom =
    F.map (β_ M₁' N₁').hom ≫ F.map
      (PresheafOfModules.Monoidal.tensorHom g' f')
  have h : PresheafOfModules.Monoidal.tensorHom f' g' ≫
      (β_ M₂' N₂').hom = (β_ M₁' N₁').hom ≫
        PresheafOfModules.Monoidal.tensorHom g' f' := by
    change (f' ⊗ₘ g') ≫ (β_ M₂' N₂').hom =
      (β_ M₁' N₁').hom ≫ (g' ⊗ₘ f')
    exact CategoryTheory.BraidedCategory.braiding_naturality f' g'
  calc
    F.map (PresheafOfModules.Monoidal.tensorHom f' g') ≫
        F.map (β_ M₂' N₂').hom =
        F.map (PresheafOfModules.Monoidal.tensorHom f' g' ≫
          (β_ M₂' N₂').hom) :=
      (F.map_comp _ _).symm
    _ = F.map ((β_ M₁' N₁').hom ≫
          PresheafOfModules.Monoidal.tensorHom g' f') := congrArg F.map h
    _ = F.map (β_ M₁' N₁').hom ≫
        F.map (PresheafOfModules.Monoidal.tensorHom g' f') := F.map_comp _ _

/-- Isomorphisms of both factors induce an isomorphism of the corresponding
tensor products over an arbitrary commutative-ring sheaf. -/
noncomputable def SheafOfModules.commRingSheafTensorMapIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    {M₁ M₂ N₁ N₂ : SheafOfModules (commRingSheafToRingSheaf R)}
    (eM : M₁ ≅ M₂) (eN : N₁ ≅ N₂) :
    commRingSheafTensor R M₁ N₁ ≅ commRingSheafTensor R M₂ N₂ where
  hom := commRingSheafTensorMap R eM.hom eN.hom
  inv := commRingSheafTensorMap R eM.inv eN.inv
  hom_inv_id := by
    rw [commRingSheafTensorMap_comp, eM.hom_inv_id, eN.hom_inv_id,
      commRingSheafTensorMap_id]
  inv_hom_id := by
    rw [commRingSheafTensorMap_comp, eM.inv_hom_id, eN.inv_hom_id,
      commRingSheafTensorMap_id]

/-- An endomorphism of the structure-sheaf module acts identically through
the left or right tensor factor. -/
theorem schemeModuleTensorMap_unit_central
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    schemeModuleTensorMap a (𝟙 (SheafOfModules.unit X.ringCatSheaf)) =
      schemeModuleTensorMap (𝟙 (SheafOfModules.unit X.ringCatSheaf)) a := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  change F.map (PresheafOfModules.Monoidal.tensorHom a.val
      (𝟙 (SheafOfModules.unit X.ringCatSheaf).val)) =
    F.map (PresheafOfModules.Monoidal.tensorHom
      (𝟙 (SheafOfModules.unit X.ringCatSheaf).val) a.val)
  have h := presheafTensorHom_unit_central a.val
  exact congrArg F.map h

/-- The sheaf tensor map is additive in its first argument when the second
argument is an identity. -/
theorem schemeModuleTensorMap_add_first_id
    {M M' N : X.Modules} (f g : M ⟶ M') :
    schemeModuleTensorMap (f + g) (𝟙 N) =
      schemeModuleTensorMap f (𝟙 N) + schemeModuleTensorMap g (𝟙 N) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  change F.map
      (PresheafOfModules.Monoidal.tensorHom (f.val + g.val) (𝟙 N.val)) =
    F.map (PresheafOfModules.Monoidal.tensorHom f.val (𝟙 N.val)) +
      F.map (PresheafOfModules.Monoidal.tensorHom g.val (𝟙 N.val))
  have h : PresheafOfModules.Monoidal.tensorHom (f.val + g.val) (𝟙 N.val) =
      PresheafOfModules.Monoidal.tensorHom f.val (𝟙 N.val) +
        PresheafOfModules.Monoidal.tensorHom g.val (𝟙 N.val) := by
    exact presheafTensorHom_add_left f.val g.val
  rw [h]
  exact F.map_add

/-- The sheaf tensor map is additive in its second argument when the first
argument is an identity. -/
theorem schemeModuleTensorMap_add_second_id
    {M N N' : X.Modules} (f g : N ⟶ N') :
    schemeModuleTensorMap (𝟙 M) (f + g) =
      schemeModuleTensorMap (𝟙 M) f + schemeModuleTensorMap (𝟙 M) g := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  change F.map
      (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) (f.val + g.val)) =
    F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) f.val) +
      F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) g.val)
  have h : PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) (f.val + g.val) =
      PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) f.val +
        PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) g.val := by
    exact presheafTensorHom_add_right f.val g.val
  rw [h]
  exact F.map_add

/-- Tensoring morphisms is additive in the first argument. -/
theorem schemeModuleTensorMap_add_first
    {M M' N N' : X.Modules} (f g : M ⟶ M') (h : N ⟶ N') :
    schemeModuleTensorMap (f + g) h =
      schemeModuleTensorMap f h + schemeModuleTensorMap g h := by
  calc
    schemeModuleTensorMap (f + g) h =
        schemeModuleTensorMap (f + g) (𝟙 N) ≫
          schemeModuleTensorMap (𝟙 M') h := by
      rw [schemeModuleTensorMap_comp]
      simp
    _ = (schemeModuleTensorMap f (𝟙 N) +
          schemeModuleTensorMap g (𝟙 N)) ≫
          schemeModuleTensorMap (𝟙 M') h := by
      rw [schemeModuleTensorMap_add_first_id]
    _ = schemeModuleTensorMap f (𝟙 N) ≫
          schemeModuleTensorMap (𝟙 M') h +
        schemeModuleTensorMap g (𝟙 N) ≫
          schemeModuleTensorMap (𝟙 M') h := by
      exact Preadditive.add_comp _ _ _ _ _ _
    _ = schemeModuleTensorMap f h + schemeModuleTensorMap g h := by
      rw [schemeModuleTensorMap_comp, schemeModuleTensorMap_comp]
      simp

/-- Tensoring morphisms is additive in the second argument. -/
theorem schemeModuleTensorMap_add_second
    {M M' N N' : X.Modules} (h : M ⟶ M') (f g : N ⟶ N') :
    schemeModuleTensorMap h (f + g) =
      schemeModuleTensorMap h f + schemeModuleTensorMap h g := by
  calc
    schemeModuleTensorMap h (f + g) =
        schemeModuleTensorMap (𝟙 M) (f + g) ≫
          schemeModuleTensorMap h (𝟙 N') := by
      rw [schemeModuleTensorMap_comp]
      simp
    _ = (schemeModuleTensorMap (𝟙 M) f +
          schemeModuleTensorMap (𝟙 M) g) ≫
          schemeModuleTensorMap h (𝟙 N') := by
      rw [schemeModuleTensorMap_add_second_id]
    _ = schemeModuleTensorMap (𝟙 M) f ≫
          schemeModuleTensorMap h (𝟙 N') +
        schemeModuleTensorMap (𝟙 M) g ≫
          schemeModuleTensorMap h (𝟙 N') := by
      exact Preadditive.add_comp _ _ _ _ _ _
    _ = schemeModuleTensorMap h f + schemeModuleTensorMap h g := by
      rw [schemeModuleTensorMap_comp, schemeModuleTensorMap_comp]
      simp

/-- Tensoring on the right by a fixed module sheaf.  This packages the
object-level construction as a functor, so it can later be applied to the
closed-immersion ideal sequence once exactness for a locally free twist is
established. -/
noncomputable def schemeModuleTensorRight (N : X.Modules) : X.Modules ⥤ X.Modules where
  obj M := schemeModuleTensor M N
  map f := schemeModuleTensorMap f (𝟙 N)
  map_id M := schemeModuleTensorMap_id M N
  map_comp f g := by
    simpa using (schemeModuleTensorMap_comp f (𝟙 N) g (𝟙 N)).symm

/-- Package mutually inverse right-tensor functors as an equivalence.  For
an invertible module sheaf `T`, one takes `Tinv` to be its inverse and obtains
the two natural isomorphisms from tensor associativity and
`T ⊗ Tinv ≅ 𝒪_X`. -/
noncomputable def schemeModuleTensorRightEquivalenceOfInverse
    (T Tinv : X.Modules)
    (unitIso : 𝟭 X.Modules ≅
      schemeModuleTensorRight Tinv ⋙ schemeModuleTensorRight T)
    (counitIso : schemeModuleTensorRight T ⋙
      schemeModuleTensorRight Tinv ≅ 𝟭 X.Modules) :
    X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (schemeModuleTensorRight Tinv)
    (schemeModuleTensorRight T) unitIso counitIso

/-- Tensoring scheme modules on the right is additive, without any flatness
or local-freeness assumption on the tensor factor. -/
noncomputable instance schemeModuleTensorRight_additive (N : X.Modules) :
    (schemeModuleTensorRight N).Additive where
  map_add {M M'} f g := by
    let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    change F.map
        (PresheafOfModules.Monoidal.tensorHom (f.val + g.val) (𝟙 N.val)) =
      F.map (PresheafOfModules.Monoidal.tensorHom f.val (𝟙 N.val)) +
        F.map (PresheafOfModules.Monoidal.tensorHom g.val (𝟙 N.val))
    have h : PresheafOfModules.Monoidal.tensorHom (f.val + g.val) (𝟙 N.val) =
        PresheafOfModules.Monoidal.tensorHom f.val (𝟙 N.val) +
          PresheafOfModules.Monoidal.tensorHom g.val (𝟙 N.val) := by
      exact presheafTensorHom_add_left f.val g.val
    rw [h]
    exact F.map_add

/-- An isomorphism of right tensor factors induces a natural isomorphism of
the associated right-tensor functors. -/
noncomputable def schemeModuleTensorRightCongr {L₁ L₂ : X.Modules} (e : L₁ ≅ L₂) :
    schemeModuleTensorRight L₁ ≅ schemeModuleTensorRight L₂ :=
  NatIso.ofComponents (fun M =>
    { hom := schemeModuleTensorMap (𝟙 M) e.hom
      inv := schemeModuleTensorMap (𝟙 M) e.inv
      hom_inv_id := by
        calc
          schemeModuleTensorMap (𝟙 M) e.hom ≫ schemeModuleTensorMap (𝟙 M) e.inv =
              schemeModuleTensorMap ((𝟙 M) ≫ (𝟙 M)) (e.hom ≫ e.inv) :=
            schemeModuleTensorMap_comp (𝟙 M) e.hom (𝟙 M) e.inv
          _ = schemeModuleTensorMap (𝟙 M) (𝟙 L₁) := by simp
          _ = 𝟙 (schemeModuleTensor M L₁) := schemeModuleTensorMap_id M L₁
      inv_hom_id := by
        calc
          schemeModuleTensorMap (𝟙 M) e.inv ≫ schemeModuleTensorMap (𝟙 M) e.hom =
              schemeModuleTensorMap ((𝟙 M) ≫ (𝟙 M)) (e.inv ≫ e.hom) :=
            schemeModuleTensorMap_comp (𝟙 M) e.inv (𝟙 M) e.hom
          _ = schemeModuleTensorMap (𝟙 M) (𝟙 L₂) := by simp
          _ = 𝟙 (schemeModuleTensor M L₂) := schemeModuleTensorMap_id M L₂ }) (by
    intro M M' f
    change schemeModuleTensorMap f (𝟙 L₁) ≫ schemeModuleTensorMap (𝟙 M') e.hom =
      schemeModuleTensorMap (𝟙 M) e.hom ≫ schemeModuleTensorMap f (𝟙 L₂)
    calc
      schemeModuleTensorMap f (𝟙 L₁) ≫ schemeModuleTensorMap (𝟙 M') e.hom =
          schemeModuleTensorMap (f ≫ 𝟙 M') ((𝟙 L₁) ≫ e.hom) :=
        schemeModuleTensorMap_comp f (𝟙 L₁) (𝟙 M') e.hom
      _ = schemeModuleTensorMap f e.hom := by simp
      _ = schemeModuleTensorMap ((𝟙 M) ≫ f) (e.hom ≫ (𝟙 L₂)) := by simp
      _ = schemeModuleTensorMap (𝟙 M) e.hom ≫ schemeModuleTensorMap f (𝟙 L₂) :=
        (schemeModuleTensorMap_comp (𝟙 M) e.hom f (𝟙 L₂)).symm)

/-- At the presheaf level, tensoring with the structure sheaf is the identity.
Writing this iso explicitly avoids treating the newly defined sheaf tensor as
an unverified notation. -/
noncomputable def schemeModuleTensorUnitLeftRawIso (M : X.Modules) :
    PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
      (SheafOfModules.unit X.ringCatSheaf).val M.val ≅ M.val := by
  let M' : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := M.val
  change PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
    (PresheafOfModules.unit (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) M' ≅ M'
  letI : MonoidalCategory
      (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.monoidalCategory
  exact λ_ M'

/-- Tensoring a module sheaf with `𝒪_X` on the left is canonically
isomorphic to the original sheaf.  The second factor is the sheafification
counit, whose invertibility identifies the sheafification of an existing
module sheaf with that sheaf. -/
noncomputable def schemeModuleTensorUnitLeftIso (M : X.Modules) :
    schemeModuleTensor (SheafOfModules.unit X.ringCatSheaf) M ≅ M := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  exact F.mapIso (schemeModuleTensorUnitLeftRawIso M) ≪≫
    @asIso _ _ _ _ _ (NatIso.isIso_app_of_isIso adj.counit M)

/-- The analogous presheaf-level right unit iso. -/
noncomputable def schemeModuleTensorUnitRightRawIso (M : X.Modules) :
    PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
      M.val (SheafOfModules.unit X.ringCatSheaf).val ≅ M.val := by
  let M' : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := M.val
  change PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) M'
    (PresheafOfModules.unit (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ≅ M'
  letI : MonoidalCategory
      (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.monoidalCategory
  exact ρ_ M'

/-- Tensoring on the right by `𝒪_X` is canonically the identity.  In
particular, `schemeModuleTensorRight 𝒪_X` has the expected objectwise unit
isomorphism. -/
noncomputable def schemeModuleTensorUnitRightIso (M : X.Modules) :
    schemeModuleTensor M (SheafOfModules.unit X.ringCatSheaf) ≅ M := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  exact F.mapIso (schemeModuleTensorUnitRightRawIso M) ≪≫
    @asIso _ _ _ _ _ (NatIso.isIso_app_of_isIso adj.counit M)

/-- The presheaf right-unit isomorphism used to normalize the source of the
sheafification--right-tensor comparison. -/
noncomputable def schemeModuleTensorSheafificationRightComparisonUnitRawIso
    (P : PresheafOfModules X.ringCatSheaf.obj) :
    PresheafOfModules.Monoidal.tensorObj P
      (SheafOfModules.unit X.ringCatSheaf).val ≅ P := by
  let P' : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := P
  letI : MonoidalCategory
      (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.monoidalCategory
  change P' ⊗ (PresheafOfModules.unit
    (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ≅ P'
  exact ρ_ P'

/-- A unit normal form for the source and target of the canonical
sheafification--right-tensor comparison. -/
noncomputable def schemeModuleTensorSheafificationRightComparisonUnitNormalFormIso
    (P : PresheafOfModules X.ringCatSheaf.obj) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModules.Monoidal.tensorObj P
        (SheafOfModules.unit X.ringCatSheaf).val) ≅
    schemeModuleTensor
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P)
      (SheafOfModules.unit X.ringCatSheaf) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let P' : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := P
  letI : MonoidalCategory
      (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.monoidalCategory
  have e : PresheafOfModules.Monoidal.tensorObj P'
      (SheafOfModules.unit X.ringCatSheaf).val ≅ P' := by
    change P' ⊗ (PresheafOfModules.unit
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ≅ P'
    exact ρ_ P'
  exact F.mapIso e ≪≫
    (schemeModuleTensorUnitRightIso (F.obj P)).symm

/-- The sheafification--right-tensor comparison is invertible on the unit. -/
theorem schemeModuleTensorSheafificationRightComparison_unit_isIso
    (P : PresheafOfModules X.ringCatSheaf.obj) :
    IsIso (schemeModuleTensorSheafificationRightComparison P
      (SheafOfModules.unit X.ringCatSheaf)) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let P' : PresheafOfModules X.ringCatSheaf.obj := P
  let FP : X.Modules := F.obj P
  let FP' : PresheafOfModules X.ringCatSheaf.obj := FP.val
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  letI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  have hraw : PresheafOfModules.Monoidal.tensorHom
      (adj.unit.app P') (𝟙 (SheafOfModules.unit X.ringCatSheaf).val) ≫
      (ρ_ FP').hom =
      (schemeModuleTensorSheafificationRightComparisonUnitRawIso P').hom ≫
        adj.unit.app P' := by
    unfold schemeModuleTensorSheafificationRightComparisonUnitRawIso
    dsimp
    exact rightUnitor_naturality (adj.unit.app P')
  have hcomp : schemeModuleTensorSheafificationRightComparison P
      (SheafOfModules.unit X.ringCatSheaf) ≫
      (schemeModuleTensorUnitRightIso (F.obj P)).hom =
      F.map (schemeModuleTensorSheafificationRightComparisonUnitRawIso P).hom := by
    change F.map (PresheafOfModules.Monoidal.tensorHom
      (adj.unit.app P') (𝟙 (SheafOfModules.unit X.ringCatSheaf).val)) ≫
      (F.map (ρ_ FP').hom ≫ adj.counit.app FP) =
      F.map (schemeModuleTensorSheafificationRightComparisonUnitRawIso P').hom
    calc
      F.map (PresheafOfModules.Monoidal.tensorHom
          (adj.unit.app P') (𝟙 (SheafOfModules.unit X.ringCatSheaf).val)) ≫
          (F.map (ρ_ FP').hom ≫ adj.counit.app FP) =
          (F.map (PresheafOfModules.Monoidal.tensorHom
            (adj.unit.app P') (𝟙 (SheafOfModules.unit X.ringCatSheaf).val)) ≫
            F.map (ρ_ FP').hom) ≫ adj.counit.app FP :=
        (Category.assoc _ _ _).symm
      _ = F.map (PresheafOfModules.Monoidal.tensorHom
            (adj.unit.app P') (𝟙 (SheafOfModules.unit X.ringCatSheaf).val) ≫
            (ρ_ FP').hom) ≫ adj.counit.app FP :=
        congrArg (fun q => q ≫ adj.counit.app FP)
          (F.map_comp _ _).symm
      _ = F.map ((schemeModuleTensorSheafificationRightComparisonUnitRawIso P').hom ≫
            adj.unit.app P') ≫ adj.counit.app FP :=
        congrArg (fun q => q ≫ adj.counit.app FP) (congrArg F.map hraw)
      _ = (F.map (schemeModuleTensorSheafificationRightComparisonUnitRawIso P').hom ≫
            F.map (adj.unit.app P')) ≫ adj.counit.app FP :=
        congrArg (fun q => q ≫ adj.counit.app FP) (F.map_comp _ _)
      _ = F.map (schemeModuleTensorSheafificationRightComparisonUnitRawIso P').hom ≫
          (F.map (adj.unit.app P') ≫ adj.counit.app FP) := Category.assoc _ _ _
      _ = F.map (schemeModuleTensorSheafificationRightComparisonUnitRawIso P').hom := by
        have htri : F.map (adj.unit.app P') ≫ adj.counit.app FP = 𝟙 _ := by
          change F.map (adj.unit.app P') ≫ adj.counit.app (F.obj P') = 𝟙 _
          exact adj.left_triangle_components P'
        rw [htri]
        exact Category.comp_id _
  have heq : schemeModuleTensorSheafificationRightComparison P
      (SheafOfModules.unit X.ringCatSheaf) =
      (schemeModuleTensorSheafificationRightComparisonUnitNormalFormIso P).hom := by
    calc
      schemeModuleTensorSheafificationRightComparison P
          (SheafOfModules.unit X.ringCatSheaf) =
          schemeModuleTensorSheafificationRightComparison P
            (SheafOfModules.unit X.ringCatSheaf) ≫ 𝟙 _ :=
        (Category.comp_id _).symm
      _ = schemeModuleTensorSheafificationRightComparison P
          (SheafOfModules.unit X.ringCatSheaf) ≫
          ((schemeModuleTensorUnitRightIso (F.obj P)).hom ≫
            (schemeModuleTensorUnitRightIso (F.obj P)).inv) := by
        exact congrArg (fun q =>
          schemeModuleTensorSheafificationRightComparison P
            (SheafOfModules.unit X.ringCatSheaf) ≫ q)
          (schemeModuleTensorUnitRightIso (F.obj P)).hom_inv_id.symm
      _ = (schemeModuleTensorSheafificationRightComparison P
          (SheafOfModules.unit X.ringCatSheaf) ≫
          (schemeModuleTensorUnitRightIso (F.obj P)).hom) ≫
          (schemeModuleTensorUnitRightIso (F.obj P)).inv := (Category.assoc _ _ _).symm
      _ = F.map (schemeModuleTensorSheafificationRightComparisonUnitRawIso P).hom ≫
          (schemeModuleTensorUnitRightIso (F.obj P)).inv :=
        congrArg (fun q => q ≫ (schemeModuleTensorUnitRightIso (F.obj P)).inv) hcomp
      _ = (schemeModuleTensorSheafificationRightComparisonUnitNormalFormIso P).hom := by
        unfold schemeModuleTensorSheafificationRightComparisonUnitNormalFormIso
        dsimp
        rfl
  rw [heq]
  exact (schemeModuleTensorSheafificationRightComparisonUnitNormalFormIso P).isIso_hom


/-- The sheafification--right-tensor comparison is invertible whenever its
right factor is isomorphic to the unit module. -/
theorem schemeModuleTensorSheafificationRightComparison_isIso_of_iso_unit
    (P : PresheafOfModules X.ringCatSheaf.obj) {N : X.Modules}
    (e : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (schemeModuleTensorSheafificationRightComparison P N) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let eRaw := schemeModuleTensorSheafificationRightComparisonSourceCongr P e
  let eSource := F.mapIso eRaw
  let eTarget := schemeModuleTensorMapIso (Iso.refl (F.obj P)) e
  letI : IsIso (schemeModuleTensorSheafificationRightComparison P
      (SheafOfModules.unit X.ringCatSheaf)) :=
    schemeModuleTensorSheafificationRightComparison_unit_isIso P
  let eUnit := asIso (schemeModuleTensorSheafificationRightComparison P
    (SheafOfModules.unit X.ringCatSheaf))
  have hnat := schemeModuleTensorSheafificationRightComparison_naturality P e.hom
  have hnat' : schemeModuleTensorSheafificationRightComparison P N ≫ eTarget.hom =
      eSource.hom ≫ schemeModuleTensorSheafificationRightComparison P
        (SheafOfModules.unit X.ringCatSheaf) := by
    exact hnat
  let eComp := eSource ≪≫ eUnit ≪≫ eTarget.symm
  have heq : schemeModuleTensorSheafificationRightComparison P N = eComp.hom := by
    calc
      schemeModuleTensorSheafificationRightComparison P N =
          schemeModuleTensorSheafificationRightComparison P N ≫ 𝟙 _ :=
        (Category.comp_id _).symm
      _ = schemeModuleTensorSheafificationRightComparison P N ≫
          (eTarget.hom ≫ eTarget.inv) := by
        exact congrArg (fun q =>
          schemeModuleTensorSheafificationRightComparison P N ≫ q)
          eTarget.hom_inv_id.symm
      _ = (schemeModuleTensorSheafificationRightComparison P N ≫
          eTarget.hom) ≫ eTarget.inv := (Category.assoc _ _ _).symm
      _ = (eSource.hom ≫ schemeModuleTensorSheafificationRightComparison P
          (SheafOfModules.unit X.ringCatSheaf)) ≫ eTarget.inv :=
        congrArg (fun q => q ≫ eTarget.inv) hnat'
      _ = eComp.hom := by rfl
  rw [heq]
  exact eComp.isIso_hom


/-- A coordinate cover detects invertibility of the sheafification--right-tensor comparison. -/
theorem schemeModuleTensorSheafificationRightComparison_isIso_of_coversTop
    {ι : Type u} (U : ι → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    (P : PresheafOfModules X.ringCatSheaf.obj) (N : X.Modules)
    (h : ∀ j, IsIso ((SheafOfModules.overFunctor X.ringCatSheaf (U j)).map
      (schemeModuleTensorSheafificationRightComparison P N))) :
    IsIso (schemeModuleTensorSheafificationRightComparison P N) := by
  let F : ∀ j, X.Modules ⥤ SheafOfModules (X.ringCatSheaf.over (U j)) :=
    fun j => SheafOfModules.overFunctor X.ringCatSheaf (U j)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U hU
  letI : ∀ j, IsIso ((F j).map
      (schemeModuleTensorSheafificationRightComparison P N)) := by
    intro j
    exact h j
  exact hF.isIso (schemeModuleTensorSheafificationRightComparison P N)

/-- Naturality of the left-unit identification for the concrete sheaf
tensor product. -/
theorem schemeModuleTensorUnitLeftIso_naturality
    {M N : X.Modules} (f : M ⟶ N) :
    schemeModuleTensorMap (𝟙 (SheafOfModules.unit X.ringCatSheaf)) f ≫
        (schemeModuleTensorUnitLeftIso N).hom =
      (schemeModuleTensorUnitLeftIso M).hom ≫ f := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  let M₀ : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := M.val
  let M₁ : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := N.val
  let f₀ : M₀ ⟶ M₁ := f.val
  let U : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
    PresheafOfModules.unit (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)
  letI : MonoidalCategory
      (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.monoidalCategory
  have hraw : PresheafOfModules.Monoidal.tensorHom (𝟙 U) f₀ ≫ (λ_ M₁).hom =
      (λ_ M₀).hom ≫ f₀ :=
    leftUnitor_naturality f₀
  change F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 U) f₀) ≫
      (F.map (λ_ M₁).hom ≫ adj.counit.app N) =
    (F.map (λ_ M₀).hom ≫ adj.counit.app M) ≫ f
  have hcounit : F.map f₀ ≫ adj.counit.app N = adj.counit.app M ≫ f := by
    change F.map f.val ≫ adj.counit.app N = adj.counit.app M ≫ f
    exact adj.counit.naturality f
  calc
    F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 U) f₀) ≫
        (F.map (λ_ M₁).hom ≫ adj.counit.app N) =
        (F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 U) f₀) ≫
          F.map (λ_ M₁).hom) ≫ adj.counit.app N := (Category.assoc _ _ _).symm
    _ = F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 U) f₀ ≫
          (λ_ M₁).hom) ≫ adj.counit.app N :=
        congrArg (fun q => q ≫ adj.counit.app N)
          (F.map_comp (PresheafOfModules.Monoidal.tensorHom (𝟙 U) f₀)
            (λ_ M₁).hom).symm
    _ = F.map ((λ_ M₀).hom ≫ f₀) ≫ adj.counit.app N :=
        congrArg (fun q => F.map q ≫ adj.counit.app N) hraw
    _ = (F.map (λ_ M₀).hom ≫ F.map f₀) ≫ adj.counit.app N :=
        congrArg (fun q => q ≫ adj.counit.app N) (F.map_comp (λ_ M₀).hom f₀)
    _ = F.map (λ_ M₀).hom ≫ (F.map f₀ ≫ adj.counit.app N) :=
        Category.assoc _ _ _
    _ = F.map (λ_ M₀).hom ≫ (adj.counit.app M ≫ f) := by
      rw [hcounit]
      rfl
    _ = (F.map (λ_ M₀).hom ≫ adj.counit.app M) ≫ f :=
        (Category.assoc _ _ _).symm

/-- Inverse form of left-unit naturality. -/
theorem schemeModuleTensorUnitLeftIso_inv_naturality
    {M N : X.Modules} (f : M ⟶ N) :
    (schemeModuleTensorUnitLeftIso M).inv ≫
        schemeModuleTensorMap (𝟙 (SheafOfModules.unit X.ringCatSheaf)) f =
      f ≫ (schemeModuleTensorUnitLeftIso N).inv := by
  apply (cancel_mono (schemeModuleTensorUnitLeftIso N).hom).mp
  rw [Category.assoc, schemeModuleTensorUnitLeftIso_naturality]
  simp

/-- The tensor product of two global sections.  A section is represented by
a morphism from the structure module.  Tensoring the two representing
morphisms gives a map out of `O_X tensor O_X`, and the inverse left-unitor
identifies that source with `O_X`.  This is the section multiplication map
needed to turn an isomorphism `L tensor M ≅ H` into the fixed and moving
linear systems in Voisin's divisor argument. -/
noncomputable def schemeModuleTensorSection
    (M N : X.Modules) (s : M.sections) (t : N.sections) :
    (schemeModuleTensor M N).sections :=
  (schemeModuleTensor M N).unitHomEquiv
    ((schemeModuleTensorUnitLeftIso
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).inv ≫
      schemeModuleTensorMap
        (M.unitHomEquiv.symm s) (N.unitHomEquiv.symm t))

/-- Multiplication of global sections through a supplied tensor-product
identification.  For divisor line bundles in Voisin's argument one takes
`M = O(C)`, `N = O(H-C)`, `P = O(H)`, and the canonical isomorphism
`M tensor N ≅ P`. -/
noncomputable def schemeModuleSectionProduct
    (M N P : X.Modules) (e : schemeModuleTensor M N ≅ P)
    (s : M.sections) (t : N.sections) : P.sections :=
  SheafOfModules.sectionsMap e.hom (schemeModuleTensorSection M N s t)

/-- Tensoring on the right by the structure sheaf is naturally isomorphic to
the identity functor on scheme modules. -/
noncomputable def schemeModuleTensorRightUnitIso :
    schemeModuleTensorRight (SheafOfModules.unit X.ringCatSheaf) ≅ 𝟭 X.Modules :=
  NatIso.ofComponents (fun M => schemeModuleTensorUnitRightIso M) (by
    intro M M' f
    let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    letI : IsIso adj.counit := by
      dsimp [adj]
      infer_instance
    let M₀ : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := M.val
    let M₁ : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := M'.val
    let f₀ : M₀ ⟶ M₁ := f.val
    let U : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
      PresheafOfModules.unit (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)
    letI : MonoidalCategory
        (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
      PresheafOfModules.monoidalCategory
    have hraw : PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U) ≫ (ρ_ M₁).hom =
        (ρ_ M₀).hom ≫ f₀ :=
      rightUnitor_naturality f₀
    change F.map (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U)) ≫
        (F.map (ρ_ M₁).hom ≫ adj.counit.app M') =
      (F.map (ρ_ M₀).hom ≫ adj.counit.app M) ≫ f
    have hcounit : F.map f₀ ≫ adj.counit.app M' = adj.counit.app M ≫ f := by
      change F.map f.val ≫ adj.counit.app M' = adj.counit.app M ≫ f
      exact adj.counit.naturality f
    calc
      F.map (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U)) ≫
          (F.map (ρ_ M₁).hom ≫ adj.counit.app M') =
          (F.map (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U)) ≫
            F.map (ρ_ M₁).hom) ≫ adj.counit.app M' := (Category.assoc _ _ _).symm
      _ = F.map (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U) ≫
            (ρ_ M₁).hom) ≫ adj.counit.app M' :=
          congrArg (fun q => q ≫ adj.counit.app M')
            (F.map_comp (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U)) (ρ_ M₁).hom).symm
      _ = F.map ((ρ_ M₀).hom ≫ f₀) ≫ adj.counit.app M' :=
          congrArg (fun q => F.map q ≫ adj.counit.app M') hraw
      _ = (F.map (ρ_ M₀).hom ≫ F.map f₀) ≫ adj.counit.app M' :=
          congrArg (fun q => q ≫ adj.counit.app M') (F.map_comp (ρ_ M₀).hom f₀)
      _ = F.map (ρ_ M₀).hom ≫ (F.map f₀ ≫ adj.counit.app M') := Category.assoc _ _ _
      _ = F.map (ρ_ M₀).hom ≫ (adj.counit.app M ≫ f) := by
        rw [hcounit]
        rfl
      _ = (F.map (ρ_ M₀).hom ≫ adj.counit.app M) ≫ f := (Category.assoc _ _ _).symm)

/-- A globally trivial twist has a right tensor functor naturally isomorphic
to the identity. -/
noncomputable def schemeModuleTensorRightIsoUnit {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) :
    schemeModuleTensorRight L ≅ 𝟭 X.Modules :=
  schemeModuleTensorRightCongr e ≪≫ schemeModuleTensorRightUnitIso

/-- Tensoring by a globally trivial module sheaf preserves finite limits. -/
theorem schemeModuleTensorRight_preservesFiniteLimits_of_iso_unit {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) :
    PreservesFiniteLimits (schemeModuleTensorRight L) :=
  preservesFiniteLimits_of_natIso (schemeModuleTensorRightIsoUnit e).symm

/-- Tensoring by a globally trivial module sheaf preserves finite colimits. -/
theorem schemeModuleTensorRight_preservesFiniteColimits_of_iso_unit {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) :
    PreservesFiniteColimits (schemeModuleTensorRight L) :=
  preservesFiniteColimits_of_natIso (schemeModuleTensorRightIsoUnit e).symm

/-- The right tensor functor by `𝒪_X` preserves finite limits because it is
naturally isomorphic to the identity. -/
noncomputable instance schemeModuleTensorRightUnit_preservesFiniteLimits :
    PreservesFiniteLimits
      (schemeModuleTensorRight (SheafOfModules.unit X.ringCatSheaf)) :=
  preservesFiniteLimits_of_natIso schemeModuleTensorRightUnitIso.symm

/-- The right tensor functor by `𝒪_X` preserves finite colimits for the same
reason. -/
noncomputable instance schemeModuleTensorRightUnit_preservesFiniteColimits :
    PreservesFiniteColimits
      (schemeModuleTensorRight (SheafOfModules.unit X.ringCatSheaf)) :=
  preservesFiniteColimits_of_natIso schemeModuleTensorRightUnitIso.symm

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- Tensoring on the right transports any finite biproduct to the
biproduct of the individually tensorized summands.  Finite-limit
preservation supplies both preservation of the zero object and of the
underlying finite product. -/
noncomputable def schemeModuleTensorRightBiproductIso
    (T : X.Modules) [PreservesFiniteLimits (schemeModuleTensorRight T)]
    {J : Type u} [Fintype J] (M : J → X.Modules) :
    (⨁ fun j ↦ schemeModuleTensor (M j) T) ≅
      schemeModuleTensor (⨁ M) T := by
  let F := schemeModuleTensorRight T
  letI : F.PreservesZeroMorphisms := inferInstance
  letI : PreservesLimit (Discrete.functor M) F := inferInstance
  letI : PreservesBiproduct M F :=
    preservesBiproduct_of_preservesProduct F
  exact (F.mapBiproduct M).symm

/-- The ideal sheaf of a closed immersion twisted by an arbitrary module
sheaf.  This is the `I_Z ⊗ L` quotient which appears in Voisin's Serre
extension. -/
noncomputable def closedImmersionIdealTwist {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (L : X.Modules) : X.Modules :=
  schemeModuleTensor (closedImmersionModule i) L

/-- The untwisted ideal is recovered by twisting with the structure sheaf. -/
noncomputable def closedImmersionIdealTwistUnitIso {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    closedImmersionIdealTwist i (SheafOfModules.unit X.ringCatSheaf) ≅
      closedImmersionModule i :=
  schemeModuleTensorUnitRightIso (closedImmersionModule i)

/-- The closed-immersion ideal sequence after tensoring on the right by a
fixed module sheaf.  Its first object is definitionally the actual twisted
ideal `I_Z ⊗ L`. -/
noncomputable def closedImmersionIdealTwistSequence {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (L : X.Modules) :
    ShortComplex X.Modules :=
  (closedImmersionModulePushforwardSequence i).map (schemeModuleTensorRight L)

/-- Any tensor functor that preserves finite limits and colimits transports
the proved closed-immersion ideal sequence to a short exact sequence.  A
separate theorem below obtains the same conclusion from trivializations on
an open cover, without these global preservation hypotheses. -/
theorem closedImmersionIdealTwistSequence_shortExact {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (L : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight L)]
    [PreservesFiniteColimits (schemeModuleTensorRight L)] :
    (closedImmersionIdealTwistSequence i L).ShortExact := by
  exact (closedImmersionModulePushforwardSequence_shortExact i).map_of_exact
    (schemeModuleTensorRight L)

/-- Tensoring the closed-immersion ideal sequence by `𝒪_X` is short exact.
This is the fully discharged base case of the twisted Serre sequence. -/
theorem closedImmersionIdealTwistSequence_unit_shortExact {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).ShortExact :=
  closedImmersionIdealTwistSequence_shortExact i (SheafOfModules.unit X.ringCatSheaf)

/-- The ideal sequence stays short exact after tensoring by any globally
trivial module sheaf.  This is the local exactness statement needed for the
locally free projective twists in Voisin's construction. -/
theorem closedImmersionIdealTwistSequence_shortExact_of_iso_unit {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) :
    letI : PreservesFiniteLimits (schemeModuleTensorRight L) :=
      schemeModuleTensorRight_preservesFiniteLimits_of_iso_unit e
    letI : PreservesFiniteColimits (schemeModuleTensorRight L) :=
      schemeModuleTensorRight_preservesFiniteColimits_of_iso_unit e
    (closedImmersionIdealTwistSequence i L).ShortExact := by
  letI : PreservesFiniteLimits (schemeModuleTensorRight L) :=
    schemeModuleTensorRight_preservesFiniteLimits_of_iso_unit e
  letI : PreservesFiniteColimits (schemeModuleTensorRight L) :=
    schemeModuleTensorRight_preservesFiniteColimits_of_iso_unit e
  exact closedImmersionIdealTwistSequence_shortExact i L

/-- A map of twisting sheaves induces the corresponding map of twisted ideal
sheaves. -/
noncomputable def closedImmersionIdealTwistMap {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {L₁ L₂ : X.Modules} (f : L₁ ⟶ L₂) :
    closedImmersionIdealTwist i L₁ ⟶ closedImmersionIdealTwist i L₂ :=
  schemeModuleTensorMap (𝟙 (closedImmersionModule i)) f

end

/-!
## Local tensor exactness on an over-site

The projective twist in Voisin's construction is only locally trivial.  The
following generic statements are the over-site counterpart of the global
`schemeModuleTensorRightIsoUnit` results above.  They let a chosen local
trivialization be used directly on the sheaf of modules over an open, where
tensoring by the twist is naturally isomorphic to the identity.
-/

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- The hom of the over-site tensor comparison, exposed in the form used by
the local naturality calculations. -/
theorem overFunctor_commRingSheafTensorIso_hom_eq
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (M N : SheafOfModules (commRingSheafToRingSheaf R)) :
    (overFunctor_commRingSheafTensorIso R U M N).hom =
      (overFunctor_sheafificationComparisonIso U
        (PresheafOfModules.Monoidal.tensorObj M.val N.val)).inv ≫
      (PresheafOfModules.sheafification
        (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map
        (PresheafOfModules.pushforward₀_tensorIso
          (F := Over.forget U) M.val N.val).hom := by
  rfl

/-- The sheafified presheaf tensor map is exactly the concrete module-sheaf
tensor map. -/
theorem commRingSheafTensorMap_eq_sheafification
    (R : Sheaf J CommRingCat.{u})
    {M₁ M₂ N₁ N₂ : SheafOfModules (commRingSheafToRingSheaf R)}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    commRingSheafTensorMap R f g =
      (PresheafOfModules.sheafification
        (𝟙 (commRingSheafToRingSheaf R).obj)).map
        (PresheafOfModules.Monoidal.tensorHom f.val g.val) := by
  rfl

universe v₁ v₂ u₁ u₂

private lemma map_comp_eq_of_eq {C₁ : Type u₁} {D : Type u₂}
    [Category.{v₁} C₁] [Category.{v₂} D]
    (F : Functor C₁ D) {W X Y Z : C₁} (a : W ⟶ X) (b : X ⟶ Y)
    (c : W ⟶ Z) (d : Z ⟶ Y) (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  calc
    F.map a ≫ F.map b = F.map (a ≫ b) := (F.map_comp _ _).symm
    _ = F.map (c ≫ d) := congrArg F.map h
    _ = F.map c ≫ F.map d := F.map_comp _ _

private lemma paste_comp_eq {C₁ : Type u₁} [Category.{v₁} C₁]
    {A B C₂ D E F : C₁} (a : A ⟶ B) (b : B ⟶ C₂)
    (c : A ⟶ D) (d : D ⟶ C₂) (e : C₂ ⟶ E)
    (f : D ⟶ F) (g : F ⟶ E)
    (h₁ : a ≫ b = c ≫ d) (h₂ : d ≫ e = f ≫ g) :
    a ≫ (b ≫ e) = (c ≫ f) ≫ g := by
  calc
    a ≫ (b ≫ e) = (a ≫ b) ≫ e := (Category.assoc _ _ _).symm
    _ = (c ≫ d) ≫ e := congrArg (fun q => q ≫ e) h₁
    _ = c ≫ (d ≫ e) := Category.assoc _ _ _
    _ = c ≫ (f ≫ g) := congrArg (fun q => c ≫ q) h₂
    _ = (c ≫ f) ≫ g := (Category.assoc _ _ _).symm

/-- Raw naturality of the over-site tensor comparison, with both sides
written over the underlying restricted ring sheaf.  Keeping this intermediate
form separate avoids expensive elaboration across the two definitionally
equal presentations of that ring sheaf. -/
private theorem overFunctor_commRingSheafTensorIso_raw_naturality
    (R : Sheaf J CommRingCat.{u}) (U : C)
    {M₁ M₂ N₁ N₂ : SheafOfModules (commRingSheafToRingSheaf R)}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map
        ((PresheafOfModules.sheafification
          (𝟙 (commRingSheafToRingSheaf R).obj)).map
          (PresheafOfModules.Monoidal.tensorHom
            (R := R.obj) f.val g.val)) ≫
      ((overFunctor_sheafificationComparisonIso
          (R := commRingSheafToRingSheaf R) U
          (PresheafOfModules.Monoidal.tensorObj
            (R := R.obj) M₂.val N₂.val)).inv ≫
        (PresheafOfModules.sheafification
          (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map
          (PresheafOfModules.pushforward₀_tensorIso
            (F := Over.forget U) M₂.val N₂.val).hom) =
    ((overFunctor_sheafificationComparisonIso
          (R := commRingSheafToRingSheaf R) U
          (PresheafOfModules.Monoidal.tensorObj
            (R := R.obj) M₁.val N₁.val)).inv ≫
        (PresheafOfModules.sheafification
          (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map
          (PresheafOfModules.pushforward₀_tensorIso
            (F := Over.forget U) M₁.val N₁.val).hom) ≫
      (PresheafOfModules.sheafification
        (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map
        (PresheafOfModules.Monoidal.tensorHom
          (R := (commRingSheafOver R U).obj)
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map f).val
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map g).val) := by
  have hcomp := overFunctor_sheafificationComparison_inv_naturality
    (R := commRingSheafToRingSheaf R) U
    (PresheafOfModules.Monoidal.tensorHom (R := R.obj) f.val g.val)
  have hpre := overFunctor_pushforward₀_tensorIso_naturality R U f g
  have hsheaf := map_comp_eq_of_eq
    (PresheafOfModules.sheafification
      (𝟙 ((commRingSheafToRingSheaf R).over U).obj)) _ _ _ _ hpre
  exact paste_comp_eq _ _ _ _ _ _ _ hcomp hsheaf

private theorem commRingSheafTensorMap_over_eq
    (R : Sheaf J CommRingCat.{u}) (U : C)
    {M₁ M₂ N₁ N₂ : SheafOfModules (commRingSheafToRingSheaf R)}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    commRingSheafTensorMap (commRingSheafOver R U)
        ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map f)
        ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map g) =
      (PresheafOfModules.sheafification
        (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map
        (PresheafOfModules.Monoidal.tensorHom
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map f).val
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map g).val) := by
  rfl

/-- On an over-site, the concrete tensor comparison is natural in both
module factors. -/
theorem overFunctor_commRingSheafTensorIso_naturality
    (R : Sheaf J CommRingCat.{u}) (U : C)
    {M₁ M₂ N₁ N₂ : SheafOfModules (commRingSheafToRingSheaf R)}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map
        (commRingSheafTensorMap R f g) ≫
          (overFunctor_commRingSheafTensorIso R U M₂ N₂).hom =
      (overFunctor_commRingSheafTensorIso R U M₁ N₁).hom ≫
        commRingSheafTensorMap (commRingSheafOver R U)
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map f)
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map g) := by
  erw [commRingSheafTensorMap_eq_sheafification R f g,
    overFunctor_commRingSheafTensorIso_hom_eq,
    overFunctor_commRingSheafTensorIso_hom_eq,
    commRingSheafTensorMap_over_eq]
  erw [overFunctor_commRingSheafTensorIso_raw_naturality R U f g]
  rfl

/-- Tensoring sheaves of modules on the right is additive over an arbitrary
commutative-ring sheaf. -/
noncomputable instance commRingSheafTensorRight_additive
    (R : Sheaf J CommRingCat.{u})
    (N : SheafOfModules (commRingSheafToRingSheaf R)) :
    (commRingSheafTensorRight R N).Additive where
  map_add {M M'} f g := by
    let F := PresheafOfModules.sheafification
      (𝟙 (commRingSheafToRingSheaf R).obj)
    change F.map
        (PresheafOfModules.Monoidal.tensorHom (f.val + g.val) (𝟙 N.val)) =
      F.map (PresheafOfModules.Monoidal.tensorHom f.val (𝟙 N.val)) +
        F.map (PresheafOfModules.Monoidal.tensorHom g.val (𝟙 N.val))
    erw [presheafTensorHom_add_left]
    exact F.map_add

/-- The presheaf-level right unit comparison for module sheaves over a
commutative-ring sheaf. -/
noncomputable def commRingSheafTensorUnitRightRawIso
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules (commRingSheafToRingSheaf R)) :
    PresheafOfModules.Monoidal.tensorObj (R := R.obj)
      M.val (SheafOfModules.unit (commRingSheafToRingSheaf R)).val ≅ M.val := by
  let M' : PresheafOfModules (commRingSheafToRingSheaf R).obj := M.val
  change PresheafOfModules.Monoidal.tensorObj (R := R.obj) M'
    (PresheafOfModules.unit (R.obj ⋙ forget₂ CommRingCat RingCat)) ≅ M'
  letI : MonoidalCategory
      (PresheafOfModules (commRingSheafToRingSheaf R).obj) :=
    PresheafOfModules.monoidalCategory
  exact ρ_ M'

/-- Tensoring a module sheaf on the right by the structure module is the
identity, after sheafification. -/
noncomputable def commRingSheafTensorUnitRightIso
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules (commRingSheafToRingSheaf R)) :
    commRingSheafTensor R M (SheafOfModules.unit (commRingSheafToRingSheaf R)) ≅ M := by
  let F := PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheafToRingSheaf R).obj)
  letI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  exact F.mapIso (commRingSheafTensorUnitRightRawIso R M) ≪≫
    @asIso _ _ _ _ _ (NatIso.isIso_app_of_isIso adj.counit M)

/-- The right tensor functor by the structure module is naturally the
identity functor. -/
noncomputable def commRingSheafTensorRightUnitIso
    (R : Sheaf J CommRingCat.{u}) :
    commRingSheafTensorRight R (SheafOfModules.unit (commRingSheafToRingSheaf R)) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => commRingSheafTensorUnitRightIso R M) (by
    intro M M' f
    let F := PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheafToRingSheaf R).obj)
    letI : IsIso adj.counit := by
      dsimp [adj]
      infer_instance
    let M₀ : PresheafOfModules (commRingSheafToRingSheaf R).obj := M.val
    let M₁ : PresheafOfModules (commRingSheafToRingSheaf R).obj := M'.val
    let f₀ : M₀ ⟶ M₁ := f.val
    let U : PresheafOfModules (commRingSheafToRingSheaf R).obj :=
      PresheafOfModules.unit (R.obj ⋙ forget₂ CommRingCat RingCat)
    letI : MonoidalCategory
        (PresheafOfModules (commRingSheafToRingSheaf R).obj) :=
      PresheafOfModules.monoidalCategory
    have hraw : PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U) ≫ (ρ_ M₁).hom =
        (ρ_ M₀).hom ≫ f₀ :=
      rightUnitor_naturality f₀
    change F.map (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U)) ≫
        (F.map (ρ_ M₁).hom ≫ adj.counit.app M') =
      (F.map (ρ_ M₀).hom ≫ adj.counit.app M) ≫ f
    have hcounit : F.map f₀ ≫ adj.counit.app M' = adj.counit.app M ≫ f := by
      change F.map f.val ≫ adj.counit.app M' = adj.counit.app M ≫ f
      exact adj.counit.naturality f
    calc
      F.map (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U)) ≫
          (F.map (ρ_ M₁).hom ≫ adj.counit.app M') =
          (F.map (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U)) ≫
            F.map (ρ_ M₁).hom) ≫ adj.counit.app M' := (Category.assoc _ _ _).symm
      _ = F.map (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U) ≫
            (ρ_ M₁).hom) ≫ adj.counit.app M' :=
          congrArg (fun q => q ≫ adj.counit.app M')
            (F.map_comp (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U)) (ρ_ M₁).hom).symm
      _ = F.map ((ρ_ M₀).hom ≫ f₀) ≫ adj.counit.app M' :=
          congrArg (fun q => F.map q ≫ adj.counit.app M') hraw
      _ = (F.map (ρ_ M₀).hom ≫ F.map f₀) ≫ adj.counit.app M' :=
          congrArg (fun q => q ≫ adj.counit.app M') (F.map_comp (ρ_ M₀).hom f₀)
      _ = F.map (ρ_ M₀).hom ≫ (F.map f₀ ≫ adj.counit.app M') := Category.assoc _ _ _
      _ = F.map (ρ_ M₀).hom ≫ (adj.counit.app M ≫ f) := by
        rw [hcounit]
        rfl
      _ = (F.map (ρ_ M₀).hom ≫ adj.counit.app M) ≫ f := (Category.assoc _ _ _).symm)

/-- A locally trivial twist has a right tensor functor naturally isomorphic
to the identity over the chosen site. -/
noncomputable def commRingSheafTensorRightIsoUnit
    (R : Sheaf J CommRingCat.{u})
    {L : SheafOfModules (commRingSheafToRingSheaf R)}
    (e : L ≅ SheafOfModules.unit (commRingSheafToRingSheaf R)) :
    commRingSheafTensorRight R L ≅ 𝟭 _ :=
  commRingSheafTensorRightCongr R e ≪≫ commRingSheafTensorRightUnitIso R

/-- Tensoring by a locally trivial module sheaf preserves finite limits. -/
theorem commRingSheafTensorRight_preservesFiniteLimits_of_iso_unit
    (R : Sheaf J CommRingCat.{u})
    {L : SheafOfModules (commRingSheafToRingSheaf R)}
    (e : L ≅ SheafOfModules.unit (commRingSheafToRingSheaf R)) :
    PreservesFiniteLimits (commRingSheafTensorRight R L) :=
  preservesFiniteLimits_of_natIso (commRingSheafTensorRightIsoUnit R e).symm

/-- Tensoring by a locally trivial module sheaf preserves finite colimits. -/
theorem commRingSheafTensorRight_preservesFiniteColimits_of_iso_unit
    (R : Sheaf J CommRingCat.{u})
    {L : SheafOfModules (commRingSheafToRingSheaf R)}
    (e : L ≅ SheafOfModules.unit (commRingSheafToRingSheaf R)) :
    PreservesFiniteColimits (commRingSheafTensorRight R L) :=
  preservesFiniteColimits_of_natIso (commRingSheafTensorRightIsoUnit R e).symm

/-- Tensoring a short exact sequence by a locally trivial module sheaf keeps
it short exact.  This is the local exactness input for Voisin's projective
twist. -/
theorem commRingSheafTensor_shortExact_of_iso_unit
    (R : Sheaf J CommRingCat.{u})
    {S : ShortComplex (SheafOfModules (commRingSheafToRingSheaf R))}
    (hS : S.ShortExact)
    {L : SheafOfModules (commRingSheafToRingSheaf R)}
    (e : L ≅ SheafOfModules.unit (commRingSheafToRingSheaf R)) :
    letI : Functor.PreservesZeroMorphisms (commRingSheafTensorRight R L) :=
      Functor.preservesZeroMorphisms_of_iso (commRingSheafTensorRightIsoUnit R e).symm
    letI : PreservesFiniteLimits (commRingSheafTensorRight R L) :=
      commRingSheafTensorRight_preservesFiniteLimits_of_iso_unit R e
    letI : PreservesFiniteColimits (commRingSheafTensorRight R L) :=
      commRingSheafTensorRight_preservesFiniteColimits_of_iso_unit R e
    (S.map (commRingSheafTensorRight R L)).ShortExact := by
  letI : Functor.PreservesZeroMorphisms (commRingSheafTensorRight R L) :=
    Functor.preservesZeroMorphisms_of_iso (commRingSheafTensorRightIsoUnit R e).symm
  letI : PreservesFiniteLimits (commRingSheafTensorRight R L) :=
    commRingSheafTensorRight_preservesFiniteLimits_of_iso_unit R e
  letI : PreservesFiniteColimits (commRingSheafTensorRight R L) :=
    commRingSheafTensorRight_preservesFiniteColimits_of_iso_unit R e
  exact hS.map_of_exact (commRingSheafTensorRight R L)

end SheafOfModules

/-- Naturality of the restriction comparison for the concrete tensor product
of scheme modules. -/
theorem schemeModuleTensorOverIso_naturality {X : Scheme.{u}} (U : X.Opens)
    {M₁ M₂ N₁ N₂ : X.Modules} (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).map
        (schemeModuleTensorMap f g) ≫
          (schemeModuleTensorOverIso U M₂ N₂).hom =
      (schemeModuleTensorOverIso U M₁ N₁).hom ≫
        SheafOfModules.commRingSheafTensorMap
          (SheafOfModules.commRingSheafOver X.sheaf U)
          ((SheafOfModules.overFunctor X.ringCatSheaf U).map f)
          ((SheafOfModules.overFunctor X.ringCatSheaf U).map g) := by
  exact SheafOfModules.overFunctor_commRingSheafTensorIso_naturality
    X.sheaf U f g

/-- A morphism of scheme modules which becomes an isomorphism after restriction
to an open also becomes an isomorphism on the corresponding over-site. -/
theorem overFunctorMap_isIso_of_restrictMap_isIso {X : Scheme.{u}}
    (U : X.Opens) {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] :
    IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map f) := by
  let E := Scheme.Modules.overEquiv U
  let H := SheafOfModules.overFunctor X.ringCatSheaf U
  let n := Scheme.Modules.overFunctorEquiv U
  letI : IsIso (n.app M).hom := by
    dsimp [n]
    infer_instance
  letI : IsIso (n.app N).hom := by
    dsimp [n]
    infer_instance
  have h : E.functor.map (H.map f) ≫ (n.app N).hom =
      (n.app M).hom ≫ (Scheme.Modules.restrictFunctor U.ι).map f :=
    n.hom.naturality f
  haveI : IsIso (E.functor.map (H.map f) ≫ (n.app N).hom) := by
    rw [h]
    infer_instance
  haveI : IsIso (E.functor.map (H.map f)) :=
    IsIso.of_isIso_comp_right (E.functor.map (H.map f)) (n.app N).hom
  exact isIso_of_reflects_iso (H.map f) E.functor

/-- Restricting a tensor map to an open is an isomorphism when both factor
maps become isomorphisms there. -/
theorem restrict_schemeModuleTensorMap_isIso_of_isIso {X : Scheme.{u}}
    (U : X.Opens) {M₁ M₂ N₁ N₂ : X.Modules}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)]
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map g)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (schemeModuleTensorMap f g)) := by
  letI : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map f) :=
    overFunctorMap_isIso_of_restrictMap_isIso U f
  letI : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map g) :=
    overFunctorMap_isIso_of_restrictMap_isIso U g
  let ef := asIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map f)
  let eg := asIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map g)
  let eTensor := SheafOfModules.commRingSheafTensorMapIso
    (SheafOfModules.commRingSheafOver X.sheaf U) ef eg
  letI : IsIso (SheafOfModules.commRingSheafTensorMap
      (SheafOfModules.commRingSheafOver X.sheaf U)
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map f)
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map g)) := by
    exact eTensor.isIso_hom
  have h := schemeModuleTensorOverIso_naturality U f g
  letI : IsIso (schemeModuleTensorOverIso U M₂ N₂).hom :=
    (schemeModuleTensorOverIso U M₂ N₂).isIso_hom
  letI : IsIso (schemeModuleTensorOverIso U M₁ N₁).hom :=
    (schemeModuleTensorOverIso U M₁ N₁).isIso_hom
  haveI : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map
      (schemeModuleTensorMap f g) ≫ (schemeModuleTensorOverIso U M₂ N₂).hom) := by
    rw [h]
    change IsIso ((schemeModuleTensorOverIso U M₁ N₁).hom ≫ eTensor.hom)
    exact ((schemeModuleTensorOverIso U M₁ N₁) ≪≫ eTensor).isIso_hom
  haveI : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map
      (schemeModuleTensorMap f g)) :=
    IsIso.of_isIso_comp_right _ (schemeModuleTensorOverIso U M₂ N₂).hom
  let E := Scheme.Modules.overEquiv U
  let H := SheafOfModules.overFunctor X.ringCatSheaf U
  let n := Scheme.Modules.overFunctorEquiv U
  letI : IsIso (n.app (schemeModuleTensor M₁ N₁)).hom := by
    dsimp [n]
    infer_instance
  letI : IsIso (n.app (schemeModuleTensor M₂ N₂)).hom := by
    dsimp [n]
    infer_instance
  have hn : E.functor.map (H.map (schemeModuleTensorMap f g)) ≫
      (n.app (schemeModuleTensor M₂ N₂)).hom =
    (n.app (schemeModuleTensor M₁ N₁)).hom ≫
      (Scheme.Modules.restrictFunctor U.ι).map (schemeModuleTensorMap f g) :=
    n.hom.naturality (schemeModuleTensorMap f g)
  haveI : IsIso ((n.app (schemeModuleTensor M₁ N₁)).hom ≫
      (Scheme.Modules.restrictFunctor U.ι).map (schemeModuleTensorMap f g)) := by
    rw [← hn]
    infer_instance
  apply IsIso.of_isIso_comp_left (n.app (schemeModuleTensor M₁ N₁)).hom

/-- Restricting a right tensor product to an open is naturally isomorphic to
first restricting both factors and then tensoring on the over-site. -/
noncomputable def schemeModuleTensorRightOverIso {X : Scheme.{u}}
    (U : X.Opens) (T : X.Modules) :
    schemeModuleTensorRight T ⋙
        SheafOfModules.overFunctor X.ringCatSheaf U ≅
      SheafOfModules.overFunctor X.ringCatSheaf U ⋙
        SheafOfModules.commRingSheafTensorRight
          (SheafOfModules.commRingSheafOver X.sheaf U)
          ((SheafOfModules.overFunctor X.ringCatSheaf U).obj T) :=
  NatIso.ofComponents (fun M => schemeModuleTensorOverIso U M T) (by
    intro M M' f
    have h := schemeModuleTensorOverIso_naturality U f (𝟙 T)
    erw [(SheafOfModules.overFunctor X.ringCatSheaf U).map_id T] at h
    exact h)

/-- Restriction after tensoring by a module trivial on an open is naturally
isomorphic to ordinary restriction. -/
noncomputable def schemeModuleTensorRestrictNatIsoOfLocalTrivialization
    {X : Scheme.{u}} (U : X.Opens) (T : X.Modules)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) :
    schemeModuleTensorRight T ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι := by
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  let E := (Scheme.Modules.overEquiv U).functor
  let G := SheafOfModules.commRingSheafTensorRight
    (SheafOfModules.commRingSheafOver X.sheaf U) (F.obj T)
  let A := schemeModuleTensorRight T
  let eUnit : G ≅ 𝟭 _ :=
    SheafOfModules.commRingSheafTensorRightIsoUnit
      (SheafOfModules.commRingSheafOver X.sheaf U) eT
  exact
    Functor.isoWhiskerLeft A (Scheme.Modules.overFunctorEquiv U).symm ≪≫
      (Functor.associator A F E).symm ≪≫
      Functor.isoWhiskerRight (schemeModuleTensorRightOverIso U T) E ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft F eUnit) E ≪≫
      Functor.isoWhiskerRight (Functor.rightUnitor F) E ≪≫
      Scheme.Modules.overFunctorEquiv U

/-- Componentwise restriction isomorphism on an open where the right tensor
factor is trivial. -/
noncomputable def schemeModuleTensorRestrictIsoOfLocalTrivialization
    {X : Scheme.{u}} (U : X.Opens) (M T : X.Modules)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) :
    (Scheme.Modules.restrictFunctor U.ι).obj (schemeModuleTensor M T) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj M :=
  (schemeModuleTensorRestrictNatIsoOfLocalTrivialization U T eT).app M

/-- Naturality of the local restriction isomorphism in the untwisted tensor
factor. -/
theorem schemeModuleTensorRestrictIsoOfLocalTrivialization_naturality
    {X : Scheme.{u}} (U : X.Opens) {M N T : X.Modules}
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) (f : M ⟶ N) :
    (Scheme.Modules.restrictFunctor U.ι).map
        (schemeModuleTensorMap f (𝟙 T)) ≫
      (schemeModuleTensorRestrictIsoOfLocalTrivialization U N T eT).hom =
    (schemeModuleTensorRestrictIsoOfLocalTrivialization U M T eT).hom ≫
      (Scheme.Modules.restrictFunctor U.ι).map f := by
  exact
    (schemeModuleTensorRestrictNatIsoOfLocalTrivialization U T eT).hom.naturality f

/-- At a point of an open where the right tensor factor is trivial, tensoring
is naturally invisible on the underlying abelian-group stalk. -/
noncomputable def schemeModuleTensorStalkNatIsoOfLocalTrivialization
    {X : Scheme.{u}} (U : X.Opens) (x : U) (T : X.Modules)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) :
    schemeModuleTensorRight T ⋙ Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι x) ≅
      Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι x) := by
  let A := schemeModuleTensorRight T
  let R := Scheme.Modules.restrictFunctor U.ι
  let H := Scheme.Modules.toPresheaf (U : Scheme) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let S := Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι x)
  let n : R ⋙ H ≅ S := Scheme.Modules.restrictStalkNatIso U.ι x
  exact
    Functor.isoWhiskerLeft A n.symm ≪≫
      (Functor.associator A R H).symm ≪≫
      Functor.isoWhiskerRight
        (schemeModuleTensorRestrictNatIsoOfLocalTrivialization U T eT) H ≪≫ n

/-- Component of the local stalk isomorphism. -/
noncomputable def schemeModuleTensorStalkIsoOfLocalTrivialization
    {X : Scheme.{u}} (U : X.Opens) (x : U)
    (M T : X.Modules)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) :
    (schemeModuleTensor M T).presheaf.stalk (U.ι x) ≅
      M.presheaf.stalk (U.ι x) :=
  (schemeModuleTensorStalkNatIsoOfLocalTrivialization U x T eT).app M

/-- Naturality of the local stalk isomorphism in the untwisted factor. -/
theorem schemeModuleTensorStalkIsoOfLocalTrivialization_naturality
    {X : Scheme.{u}} (U : X.Opens) (x : U) {M N T : X.Modules}
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) (f : M ⟶ N) :
    (Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι x)).map
        (schemeModuleTensorMap f (𝟙 T)) ≫
      (schemeModuleTensorStalkIsoOfLocalTrivialization U x N T eT).hom =
    (schemeModuleTensorStalkIsoOfLocalTrivialization U x M T eT).hom ≫
      (Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι x)).map f := by
  exact
    (schemeModuleTensorStalkNatIsoOfLocalTrivialization U x T eT).hom.naturality f

set_option linter.style.haveILetI false in
/-- If a module has zero stalk at a point and the tensor factor is trivial
on a neighborhood of that point, their tensor product also has zero stalk
there. -/
theorem schemeModuleTensor_stalk_subsingleton_of_localTrivialization
    {X : Scheme.{u}} (U : X.Opens) (x : U)
    (M T : X.Modules)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (hM : Subsingleton (M.presheaf.stalk (U.ι x))) :
    Subsingleton ((schemeModuleTensor M T).presheaf.stalk (U.ι x)) := by
  letI : Subsingleton (M.presheaf.stalk (U.ι x)) := hM
  let e := schemeModuleTensorStalkIsoOfLocalTrivialization U x M T eT
  constructor
  intro a b
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  exact Subsingleton.elim _ _

private lemma preservesZeroMorphisms_of_iso_explicit
    {C₁ : Type u₁} {D : Type u₂}
    [Category.{v₁} C₁] [Category.{v₂} D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms D]
    {F₁ F₂ : Functor C₁ D} (h : F₁.PreservesZeroMorphisms) (e : F₁ ≅ F₂) :
    F₂.PreservesZeroMorphisms where
  map_zero X Y := by
    rw [← cancel_epi (e.hom.app X), ← e.hom.naturality]
    rw [h.map_zero, zero_comp, comp_zero]

namespace SheafOfModules

variable {X : Scheme.{u}}

/-- A globally trivial scheme module restricts to the unit module on every
over-site.  The explicit transport records the canonical identification of
the two underlying over-site ring sheaves. -/
noncomputable def overFunctor_globalUnitIso
    {T : X.Modules} (U : X.Opens)
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)) := by
  exact commRingSheafOverToRingSheafTransport_globalUnitIso X.sheaf U eT

end SheafOfModules

set_option linter.style.haveILetI false in
/-- If the right tensor factor is trivial on an open, restricting the tensor
of any short exact sequence to that open is short exact.  This is the generic
form of the local calculation used below for the closed-immersion ideal
sequence. -/
theorem shortComplex_tensor_over_shortExact_of_iso_unit
    {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (U : X.Opens) {T : X.Modules}
    (eU : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) :
    let F := SheafOfModules.overFunctor X.ringCatSheaf U
    let hF : F.PreservesZeroMorphisms :=
      SheafOfModules.overFunctor_preservesZeroMorphisms X.ringCatSheaf U
    (@ShortComplex.map _ _ _ _ _ _
      (S.map (schemeModuleTensorRight T)) F hF).ShortExact := by
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  let hF : F.PreservesZeroMorphisms :=
    SheafOfModules.overFunctor_preservesZeroMorphisms X.ringCatSheaf U
  let G := SheafOfModules.commRingSheafTensorRight
    (SheafOfModules.commRingSheafOver X.sheaf U) (F.obj T)
  let eFG : F ⋙ G ≅ F :=
    Functor.isoWhiskerLeft F
      (SheafOfModules.commRingSheafTensorRightIsoUnit
        (SheafOfModules.commRingSheafOver X.sheaf U) eU) ≪≫
      Functor.rightUnitor F
  let hFG : (F ⋙ G).PreservesZeroMorphisms :=
    preservesZeroMorphisms_of_iso_explicit hF eFG.symm
  let eTF : schemeModuleTensorRight T ⋙ F ≅ F ⋙ G :=
    schemeModuleTensorRightOverIso U T
  let hTF : (schemeModuleTensorRight T ⋙ F).PreservesZeroMorphisms :=
    preservesZeroMorphisms_of_iso_explicit hFG eTF.symm
  letI : F.PreservesZeroMorphisms := hF
  letI : (F ⋙ G).PreservesZeroMorphisms := hFG
  letI : (schemeModuleTensorRight T ⋙ F).PreservesZeroMorphisms := hTF
  have hSF := SheafOfModules.ShortComplex.shortExact_map_overFunctor
    X.ringCatSheaf U S hS
  have hSFG := SheafOfModules.commRingSheafTensor_shortExact_of_iso_unit
    (SheafOfModules.commRingSheafOver X.sheaf U) hSF eU
  let e := @ShortComplex.mapNatIso _ _ _ _ _ _ S _ _ hTF hFG eTF
  apply ShortComplex.shortExact_of_iso e.symm
  exact hSFG

/-- Tensoring by a module trivial on an open cover preserves every short
exact sequence. -/
theorem shortComplex_tensor_shortExact_of_coversTop_iso_unit
    {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    {T : X.Modules}
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j)))) :
    (S.map (schemeModuleTensorRight T)).ShortExact := by
  apply SheafOfModules.ShortComplex.shortExact_of_coversTop U hU
  intro j
  exact shortComplex_tensor_over_shortExact_of_iso_unit
    S hS (U j) (eU j)

/-- Tensoring by a module trivial on an open cover preserves finite limits.
For module sheaves, this is the left-exact half of exactness of tensoring by
a line bundle. -/
theorem schemeModuleTensorRight_preservesFiniteLimits_of_coversTop_iso_unit
    {X : Scheme.{u}} {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    {T : X.Modules}
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j)))) :
    PreservesFiniteLimits (schemeModuleTensorRight T) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (schemeModuleTensorRight T)).mpr
  intro S hS
  have hST := shortComplex_tensor_shortExact_of_coversTop_iso_unit
    S hS U hU eU
  exact ⟨hST.exact, hST.mono_f⟩

/-- Tensoring by a module trivial on an open cover preserves finite
colimits.  Together with the preceding theorem this packages exactness of
tensoring by a line bundle in the form needed by the Ext construction. -/
theorem schemeModuleTensorRight_preservesFiniteColimits_of_coversTop_iso_unit
    {X : Scheme.{u}} {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    {T : X.Modules}
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j)))) :
    PreservesFiniteColimits (schemeModuleTensorRight T) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (schemeModuleTensorRight T)).mpr
  intro S hS
  have hST := shortComplex_tensor_shortExact_of_coversTop_iso_unit
    S hS U hU eU
  exact ⟨hST.exact, hST.epi_g⟩

section

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- Explicit-cover form of preservation of a finite biproduct by tensoring.
It is the decomposition interface used for a projective twist which is only
locally trivial. -/
noncomputable def schemeModuleTensorRightBiproductIso_of_coversTop_iso_unit
    {X : Scheme.{u}} {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    {T : X.Modules}
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j))))
    {J : Type u} [Fintype J] (M : J → X.Modules) :
    (⨁ fun j ↦ schemeModuleTensor (M j) T) ≅
      schemeModuleTensor (⨁ M) T := by
  letI : PreservesFiniteLimits (schemeModuleTensorRight T) :=
    schemeModuleTensorRight_preservesFiniteLimits_of_coversTop_iso_unit
      U hU eU
  exact schemeModuleTensorRightBiproductIso T M

end

/-- After passing to an open site on which the twist is trivial, the
closed-immersion ideal sequence remains short exact after tensoring by that
local twist.  The two maps are written with their preservation-of-zero proofs
explicitly so that this statement does not require a global exactness
hypothesis for the twist on `X`. -/
theorem closedImmersionModulePushforwardSequence_overTensor_shortExact_of_iso_unit
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens)
    {T : X.Modules}
    (eU : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) :
    let F := SheafOfModules.overFunctor X.ringCatSheaf U
    let G := SheafOfModules.commRingSheafTensorRight
      (SheafOfModules.commRingSheafOver X.sheaf U) (F.obj T)
    let hF : F.PreservesZeroMorphisms :=
      SheafOfModules.overFunctor_preservesZeroMorphisms X.ringCatSheaf U
    let hG : G.PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_iso
        (SheafOfModules.commRingSheafTensorRightIsoUnit
          (SheafOfModules.commRingSheafOver X.sheaf U) eU).symm
    (@ShortComplex.map _ _ _ _ _ _
      (@ShortComplex.map _ _ _ _ _ _
        (closedImmersionModulePushforwardSequence i) F hF) G hG).ShortExact := by
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  let G := SheafOfModules.commRingSheafTensorRight
      (SheafOfModules.commRingSheafOver X.sheaf U) (F.obj T)
  let hF : F.PreservesZeroMorphisms :=
    SheafOfModules.overFunctor_preservesZeroMorphisms X.ringCatSheaf U
  let hG : G.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_iso
      (SheafOfModules.commRingSheafTensorRightIsoUnit
        (SheafOfModules.commRingSheafOver X.sheaf U) eU).symm
  letI : F.PreservesZeroMorphisms := hF
  letI : G.PreservesZeroMorphisms := hG
  letI : PreservesFiniteLimits G :=
    SheafOfModules.commRingSheafTensorRight_preservesFiniteLimits_of_iso_unit
      (SheafOfModules.commRingSheafOver X.sheaf U) eU
  letI : PreservesFiniteColimits G :=
    SheafOfModules.commRingSheafTensorRight_preservesFiniteColimits_of_iso_unit
      (SheafOfModules.commRingSheafOver X.sheaf U) eU
  have hS := closedImmersionModulePushforwardSequence_shortExact i
  have hSF := SheafOfModules.ShortComplex.shortExact_map_overFunctor
    X.ringCatSheaf U (closedImmersionModulePushforwardSequence i) hS
  have hSFG := SheafOfModules.commRingSheafTensor_shortExact_of_iso_unit
    (SheafOfModules.commRingSheafOver X.sheaf U) hSF eU
  exact hSFG

/-- If a twist is trivial on an open, then the restriction of the actual
globally defined twisted ideal sequence to that open is short exact. -/
theorem closedImmersionIdealTwistSequence_over_shortExact_of_iso_unit
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) {T : X.Modules}
    (eU : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) :
    let F := SheafOfModules.overFunctor X.ringCatSheaf U
    let hF : F.PreservesZeroMorphisms :=
      SheafOfModules.overFunctor_preservesZeroMorphisms X.ringCatSheaf U
    (@ShortComplex.map _ _ _ _ _ _
      (closedImmersionIdealTwistSequence i T) F hF).ShortExact := by
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  let hF : F.PreservesZeroMorphisms :=
    SheafOfModules.overFunctor_preservesZeroMorphisms X.ringCatSheaf U
  let G := SheafOfModules.commRingSheafTensorRight
    (SheafOfModules.commRingSheafOver X.sheaf U) (F.obj T)
  let eFG : F ⋙ G ≅ F :=
    Functor.isoWhiskerLeft F
      (SheafOfModules.commRingSheafTensorRightIsoUnit
        (SheafOfModules.commRingSheafOver X.sheaf U) eU) ≪≫
      Functor.rightUnitor F
  let hFG : (F ⋙ G).PreservesZeroMorphisms :=
    preservesZeroMorphisms_of_iso_explicit hF eFG.symm
  let eTF : schemeModuleTensorRight T ⋙ F ≅ F ⋙ G :=
    schemeModuleTensorRightOverIso U T
  let hTF : (schemeModuleTensorRight T ⋙ F).PreservesZeroMorphisms :=
    preservesZeroMorphisms_of_iso_explicit hFG eTF.symm
  have hlocal :=
    closedImmersionModulePushforwardSequence_overTensor_shortExact_of_iso_unit
      i U eU
  let e := @ShortComplex.mapNatIso _ _ _ _ _ _
    (closedImmersionModulePushforwardSequence i) _ _ hTF hFG eTF
  apply ShortComplex.shortExact_of_iso e.symm
  exact hlocal

/-- A twist which is trivial on an open cover makes the globally defined
twisted ideal sequence short exact.  This is the local-to-global exactness
statement needed for projective line-bundle twists. -/
theorem closedImmersionIdealTwistSequence_shortExact_of_coversTop_iso_unit
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    {T : X.Modules}
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j)))) :
    (closedImmersionIdealTwistSequence i T).ShortExact := by
  apply SheafOfModules.ShortComplex.shortExact_of_coversTop U hU
  intro j
  exact closedImmersionIdealTwistSequence_over_shortExact_of_iso_unit
    i (U j) (eU j)

/-- A globally trivial twist supplies the local unit identification needed by
the over-site tensor exactness theorem. -/
theorem closedImmersionModulePushforwardSequence_overTensor_shortExact_of_global_iso_unit
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens)
    {T : X.Modules}
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf) :
    ∃ eU : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)),
      let F := SheafOfModules.overFunctor X.ringCatSheaf U
      let G := SheafOfModules.commRingSheafTensorRight
        (SheafOfModules.commRingSheafOver X.sheaf U) (F.obj T)
      let hF : F.PreservesZeroMorphisms :=
        SheafOfModules.overFunctor_preservesZeroMorphisms X.ringCatSheaf U
      let hG : G.PreservesZeroMorphisms :=
        Functor.preservesZeroMorphisms_of_iso
          (SheafOfModules.commRingSheafTensorRightIsoUnit
            (SheafOfModules.commRingSheafOver X.sheaf U) eU).symm
      (@ShortComplex.map _ _ _ _ _ _
        (@ShortComplex.map _ _ _ _ _ _
          (closedImmersionModulePushforwardSequence i) F hF) G hG).ShortExact := by
  refine ⟨SheafOfModules.overFunctor_globalUnitIso U eT, ?_⟩
  exact closedImmersionModulePushforwardSequence_overTensor_shortExact_of_iso_unit
    i U (SheafOfModules.overFunctor_globalUnitIso U eT)

end PfaffianDescent
