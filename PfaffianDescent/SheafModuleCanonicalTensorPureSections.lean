import PfaffianDescent.SchemeModuleLocallyRankOneTensor

/-! Actual pure tensor sections and their canonical unit-chart coefficient.
All maps use the original sheafification unit, tensor maps and counit. No
pairing, pure-section comparison or multiplicativity premise is supplied.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SheafOfModules
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open scoped TensorProduct
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual pointwise pure tensor sent through the original unit into
its SAME sheafified tensor product. -/
def commRingSheafTensorPureSection
    (M N : SheafOfModules (commRingSheafToRingSheaf R)) (V : Cᵒᵖ)
    (m : M.val.obj V) (n : N.val.obj V) : (commRingSheafTensor R M N).val.obj V :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app
    (PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val)).app V
      (m ⊗ₜ[R.obj.obj V] n)

/-- Actual tensor-map compatibility follows directly from the original
sheafification-unit naturality, on the original pure tensor. -/
theorem commRingSheafTensorPureSection_map
    {M₁ M₂ N₁ N₂ : SheafOfModules (commRingSheafToRingSheaf R)}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) (V : Cᵒᵖ)
    (m : M₁.val.obj V) (n : N₁.val.obj V) :
    (commRingSheafTensorMap R f g).val.app V
        (commRingSheafTensorPureSection R M₁ N₁ V m n) =
      commRingSheafTensorPureSection R M₂ N₂ V (f.val.app V m) (g.val.app V n) := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheafToRingSheaf R).obj)
  let t := PresheafOfModules.Monoidal.tensorHom (R := R.obj) f.val g.val
  have h := congrArg (fun k => (k.app V).hom (m ⊗ₜ[R.obj.obj V] n))
    (A.unit.naturality t).symm
  change (commRingSheafTensorMap R f g).val.app V
      (commRingSheafTensorPureSection R M₁ N₁ V m n) =
    commRingSheafTensorPureSection R M₂ N₂ V (f.val.app V m) (g.val.app V n) at h
  exact h

/-- Actual pure tensor restriction is the pure tensor of the two ORIGINAL
restricted sections. This is unit naturality and tensor restriction. -/
theorem commRingSheafTensorPureSection_restrict
    (M N : SheafOfModules (commRingSheafToRingSheaf R))
    {V W : Cᵒᵖ} (f : V ⟶ W) (m : M.val.obj V) (n : N.val.obj V) :
    (commRingSheafTensor R M N).val.map f
        (commRingSheafTensorPureSection R M N V m n) =
      commRingSheafTensorPureSection R M N W (M.val.map f m) (N.val.map f n) := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheafToRingSheaf R).obj)
  let T := PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
  have h := (PresheafOfModules.naturality_apply (A.unit.app T) f
    (m ⊗ₜ[R.obj.obj V] n)).symm
  change (commRingSheafTensor R M N).val.map f
      (commRingSheafTensorPureSection R M N V m n) =
    commRingSheafTensorPureSection R M N W (M.val.map f m) (N.val.map f n) at h
  exact h

/-- The ACTUAL right-unit Iso has the actual scalar product on pure
sections; the original counit/adjunction law proves this. -/
theorem commRingSheafTensorUnitRightIso_pureSection
    (M : SheafOfModules (commRingSheafToRingSheaf R)) (V : Cᵒᵖ)
    (m : M.val.obj V) (r : R.obj.obj V) :
    (commRingSheafTensorUnitRightIso R M).hom.val.app V
        (commRingSheafTensorPureSection R M
          (SheafOfModules.unit (commRingSheafToRingSheaf R)) V m r) = r • m := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheafToRingSheaf R).obj)
  let T := PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val
    (SheafOfModules.unit (commRingSheafToRingSheaf R)).val
  let q := (commRingSheafTensorUnitRightRawIso R M).hom
  have h : A.unit.app T ≫ (commRingSheafTensorUnitRightIso R M).hom.val = q := by
    have he : (A.homEquiv T M).symm q = (commRingSheafTensorUnitRightIso R M).hom :=
      A.homEquiv_counit T M q
    exact (congrArg (A.homEquiv T M) he).symm.trans ((A.homEquiv T M).apply_symm_apply q)
  have hv := congrArg (fun k => (k.app V).hom (m ⊗ₜ[R.obj.obj V] r)) h
  change (commRingSheafTensorUnitRightIso R M).hom.val.app V
      (commRingSheafTensorPureSection R M
        (SheafOfModules.unit (commRingSheafToRingSheaf R)) V m r) = q.app V (m ⊗ₜ[R.obj.obj V] r) at hv
  exact hv.trans (ModuleCat.MonoidalCategory.rightUnitor_hom_apply
    (R := R.obj.obj V) (M := M.val.obj V) m r)

/-- Canonical product of the two actual unit charts, using the SAME
original tensor map and original unit Iso. -/
def commRingSheafTensorCanonicalUnitIso
    {M N : SheafOfModules (commRingSheafToRingSheaf R)}
    (eM : M ≅ SheafOfModules.unit (commRingSheafToRingSheaf R))
    (eN : N ≅ SheafOfModules.unit (commRingSheafToRingSheaf R)) :
    commRingSheafTensor R M N ≅ SheafOfModules.unit (commRingSheafToRingSheaf R) :=
  commRingSheafTensorMapIso R eM eN ≪≫
    commRingSheafTensorUnitRightIso R (SheafOfModules.unit (commRingSheafToRingSheaf R))

/-- The canonical tensor chart is literally multiplication of the two
actual original coefficients, including all sheafification normalization. -/
theorem commRingSheafTensorCanonicalUnitIso_pureSection
    {M N : SheafOfModules (commRingSheafToRingSheaf R)}
    (eM : M ≅ SheafOfModules.unit (commRingSheafToRingSheaf R))
    (eN : N ≅ SheafOfModules.unit (commRingSheafToRingSheaf R))
    (V : Cᵒᵖ) (m : M.val.obj V) (n : N.val.obj V) :
    (commRingSheafTensorCanonicalUnitIso R eM eN).hom.val.app V
        (commRingSheafTensorPureSection R M N V m n) =
      @HMul.hMul (R.obj.obj V) (R.obj.obj V) (R.obj.obj V) _
        (eM.hom.val.app V m) (eN.hom.val.app V n) := by
  change (commRingSheafTensorUnitRightIso R (SheafOfModules.unit (commRingSheafToRingSheaf R))).hom.val.app V
      ((commRingSheafTensorMap R eM.hom eN.hom).val.app V
        (commRingSheafTensorPureSection R M N V m n)) = _
  rw [commRingSheafTensorPureSection_map, commRingSheafTensorUnitRightIso_pureSection]
  exact @mul_comm (R.obj.obj V) _ (eN.hom.val.app V n) (eM.hom.val.app V m)

end PfaffianDescent.SheafOfModules
