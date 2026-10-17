import PfaffianDescent.CubicPointTraceFieldBaseChangeDiagonal
import PfaffianDescent.CubicPointTraceFieldBaseChangeAffine

/-! # The diagonal residue module as an actual structure-sheaf retract

The diagonal inclusion is the spectrum of tensor multiplication. The
canonical unit-to-pushforward map is identified with multiplication on
affine modules, and its explicit separability section is sheafified.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The actual tensor multiplication defining the diagonal point. -/
abbrev cubicPointTraceFieldBaseChangeDiagonalRingHom : (L ⊗[K] L) →+* L :=
  (Algebra.TensorProduct.lmul' K (S := L)).toRingHom

/-- The residue field with the module action of the diagonal tensor-ring map. -/
def cubicPointTraceFieldBaseChangeDiagonalResidueModule : ModuleCat (L ⊗[K] L) :=
  cubicPointTraceFieldBaseChangeAffineResidueModule
    (cubicPointTraceFieldBaseChangeDiagonalRingHom K L)

/-- The actual module quotient map for the diagonal component. -/
def cubicPointTraceFieldBaseChangeDiagonalModuleQuotient :
    ModuleCat.of (L ⊗[K] L) (L ⊗[K] L) ⟶
      cubicPointTraceFieldBaseChangeDiagonalResidueModule K L :=
  cubicPointTraceFieldBaseChangeAffineModuleQuotient
    (cubicPointTraceFieldBaseChangeDiagonalRingHom K L)

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The module section selecting the diagonal, constructed from separability. -/
def cubicPointTraceFieldBaseChangeDiagonalModuleSection :
    cubicPointTraceFieldBaseChangeDiagonalResidueModule K L ⟶
      ModuleCat.of (L ⊗[K] L) (L ⊗[K] L) := by
  exact @ModuleCat.ofHom (L ⊗[K] L) _
    (cubicPointTraceFieldBaseChangeDiagonalResidueModule K L) (L ⊗[K] L) _
    (ModuleCat.isModule (cubicPointTraceFieldBaseChangeDiagonalResidueModule K L)) _ _ {
    toFun := fun a => (show L from a) • cubicPointTraceFieldBaseChangeDiagonalProjector K L
    map_add' := fun a b => add_smul (show L from a) (show L from b) _
    map_smul' := fun t a => by
      change (Algebra.TensorProduct.lmul' K t * (show L from a)) •
        cubicPointTraceFieldBaseChangeDiagonalProjector K L =
          t * ((show L from a) • cubicPointTraceFieldBaseChangeDiagonalProjector K L)
      calc
        (Algebra.TensorProduct.lmul' K t * (show L from a)) •
            cubicPointTraceFieldBaseChangeDiagonalProjector K L =
          (show L from a) • (Algebra.TensorProduct.lmul' K t •
            cubicPointTraceFieldBaseChangeDiagonalProjector K L) := by
              rw [smul_smul, mul_comm]
        _ = (show L from a) •
            (t * cubicPointTraceFieldBaseChangeDiagonalProjector K L) :=
          congrArg (fun z => (show L from a) • z)
            (cubicPointTraceFieldBaseChangeDiagonalProjector_mul K L t).symm
        _ = t * ((show L from a) • cubicPointTraceFieldBaseChangeDiagonalProjector K L) :=
          (Algebra.mul_smul_comm _ _ _).symm }

@[simp]
theorem cubicPointTraceFieldBaseChangeDiagonalModuleSection_quotient :
    cubicPointTraceFieldBaseChangeDiagonalModuleSection K L ≫
      cubicPointTraceFieldBaseChangeDiagonalModuleQuotient K L = 𝟙 _ := by
  ext a
  change Algebra.TensorProduct.lmul' K
      ((show L from a) • cubicPointTraceFieldBaseChangeDiagonalProjector K L) = a
  rw [Algebra.smul_def, map_mul]
  change Algebra.TensorProduct.lmul' K ((show L from a) ⊗ₜ[K] 1) *
    Algebra.TensorProduct.lmul' K (cubicPointTraceFieldBaseChangeDiagonalProjector K L) = a
  rw [cubicPointTraceFieldBaseChangeDiagonalProjector_eval K L]
  simp

/-- Multiplication by the diagonal projector on the actual affine module. -/
def cubicPointTraceFieldBaseChangeDiagonalModuleProjector :
    ModuleCat.of (L ⊗[K] L) (L ⊗[K] L) ⟶
      ModuleCat.of (L ⊗[K] L) (L ⊗[K] L) :=
  cubicPointTraceFieldBaseChangeDiagonalModuleQuotient K L ≫
    cubicPointTraceFieldBaseChangeDiagonalModuleSection K L

theorem cubicPointTraceFieldBaseChangeDiagonalModuleProjector_apply (t : L ⊗[K] L) :
    cubicPointTraceFieldBaseChangeDiagonalModuleProjector K L t =
      t * cubicPointTraceFieldBaseChangeDiagonalProjector K L :=
  (cubicPointTraceFieldBaseChangeDiagonalProjector_mul K L t).symm

end

section ActualSheaf
variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The actual tensor-spectrum diagonal inclusion. -/
def cubicPointTraceFieldBaseChangeTensorDiagonal :
    Spec (.of L) ⟶ Spec (.of (L ⊗[K] L)) :=
  Spec.map (CommRingCat.ofHom (cubicPointTraceFieldBaseChangeDiagonalRingHom K L))

/-- The actual pushforward of the rational diagonal component's unit module. -/
def cubicPointTraceFieldBaseChangeDiagonalPushforward :
    (Spec (.of (L ⊗[K] L))).Modules :=
  cubicPointTraceFieldBaseChangeAffinePushforward
    (cubicPointTraceFieldBaseChangeDiagonalRingHom K L)

/-- The affine global sections of the actual diagonal pushforward, with
their actual tensor-ring action. -/
def cubicPointTraceFieldBaseChangeDiagonalPushforwardGammaIso :
    (moduleSpecΓFunctor (R := .of (L ⊗[K] L))).obj
      (cubicPointTraceFieldBaseChangeDiagonalPushforward K L) ≅
        cubicPointTraceFieldBaseChangeDiagonalResidueModule K L :=
  cubicPointTraceFieldBaseChangeAffinePushforwardGammaIso
    (cubicPointTraceFieldBaseChangeDiagonalRingHom K L)

instance cubicPointTraceFieldBaseChangeDiagonalPushforward_fromTilde_isIso :
    IsIso (Scheme.Modules.fromTildeΓ
      (R := .of (L ⊗[K] L)) (cubicPointTraceFieldBaseChangeDiagonalPushforward K L)) :=
  cubicPointTraceFieldBaseChangeAffinePushforward_fromTilde_isIso
    (cubicPointTraceFieldBaseChangeDiagonalRingHom K L)

/-- The diagonal residue module sheafifies to the actual point pushforward. -/
def cubicPointTraceFieldBaseChangeDiagonalTildeIso :
    (tilde.functor (.of (L ⊗[K] L))).obj
      (cubicPointTraceFieldBaseChangeDiagonalResidueModule K L) ≅
        cubicPointTraceFieldBaseChangeDiagonalPushforward K L :=
  cubicPointTraceFieldBaseChangeAffineTildeIso
    (cubicPointTraceFieldBaseChangeDiagonalRingHom K L)

/-- Sheafifying tensor multiplication gives precisely the original
unit-to-point-pushforward map; this fixes the geometric meaning of the retract. -/
theorem cubicPointTraceFieldBaseChangeDiagonalTildeIso_quotient :
    (tilde.functor (.of (L ⊗[K] L))).map
        (cubicPointTraceFieldBaseChangeDiagonalModuleQuotient K L) ≫
      (cubicPointTraceFieldBaseChangeDiagonalTildeIso K L).hom =
    (affineGlobalSectionsUnitTildeIso (A := L ⊗[K] L)).hom ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeTensorDiagonal K L) :=
  cubicPointTraceFieldBaseChangeAffineTildeIso_quotient
    (cubicPointTraceFieldBaseChangeDiagonalRingHom K L)

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The actual structure-sheaf inclusion of the diagonal rational summand. -/
def cubicPointTraceFieldBaseChangeDiagonalSheafSection :
    cubicPointTraceFieldBaseChangeDiagonalPushforward K L ⟶
      SheafOfModules.unit (Spec (.of (L ⊗[K] L))).ringCatSheaf :=
  (cubicPointTraceFieldBaseChangeDiagonalTildeIso K L).inv ≫
    (tilde.functor (.of (L ⊗[K] L))).map
      (cubicPointTraceFieldBaseChangeDiagonalModuleSection K L) ≫
        (affineGlobalSectionsUnitTildeIso (A := L ⊗[K] L)).hom

/-- The canonical restriction onto the actual rational diagonal summand has
the constructed section as its right inverse. -/
theorem cubicPointTraceFieldBaseChangeDiagonalSheafSection_quotient :
    cubicPointTraceFieldBaseChangeDiagonalSheafSection K L ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeTensorDiagonal K L) = 𝟙 _ := by
  let F := tilde.functor (.of (L ⊗[K] L))
  let e := cubicPointTraceFieldBaseChangeDiagonalTildeIso K L
  let u := affineGlobalSectionsUnitTildeIso (A := L ⊗[K] L)
  let s := cubicPointTraceFieldBaseChangeDiagonalModuleSection K L
  let m := cubicPointTraceFieldBaseChangeDiagonalModuleQuotient K L
  change (e.inv ≫ F.map s ≫ u.hom) ≫ _ = _
  simp only [Category.assoc]
  rw [← cubicPointTraceFieldBaseChangeDiagonalTildeIso_quotient K L]
  change e.inv ≫ (F.map s ≫ (F.map m ≫ e.hom)) = _
  rw [← Category.assoc (F.map s), ← F.map_comp,
    cubicPointTraceFieldBaseChangeDiagonalModuleSection_quotient K L, F.map_id]
  simp

/-- The actual diagonal component projector on the structure sheaf. -/
def cubicPointTraceFieldBaseChangeDiagonalSheafProjector :
    SheafOfModules.unit (Spec (.of (L ⊗[K] L))).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (.of (L ⊗[K] L))).ringCatSheaf :=
  IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
      (cubicPointTraceFieldBaseChangeTensorDiagonal K L) ≫
    cubicPointTraceFieldBaseChangeDiagonalSheafSection K L

theorem cubicPointTraceFieldBaseChangeDiagonalSheafProjector_eq_tilde :
    cubicPointTraceFieldBaseChangeDiagonalSheafProjector K L =
      (affineGlobalSectionsUnitTildeIso (A := L ⊗[K] L)).inv ≫
        (tilde.functor (.of (L ⊗[K] L))).map
          (cubicPointTraceFieldBaseChangeDiagonalModuleProjector K L) ≫
            (affineGlobalSectionsUnitTildeIso (A := L ⊗[K] L)).hom := by
  let F := tilde.functor (.of (L ⊗[K] L))
  let e := cubicPointTraceFieldBaseChangeDiagonalTildeIso K L
  let u := affineGlobalSectionsUnitTildeIso (A := L ⊗[K] L)
  let s := cubicPointTraceFieldBaseChangeDiagonalModuleSection K L
  let m := cubicPointTraceFieldBaseChangeDiagonalModuleQuotient K L
  unfold cubicPointTraceFieldBaseChangeDiagonalSheafProjector
    cubicPointTraceFieldBaseChangeDiagonalSheafSection
  apply (cancel_epi u.hom).1
  rw [← Category.assoc, ← cubicPointTraceFieldBaseChangeDiagonalTildeIso_quotient K L]
  change (F.map m ≫ e.hom) ≫ (e.inv ≫ F.map s ≫ u.hom) =
    u.hom ≫ (u.inv ≫ F.map (m ≫ s) ≫ u.hom)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [F.map_comp]
  exact (Category.assoc _ _ _).symm

theorem cubicPointTraceFieldBaseChangeDiagonalSheafProjector_idempotent :
    cubicPointTraceFieldBaseChangeDiagonalSheafProjector K L ≫
      cubicPointTraceFieldBaseChangeDiagonalSheafProjector K L =
        cubicPointTraceFieldBaseChangeDiagonalSheafProjector K L := by
  unfold cubicPointTraceFieldBaseChangeDiagonalSheafProjector
  simp only [Category.assoc]
  rw [← Category.assoc
    (cubicPointTraceFieldBaseChangeDiagonalSheafSection K L),
    cubicPointTraceFieldBaseChangeDiagonalSheafSection_quotient K L,
    Category.id_comp]

end ActualSheaf
end PfaffianDescent
