import PfaffianDescent.CubicPointTraceFieldBaseChangeIsomorphicSupport

/-! # Actual pulled-back point support in the tensor-spectrum model

This identifies actual geometric pullback with precisely the whole support
used by the rational diagonal summand. The unit restriction square is proved.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (i : Spec (.of L) ⟶ X)
  (hi : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The actual scalar-extension projection back to the original scheme. -/
abbrev cubicPointTraceFieldBaseChangeProjection :
    schemeBaseChangeToField (L := L) X p ⟶ X :=
  pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The actual tensor fibre is the actual pullback of the original point
along scalar extension. -/
def cubicPointTraceFieldBaseChangeTensorSupportPullbackIso :
    Spec (.of (L ⊗[K] L)) ≅
      pullback (cubicPointTraceFieldBaseChangeProjection K L p) i :=
  (pullbackSpecIso K L L).symm ≪≫
    (finitePointBaseChangeToAmbient_isPullback (L := L) p i hi).isoPullback

@[reassoc]
theorem cubicPointTraceFieldBaseChangeTensorSupportPullbackIso_hom_fst :
    (cubicPointTraceFieldBaseChangeTensorSupportPullbackIso K L p i hi).hom ≫
      pullback.fst (cubicPointTraceFieldBaseChangeProjection K L p) i =
        cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi := by
  rw [cubicPointTraceFieldBaseChangeTensorSupportPullbackIso, Iso.trans_hom,
    Category.assoc, IsPullback.isoPullback_hom_fst]
  rfl

/-- The original residue-field action is the left tensor factor. -/
@[reassoc]
theorem cubicPointTraceFieldBaseChangeTensorSupportPullbackIso_hom_snd :
    (cubicPointTraceFieldBaseChangeTensorSupportPullbackIso K L p i hi).hom ≫
      pullback.snd (cubicPointTraceFieldBaseChangeProjection K L p) i =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] L)) := by
  rw [cubicPointTraceFieldBaseChangeTensorSupportPullbackIso, Iso.trans_hom,
    Category.assoc, IsPullback.isoPullback_hom_snd]
  exact pullbackSpecIso_inv_fst K L L

/-- The new base field acts through the right tensor factor. -/
@[reassoc]
theorem cubicPointTraceFieldBaseChangeTensorPointToAmbient_toField :
    cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom) := by
  rw [cubicPointTraceFieldBaseChangeTensorPointToAmbient, Category.assoc,
    finitePointBaseChangeToAmbient_snd]
  exact pullbackSpecIso_inv_snd K L L

variable [IsClosedImmersion i]

/-- The actual pulled-back point module identifies with the entire actual
extended support used by the rational diagonal summand. -/
def cubicPointTraceFieldBaseChangeExtendedSupportIso :
    (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeProjection K L p)).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) ≅
        cubicPointTraceFieldBaseChangeExtendedPointPushforward K L p i hi :=
  cubicPointTraceFieldBaseChangeClosedSupportIso
      (cubicPointTraceFieldBaseChangeProjection K L p) i ≪≫
    cubicPointTraceFieldBaseChangeIsomorphicSupportIso
      (cubicPointTraceFieldBaseChangeTensorSupportPullbackIso K L p i hi)
      (pullback.fst (cubicPointTraceFieldBaseChangeProjection K L p) i) ≪≫
    (Scheme.Modules.pushforwardCongr
      (cubicPointTraceFieldBaseChangeTensorSupportPullbackIso_hom_fst K L p i hi)).app
      (SheafOfModules.unit (Spec (.of (L ⊗[K] L))).ringCatSheaf)

/-- The proved actual support isomorphism carries the pulled-back original
unit restriction to the actual tensor-support unit restriction. -/
theorem cubicPointTraceFieldBaseChangeExtendedSupportIso_unit :
    (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeProjection K L p)).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫
        (cubicPointTraceFieldBaseChangeExtendedSupportIso K L p i hi).hom =
      (cubicPointTraceFieldBaseChangePullbackUnitIso
        (cubicPointTraceFieldBaseChangeProjection K L p)).hom ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi) := by
  let f := cubicPointTraceFieldBaseChangeProjection K L p
  let j := pullback.fst f i
  let e := cubicPointTraceFieldBaseChangeTensorSupportPullbackIso K L p i hi
  let c := cubicPointTraceFieldBaseChangeClosedSupportIso f i
  let s := cubicPointTraceFieldBaseChangeIsomorphicSupportIso e j
  let t := (Scheme.Modules.pushforwardCongr
    (cubicPointTraceFieldBaseChangeTensorSupportPullbackIso_hom_fst K L p i hi)).app
      (SheafOfModules.unit (Spec (.of (L ⊗[K] L))).ringCatSheaf)
  have h₀ : (Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫ c.hom =
    (cubicPointTraceFieldBaseChangePullbackUnitIso f).hom ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j :=
    closedImmersionPushforwardBaseChangeHom_quotient f i
  have h₁ : IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j ≫ s.hom =
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (e.hom ≫ j) :=
    cubicPointTraceFieldBaseChangeIsomorphicSupportIso_unit e j
  have h₂ : IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (e.hom ≫ j) ≫
      t.hom = IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi) :=
    cubicPointTraceFieldBaseChange_unitPushforward_congr
      (cubicPointTraceFieldBaseChangeTensorSupportPullbackIso_hom_fst K L p i hi)
  change (Scheme.Modules.pullback f).map
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫
      (c.hom ≫ s.hom ≫ t.hom) = _
  calc
    _ = ((Scheme.Modules.pullback f).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫ c.hom) ≫
          s.hom ≫ t.hom := by simp only [Category.assoc]
    _ = ((cubicPointTraceFieldBaseChangePullbackUnitIso f).hom ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j) ≫
          s.hom ≫ t.hom := congrArg (fun v => (v ≫ s.hom) ≫ t.hom) h₀
    _ = (cubicPointTraceFieldBaseChangePullbackUnitIso f).hom ≫
        ((IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j ≫ s.hom) ≫ t.hom) := by
      simp only [Category.assoc]
    _ = (cubicPointTraceFieldBaseChangePullbackUnitIso f).hom ≫
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (e.hom ≫ j) ≫ t.hom) :=
      congrArg (fun v => (cubicPointTraceFieldBaseChangePullbackUnitIso f).hom ≫
        (v ≫ t.hom)) h₁
    _ = _ := congrArg ((cubicPointTraceFieldBaseChangePullbackUnitIso f).hom ≫ ·) h₂

end

/-- The finite diagonal projection uses scalars from the new field in the
right tensor factor and original-point scalars in the left tensor factor. -/
theorem cubicPointTraceFieldBaseChangeDiagonalProjector_finite_geometric_scalars
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ s : Finset (L × L), ∀ t : L ⊗[K] L,
      cubicPointTraceFieldBaseChangeDiagonalProjector K L * t =
        ∑ ab ∈ s, ((1 : L) ⊗ₜ[K] ab.2) * ((ab.1 ⊗ₜ[K] (1 : L)) * t) := by
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset
    (cubicPointTraceFieldBaseChangeDiagonalProjector K L)
  refine ⟨s, fun t => ?_⟩
  rw [hs, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [← mul_assoc]
  congr 1
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end PfaffianDescent
