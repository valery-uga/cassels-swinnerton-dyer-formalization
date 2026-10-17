import PfaffianDescent.CubicPointTraceFieldBaseChangeClosedSupportScalar
import PfaffianDescent.CubicPointTraceFieldBaseChangeExtendedSupportExt

/-! # Actual residue scalars act by the original tensor factor -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PfaffianDescent.BundleSectionZeroLocus
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual scalar multiplication is preserved by the actual isomorphic
support comparison. -/
theorem cubicPointTraceFieldBaseChangeIsomorphicSupportIso_scalar
    {L : Type u} [Field L] {A B X : Scheme.{u}} (e : A ≅ B)
    (j : B ⟶ X) (p : B ⟶ Spec (.of L)) (a : L) :
    (Scheme.Modules.pushforward j).map (schemeModuleConstantEndomorphism p a) ≫
      (cubicPointTraceFieldBaseChangeIsomorphicSupportIso e j).hom =
    (cubicPointTraceFieldBaseChangeIsomorphicSupportIso e j).hom ≫
      (Scheme.Modules.pushforward (e.hom ≫ j)).map
        (schemeModuleConstantEndomorphism (e.hom ≫ p) a) := by
  let F := Scheme.Modules.pushforward j
  let c := schemeModuleConstantEndomorphism p a
  let c' := schemeModuleConstantEndomorphism (e.hom ≫ p) a
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit e.hom
  let t := (Scheme.Modules.pushforwardComp e.hom j).app (SheafOfModules.unit A.ringCatSheaf)
  have hq : c ≫ q = q ≫ (Scheme.Modules.pushforward e.hom).map c' := by
    change unitEndomorphismOfRegularFunction (affineFunctionHom p a) ≫ q =
      q ≫ (Scheme.Modules.pushforward e.hom).map
        (unitEndomorphismOfRegularFunction (affineFunctionHom (e.hom ≫ p) a))
    rw [affineFunctionHom_comp]
    exact cubicPointTraceFieldBaseChange_unitPushforward_regularFunction e.hom (affineFunctionHom p a)
  have ht : F.map ((Scheme.Modules.pushforward e.hom).map c') ≫ t.hom =
      t.hom ≫ (Scheme.Modules.pushforward (e.hom ≫ j)).map c' :=
    (Scheme.Modules.pushforwardComp e.hom j).hom.naturality c'
  change F.map c ≫ (F.map q ≫ t.hom) = (F.map q ≫ t.hom) ≫ _
  calc
    _ = F.map (c ≫ q) ≫ t.hom := by rw [F.map_comp]; simp only [Category.assoc]
    _ = F.map (q ≫ (Scheme.Modules.pushforward e.hom).map c') ≫ t.hom :=
      congrArg (fun v => F.map v ≫ t.hom) hq
    _ = F.map q ≫ (F.map ((Scheme.Modules.pushforward e.hom).map c') ≫ t.hom) := by
      rw [F.map_comp]
      simp only [Category.assoc]
    _ = F.map q ≫ (t.hom ≫ (Scheme.Modules.pushforward (e.hom ≫ j)).map c') :=
      congrArg (F.map q ≫ ·) ht
    _ = _ := by simp only [Category.assoc]; rfl

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (i : Spec (.of L) ⟶ X)
  (hi : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K L)))
  [IsClosedImmersion i]

/-- The actual original-point scalar action on the actual tensor support. -/
def cubicPointTraceFieldBaseChangeExtendedSupportOriginalScalar (a : L) :
    cubicPointTraceFieldBaseChangeExtendedPointPushforward K L p i hi ⟶
      cubicPointTraceFieldBaseChangeExtendedPointPushforward K L p i hi :=
  (Scheme.Modules.pushforward
    (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)).map
    (schemeModuleConstantEndomorphism
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] L))) a)

/-- Actual pullback of an original point scalar is multiplication through
the actual left-factor projection, under the proved support identification. -/
theorem cubicPointTraceFieldBaseChangeExtendedSupportIso_scalar (a : L) :
    (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeProjection K L p)).map
      (fieldPointPushforwardScalarEndomorphismAddHom i a) ≫
        (cubicPointTraceFieldBaseChangeExtendedSupportIso K L p i hi).hom =
    (cubicPointTraceFieldBaseChangeExtendedSupportIso K L p i hi).hom ≫
      cubicPointTraceFieldBaseChangeExtendedSupportOriginalScalar K L p i hi a := by
  let f := cubicPointTraceFieldBaseChangeProjection K L p
  let j := pullback.fst f i
  let g := pullback.snd f i
  let e := cubicPointTraceFieldBaseChangeTensorSupportPullbackIso K L p i hi
  let c := cubicPointTraceFieldBaseChangeClosedSupportIso f i
  let s := cubicPointTraceFieldBaseChangeIsomorphicSupportIso e j
  let t := (Scheme.Modules.pushforwardCongr
    (cubicPointTraceFieldBaseChangeTensorSupportPullbackIso_hom_fst K L p i hi)).app
      (SheafOfModules.unit (Spec (.of (L ⊗[K] L))).ringCatSheaf)
  let a₀ := (Scheme.Modules.pullback f).map (fieldPointPushforwardScalarEndomorphismAddHom i a)
  let a₁ := (Scheme.Modules.pushforward j).map (schemeModuleConstantEndomorphism g a)
  let a₂ := (Scheme.Modules.pushforward (e.hom ≫ j)).map
    (schemeModuleConstantEndomorphism (e.hom ≫ g) a)
  have h₀ : a₀ ≫ c.hom = c.hom ≫ a₁ :=
    cubicPointTraceFieldBaseChangeClosedSupportIso_scalar f i a
  have h₁ : a₁ ≫ s.hom = s.hom ≫ a₂ :=
    cubicPointTraceFieldBaseChangeIsomorphicSupportIso_scalar e j g a
  have h₂ : a₂ ≫ t.hom = t.hom ≫
      cubicPointTraceFieldBaseChangeExtendedSupportOriginalScalar K L p i hi a := by
    have ht := (Scheme.Modules.pushforwardCongr
      (cubicPointTraceFieldBaseChangeTensorSupportPullbackIso_hom_fst K L p i hi)).hom.naturality
        (schemeModuleConstantEndomorphism (e.hom ≫ g) a)
    have hg : e.hom ≫ g = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] L)) :=
      cubicPointTraceFieldBaseChangeTensorSupportPullbackIso_hom_snd K L p i hi
    change a₂ ≫ t.hom = t.hom ≫ _
    exact ht.trans (congrArg (fun q => t.hom ≫
      (Scheme.Modules.pushforward
        (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)).map
          (schemeModuleConstantEndomorphism q a)) hg)
  change a₀ ≫ (c.hom ≫ s.hom ≫ t.hom) = (c.hom ≫ s.hom ≫ t.hom) ≫ _
  calc
    _ = ((a₀ ≫ c.hom) ≫ s.hom) ≫ t.hom := by simp only [Category.assoc]
    _ = ((c.hom ≫ a₁) ≫ s.hom) ≫ t.hom :=
      congrArg (fun v => (v ≫ s.hom) ≫ t.hom) h₀
    _ = (c.hom ≫ (a₁ ≫ s.hom)) ≫ t.hom := by simp only [Category.assoc]
    _ = (c.hom ≫ (s.hom ≫ a₂)) ≫ t.hom :=
      congrArg (fun v => (c.hom ≫ v) ≫ t.hom) h₁
    _ = (c.hom ≫ s.hom) ≫ (a₂ ≫ t.hom) := by simp only [Category.assoc]
    _ = (c.hom ≫ s.hom) ≫ (t.hom ≫
        cubicPointTraceFieldBaseChangeExtendedSupportOriginalScalar K L p i hi a) :=
      congrArg ((c.hom ≫ s.hom) ≫ ·) h₂
    _ = _ := by simp only [Category.assoc]

end
end PfaffianDescent
