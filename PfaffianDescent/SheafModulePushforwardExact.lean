import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Left exactness of module-sheaf pushforward

The module-sheaf pushforward attached to a continuous functor is defined
objectwise by restriction of scalars.  Restriction of scalars preserves
limits, so this construction preserves finite limits as well.  Mathlib has
the corresponding colimit results from adjunctions; this small bridge is used
when exact sequences are checked after restricting to an open subscheme.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

universe v v₁ v₂ u₁ u₂ u

/-- Reassociating a functorial composite after a fixed preceding map.  This
small form avoids asking the simplifier to unfold a large module-sheaf term
while transporting tensor comparisons. -/
theorem comp_functor_map_comp
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (F : A ⥤ B) {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z)
    {W : B} (q : W ⟶ F.obj X) :
    q ≫ F.map (f ≫ g) = (q ≫ F.map f) ≫ F.map g := by
  rw [F.map_comp, Category.assoc]

/-- A mapped equality of composites induces the corresponding equality after
mapping each factor separately. -/
theorem functor_map_comp_eq_of_map_comp_eq
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (F : A ⥤ B) {W X Y Z : A}
    (f : W ⟶ X) (g : X ⟶ Y) (h : W ⟶ Z) (i : Z ⟶ Y)
    (H : F.map (f ≫ g) = F.map (h ≫ i)) :
    F.map f ≫ F.map g = F.map h ≫ F.map i := by
  calc
    F.map f ≫ F.map g = F.map (f ≫ g) := (F.map_comp _ _).symm
    _ = F.map (h ≫ i) := H
    _ = F.map h ≫ F.map i := F.map_comp _ _

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
  (φ : S ⟶ F.op ⋙ R)

/-- Pushforward of presheaves of modules preserves finite limits.  Evaluation
at an object of the source site turns it into restriction of scalars applied
to evaluation at its image. -/
theorem pushforward_preservesFiniteLimits :
    PreservesFiniteLimits (PresheafOfModules.pushforward φ) where
  preservesFiniteLimits J _ _ :=
    { preservesLimit := fun {K} ↦
        { preserves := fun {c} hc ↦ by
            refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ ?_)⟩
            change IsLimit ((ModuleCat.restrictScalars (φ.app X).hom).mapCone
              ((PresheafOfModules.evaluation R (F.op.obj X)).mapCone c))
            exact isLimitOfPreserves (ModuleCat.restrictScalars (φ.app X).hom)
              (isLimitOfPreserves (PresheafOfModules.evaluation R (F.op.obj X)) hc) } }

/-- Precomposition of module presheaves commutes with tensor products.  This
is the presheaf-level part of the comparison required to show that a sheaf
tensor product commutes with restriction to an open. -/
noncomputable def pushforward₀_tensorIso
    {R : Dᵒᵖ ⥤ CommRingCat.{u}}
    (M N : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.pushforward₀OfCommRingCat F R).obj (M ⊗ N) ≅
      (PresheafOfModules.pushforward₀OfCommRingCat F R).obj M ⊗
        (PresheafOfModules.pushforward₀OfCommRingCat F R).obj N :=
  (Functor.Monoidal.μIso (PresheafOfModules.pushforward₀OfCommRingCat F R) M N).symm

/-- Restriction's tensor comparison is natural in both presheaf-module
factors. -/
theorem pushforward₀_tensorIso_naturality
    {R : Dᵒᵖ ⥤ CommRingCat.{u}}
    {M₁ M₂ N₁ N₂ : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    (PresheafOfModules.pushforward₀OfCommRingCat F R).map
      (PresheafOfModules.Monoidal.tensorHom f g) ≫
      (pushforward₀_tensorIso (F := F) M₂ N₂).hom =
    (pushforward₀_tensorIso (F := F) M₁ N₁).hom ≫
      PresheafOfModules.Monoidal.tensorHom
        ((PresheafOfModules.pushforward₀OfCommRingCat F R).map f)
        ((PresheafOfModules.pushforward₀OfCommRingCat F R).map g) :=
  (Functor.OplaxMonoidal.δ_natural
    (PresheafOfModules.pushforward₀OfCommRingCat F R) f g).symm

section SheafificationComparison

variable {C' : Type u₁} [Category.{v₁} C'] {D' : Type u₂} [Category.{v₂} D']
  {J : GrothendieckTopology C'} {K : GrothendieckTopology D'} {G : C' ⥤ D'}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous G J K]
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (P : PresheafOfModules R.obj)

/-- The canonical comparison from sheafifying after module-presheaf
pushforward to pushing forward after sheafification.  For restriction to an
over-site the underlying additive comparison is an isomorphism; establishing
its module-linearity inverse is the remaining local-tensor compatibility
step. -/
noncomputable def pushforwardSheafificationComparison :
    (PresheafOfModules.sheafification (𝟙 S.obj)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P) ⟶
    (SheafOfModules.pushforward φ).obj
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)).symm
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P))

theorem sheafificationHomEquiv_pushforwardSheafificationComparison :
    PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)
      (pushforwardSheafificationComparison φ P) =
      (PresheafOfModules.pushforward φ.hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P) :=
  Equiv.apply_symm_apply _ _

end SheafificationComparison

end PresheafOfModules

namespace SheafOfModules

section OverSheafification

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (X : C) (P : PresheafOfModules R.obj)

/-- On the underlying additive sheaves, sheafification commutes with passage
to the site over an object.  The over-site functor is both continuous and
cocontinuous, so this is an instance of Mathlib's sheafification comparison.
This records the exact additive isomorphism needed to promote the canonical
module comparison to an isomorphism. -/
noncomputable def overFunctor_sheafificationUnderlyingIso :
    (SheafOfModules.toSheaf (R.over X)).obj
      ((PresheafOfModules.sheafification (𝟙 (R.over X).obj)).obj
        ((PresheafOfModules.pushforward (𝟙 (R.over X).obj)).obj P)) ≅
    (SheafOfModules.toSheaf (R.over X)).obj
      ((SheafOfModules.overFunctor R X).obj
        ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P)) := by
  let eL := (PresheafOfModules.sheafificationCompToSheaf
    (𝟙 (R.over X).obj)).app
      ((PresheafOfModules.pushforward (𝟙 (R.over X).obj)).obj P)
  let eC := ((Over.forget X).pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{u} (J.over X) J).app P.presheaf
  let eR := (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).app P
  exact eL ≪≫ eC ≪≫ ((Over.forget X).sheafPushforwardContinuous
    AddCommGrpCat.{u} (J.over X) J).mapIso eR.symm

/-- The module-linear counterpart to
`overFunctor_sheafificationUnderlyingIso`.  It is obtained directly from the
module-sheafification adjunction, so no additivity-only map is being used as
a substitute for a linear one. -/
noncomputable def overFunctor_sheafificationComparison :
    (PresheafOfModules.sheafification (𝟙 (R.over X).obj)).obj
      ((PresheafOfModules.pushforward (𝟙 (R.over X).obj)).obj P) ⟶
    (SheafOfModules.pushforward (F := Over.forget X) (𝟙 (R.over X))).obj
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (R.over X).obj)).symm
    ((PresheafOfModules.pushforward (𝟙 (R.over X).obj)).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P))

theorem sheafificationHomEquiv_overFunctor_sheafificationComparison :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (R.over X).obj)
      (overFunctor_sheafificationComparison X P) =
      (PresheafOfModules.pushforward (𝟙 (R.over X).obj)).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P) :=
  Equiv.apply_symm_apply _ _

/-- Evaluating the over-site comparison under the sheafification adjunction:
its composite with the local unit is the restriction of the global unit. -/
theorem overFunctor_sheafificationComparison_unit_comp :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (R.over X).obj)).unit.app
      ((PresheafOfModules.pushforward (𝟙 (R.over X).obj)).obj P) ≫
      (overFunctor_sheafificationComparison X P).val =
    (PresheafOfModules.pushforward (𝟙 (R.over X).obj)).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P) := by
  have h := sheafificationHomEquiv_overFunctor_sheafificationComparison
    (R := R) X P
  change _ = _ at h
  exact h

/-- The canonical comparison between sheafification and restriction to an
over-site is natural in the module presheaf. -/
theorem overFunctor_sheafificationComparison_naturality
    {P Q : PresheafOfModules R.obj} (f : P ⟶ Q) :
    (PresheafOfModules.sheafification (𝟙 (R.over X).obj)).map
      ((PresheafOfModules.pushforward (𝟙 (R.over X).obj)).map f) ≫
      overFunctor_sheafificationComparison X Q =
    overFunctor_sheafificationComparison X P ≫
      (SheafOfModules.overFunctor R X).map
        ((PresheafOfModules.sheafification (𝟙 R.obj)).map f) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (R.over X).obj)
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 (R.over X).obj)).injective
  erw [adj.homEquiv_naturality_left]
  erw [sheafificationHomEquiv_overFunctor_sheafificationComparison (R := R) X Q]
  erw [adj.homEquiv_naturality_right]
  erw [sheafificationHomEquiv_overFunctor_sheafificationComparison (R := R) X P]
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  ext U x
  erw [← Functor.map_comp]
  erw [A.unit.naturality f]
  erw [Functor.map_comp]
  rfl

/-- The canonical module comparison has the standard underlying additive
sheafification comparison.  This identifies the module-linear map with the
isomorphism supplied by the cocontinuous over-site functor. -/
theorem toSheaf_map_overFunctor_sheafificationComparison :
    (SheafOfModules.toSheaf (R.over X)).map
      (overFunctor_sheafificationComparison X P) =
      (overFunctor_sheafificationUnderlyingIso X P).hom := by
  let T : Sheaf (J.over X) RingCat.{u} :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (J.over X) J).obj R
  let comparison :
      (PresheafOfModules.sheafification (𝟙 T.obj)).obj
        ((PresheafOfModules.pushforward (𝟙 T.obj)).obj P) ⟶
      (SheafOfModules.pushforward (F := Over.forget X) (𝟙 T)).obj
        ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P) :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 T.obj)).symm
      ((PresheafOfModules.pushforward (𝟙 T.obj)).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P))
  let underlying :
      (SheafOfModules.toSheaf T).obj
        ((PresheafOfModules.sheafification (𝟙 T.obj)).obj
          ((PresheafOfModules.pushforward (𝟙 T.obj)).obj P)) ≅
      (SheafOfModules.toSheaf T).obj
        ((SheafOfModules.pushforward (F := Over.forget X) (𝟙 T)).obj
          ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P)) := by
    let eL := (PresheafOfModules.sheafificationCompToSheaf
      (𝟙 T.obj)).app ((PresheafOfModules.pushforward (𝟙 T.obj)).obj P)
    let eC := ((Over.forget X).pushforwardContinuousSheafificationCompatibility
      AddCommGrpCat.{u} (J.over X) J).app P.presheaf
    let eR := (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).app P
    exact eL ≪≫ eC ≪≫ ((Over.forget X).sheafPushforwardContinuous
      AddCommGrpCat.{u} (J.over X) J).mapIso eR.symm
  change (SheafOfModules.toSheaf T).map comparison = underlying.hom
  have h := PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm
    (α := 𝟙 T.obj)
    (F := (SheafOfModules.pushforward (F := Over.forget X) (𝟙 T)).obj
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P))
    ((PresheafOfModules.pushforward (𝟙 T.obj)).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P))
  dsimp [comparison, underlying]
  erw [h]
  apply ((CategoryTheory.sheafificationAdjunction (J.over X)
    AddCommGrpCat.{u}).homEquiv _ _).injective
  refine (Equiv.apply_symm_apply _ _).trans ?_
  dsimp
  erw [Adjunction.homEquiv_unit]
  dsimp [PresheafOfModules.sheafificationCompToSheaf]
  exact (Over.forget X).toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat.{u} (J.over X) J P.presheaf |>.symm

/-- The module sheafification comparison for an over-site is an isomorphism. -/
theorem isIso_overFunctor_sheafificationComparison :
    IsIso (overFunctor_sheafificationComparison X P) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (R.over X))]
  rw [toSheaf_map_overFunctor_sheafificationComparison]
  exact Iso.isIso_hom _

/-- The module-sheafification comparison on an over-site, packaged as an
isomorphism rather than through a local typeclass instance. -/
noncomputable def overFunctor_sheafificationComparisonIso
    (X : C) (P : PresheafOfModules R.obj) :
    (PresheafOfModules.sheafification (𝟙 (R.over X).obj)).obj
      ((PresheafOfModules.pushforward (𝟙 (R.over X).obj)).obj P) ≅
    (SheafOfModules.overFunctor R X).obj
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P) := by
  let h : IsIso (overFunctor_sheafificationComparison (R := R) X P) :=
    isIso_overFunctor_sheafificationComparison (R := R) X P
  exact @asIso _ _ _ _ (overFunctor_sheafificationComparison (R := R) X P) h

/-- Naturality of the inverse over-site comparison.  This is the orientation
needed to transport a globally sheafified tensor map to its local form. -/
theorem overFunctor_sheafificationComparison_inv_naturality
    {P Q : PresheafOfModules R.obj} (f : P ⟶ Q) :
    (SheafOfModules.overFunctor R X).map
      ((PresheafOfModules.sheafification (𝟙 R.obj)).map f) ≫
      (overFunctor_sheafificationComparisonIso X Q).inv =
    (overFunctor_sheafificationComparisonIso X P).inv ≫
      (PresheafOfModules.sheafification (𝟙 (R.over X).obj)).map
        ((PresheafOfModules.pushforward (𝟙 (R.over X).obj)).map f) := by
  let eP := overFunctor_sheafificationComparisonIso X P
  let eQ := overFunctor_sheafificationComparisonIso X Q
  have h := overFunctor_sheafificationComparison_naturality (R := R) X f
  have heP : eP.hom = overFunctor_sheafificationComparison (R := R) X P := rfl
  have heQ : eQ.hom = overFunctor_sheafificationComparison (R := R) X Q := rfl
  change (SheafOfModules.overFunctor R X).map
      ((PresheafOfModules.sheafification (𝟙 R.obj)).map f) ≫ eQ.inv =
    eP.inv ≫ (PresheafOfModules.sheafification (𝟙 (R.over X).obj)).map
      ((PresheafOfModules.pushforward (𝟙 (R.over X).obj)).map f)
  rw [Iso.comp_inv_eq]
  calc
    (SheafOfModules.overFunctor R X).map
        ((PresheafOfModules.sheafification (𝟙 R.obj)).map f) =
        eP.inv ≫ (eP.hom ≫ (SheafOfModules.overFunctor R X).map
          ((PresheafOfModules.sheafification (𝟙 R.obj)).map f)) := by
      rw [← Category.assoc, eP.inv_hom_id, Category.id_comp]
    _ = eP.inv ≫
        ((PresheafOfModules.sheafification (𝟙 (R.over X).obj)).map
          ((PresheafOfModules.pushforward (𝟙 (R.over X).obj)).map f) ≫ eQ.hom) := by
      rw [heP, heQ]
      erw [h]
      rfl
    _ = (eP.inv ≫ (PresheafOfModules.sheafification (𝟙 (R.over X).obj)).map
          ((PresheafOfModules.pushforward (𝟙 (R.over X).obj)).map f)) ≫ eQ.hom :=
      (Category.assoc _ _ _).symm

end OverSheafification

section OverTensor

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- The underlying sheaf of rings of a sheaf of commutative rings. -/
noncomputable abbrev commRingSheafToRingSheaf (R : Sheaf J CommRingCat.{u}) :
  Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

/-- The tensor product of module sheaves over a commutative ring sheaf,
formed by sheafifying the pointwise module tensor product. -/
noncomputable def commRingSheafTensor (R : Sheaf J CommRingCat.{u})
    (M N : SheafOfModules (commRingSheafToRingSheaf R)) :
    SheafOfModules (commRingSheafToRingSheaf R) :=
  (PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)).obj
    (PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val)

/-- The map induced on the sheafified tensor product by maps in both module
factors. -/
noncomputable def commRingSheafTensorMap (R : Sheaf J CommRingCat.{u})
    {M₁ M₂ N₁ N₂ : SheafOfModules (commRingSheafToRingSheaf R)}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    commRingSheafTensor R M₁ N₁ ⟶ commRingSheafTensor R M₂ N₂ :=
  (PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)).map
    (PresheafOfModules.Monoidal.tensorHom (R := R.obj) f.val g.val)

/-- Maps on sheafified tensor products respect composition in both factors. -/
theorem commRingSheafTensorMap_comp (R : Sheaf J CommRingCat.{u})
    {M₁ M₂ M₃ N₁ N₂ N₃ : SheafOfModules (commRingSheafToRingSheaf R)}
    (f₁ : M₁ ⟶ M₂) (g₁ : N₁ ⟶ N₂)
    (f₂ : M₂ ⟶ M₃) (g₂ : N₂ ⟶ N₃) :
    commRingSheafTensorMap R f₁ g₁ ≫ commRingSheafTensorMap R f₂ g₂ =
      commRingSheafTensorMap R (f₁ ≫ f₂) (g₁ ≫ g₂) := by
  dsimp [commRingSheafTensorMap, commRingSheafTensor]
  let F := PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)
  let M₁' : PresheafOfModules (commRingSheafToRingSheaf R).obj := M₁.val
  let M₂' : PresheafOfModules (commRingSheafToRingSheaf R).obj := M₂.val
  let M₃' : PresheafOfModules (commRingSheafToRingSheaf R).obj := M₃.val
  let N₁' : PresheafOfModules (commRingSheafToRingSheaf R).obj := N₁.val
  let N₂' : PresheafOfModules (commRingSheafToRingSheaf R).obj := N₂.val
  let N₃' : PresheafOfModules (commRingSheafToRingSheaf R).obj := N₃.val
  let f₁' : M₁' ⟶ M₂' := f₁.val
  let f₂' : M₂' ⟶ M₃' := f₂.val
  let g₁' : N₁' ⟶ N₂' := g₁.val
  let g₂' : N₂' ⟶ N₃' := g₂.val
  change F.map (PresheafOfModules.Monoidal.tensorHom f₁' g₁') ≫
      F.map (PresheafOfModules.Monoidal.tensorHom f₂' g₂') =
    F.map (PresheafOfModules.Monoidal.tensorHom (f₁' ≫ f₂') (g₁' ≫ g₂'))
  letI : MonoidalCategory (PresheafOfModules (commRingSheafToRingSheaf R).obj) :=
    PresheafOfModules.monoidalCategory
  calc
    F.map (PresheafOfModules.Monoidal.tensorHom f₁' g₁') ≫
        F.map (PresheafOfModules.Monoidal.tensorHom f₂' g₂') =
        F.map (PresheafOfModules.Monoidal.tensorHom f₁' g₁' ≫
          PresheafOfModules.Monoidal.tensorHom f₂' g₂') :=
      (F.map_comp _ _).symm
    _ = F.map (PresheafOfModules.Monoidal.tensorHom (f₁' ≫ f₂') (g₁' ≫ g₂')) :=
      congrArg F.map (tensorHom_comp_tensorHom f₁' g₁' f₂' g₂')

/-- Tensoring identity maps gives the identity of the sheafified tensor
product. -/
theorem commRingSheafTensorMap_id (R : Sheaf J CommRingCat.{u})
    (M N : SheafOfModules (commRingSheafToRingSheaf R)) :
    commRingSheafTensorMap R (𝟙 M) (𝟙 N) = 𝟙 (commRingSheafTensor R M N) := by
  dsimp [commRingSheafTensorMap, commRingSheafTensor]
  let F := PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)
  let idM : M.val ⟶ M.val :=
    (show SheafOfModules.Hom M M from 𝟙 M).val
  let idN : N.val ⟶ N.val :=
    (show SheafOfModules.Hom N N from 𝟙 N).val
  have hidM : idM = 𝟙 M.val := rfl
  have hidN : idN = 𝟙 N.val := rfl
  let T : PresheafOfModules (commRingSheafToRingSheaf R).obj :=
    PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
  let idT : T ⟶ T := 𝟙 T
  change F.map (PresheafOfModules.Monoidal.tensorHom idM idN) = 𝟙 (F.obj T)
  rw [← F.map_id T]
  congr 1
  rw [hidM, hidN]
  change PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) (𝟙 N.val) = idT
  ext U m
  induction m using TensorProduct.induction_on with
  | zero => rfl
  | add x y hx hy =>
    calc
      _ = (ModuleCat.Hom.hom
          ((PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) (𝟙 N.val)).app U)) x +
          (ModuleCat.Hom.hom
            ((PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) (𝟙 N.val)).app U)) y :=
        LinearMap.map_add _ x y
      _ = (ModuleCat.Hom.hom (idT.app U)) x +
          (ModuleCat.Hom.hom (idT.app U)) y := congrArg₂ (· + ·) hx hy
      _ = _ := (idT.app U).hom.map_add x y |>.symm
  | tmul x y => rfl

/-- Tensoring on the right by a fixed sheaf of modules over a commutative
ring sheaf. -/
noncomputable def commRingSheafTensorRight (R : Sheaf J CommRingCat.{u})
    (N : SheafOfModules (commRingSheafToRingSheaf R)) :
    SheafOfModules (commRingSheafToRingSheaf R) ⥤
      SheafOfModules (commRingSheafToRingSheaf R) where
  obj M := commRingSheafTensor R M N
  map f := commRingSheafTensorMap R f (𝟙 N)
  map_id M := commRingSheafTensorMap_id R M N
  map_comp f g := by
    simpa using (commRingSheafTensorMap_comp R f (𝟙 N) g (𝟙 N)).symm

/-- Isomorphic right tensor factors induce isomorphic sheafified tensor
functors. -/
noncomputable def commRingSheafTensorRightCongr (R : Sheaf J CommRingCat.{u})
    {L₁ L₂ : SheafOfModules (commRingSheafToRingSheaf R)} (e : L₁ ≅ L₂) :
    commRingSheafTensorRight R L₁ ≅ commRingSheafTensorRight R L₂ :=
  NatIso.ofComponents (fun M =>
    { hom := commRingSheafTensorMap R (𝟙 M) e.hom
      inv := commRingSheafTensorMap R (𝟙 M) e.inv
      hom_inv_id := by
        calc
          commRingSheafTensorMap R (𝟙 M) e.hom ≫
              commRingSheafTensorMap R (𝟙 M) e.inv =
              commRingSheafTensorMap R ((𝟙 M) ≫ (𝟙 M)) (e.hom ≫ e.inv) :=
            commRingSheafTensorMap_comp R (𝟙 M) e.hom (𝟙 M) e.inv
          _ = commRingSheafTensorMap R (𝟙 M) (𝟙 L₁) := by simp
          _ = 𝟙 (commRingSheafTensor R M L₁) := commRingSheafTensorMap_id R M L₁
      inv_hom_id := by
        calc
          commRingSheafTensorMap R (𝟙 M) e.inv ≫
              commRingSheafTensorMap R (𝟙 M) e.hom =
              commRingSheafTensorMap R ((𝟙 M) ≫ (𝟙 M)) (e.inv ≫ e.hom) :=
            commRingSheafTensorMap_comp R (𝟙 M) e.inv (𝟙 M) e.hom
          _ = commRingSheafTensorMap R (𝟙 M) (𝟙 L₂) := by simp
          _ = 𝟙 (commRingSheafTensor R M L₂) := commRingSheafTensorMap_id R M L₂ }) (by
    intro M M' f
    change commRingSheafTensorMap R f (𝟙 L₁) ≫
        commRingSheafTensorMap R (𝟙 M') e.hom =
      commRingSheafTensorMap R (𝟙 M) e.hom ≫
        commRingSheafTensorMap R f (𝟙 L₂)
    calc
      commRingSheafTensorMap R f (𝟙 L₁) ≫
          commRingSheafTensorMap R (𝟙 M') e.hom =
          commRingSheafTensorMap R (f ≫ 𝟙 M') ((𝟙 L₁) ≫ e.hom) :=
        commRingSheafTensorMap_comp R f (𝟙 L₁) (𝟙 M') e.hom
      _ = commRingSheafTensorMap R f e.hom := by simp
      _ = commRingSheafTensorMap R ((𝟙 M) ≫ f) (e.hom ≫ (𝟙 L₂)) := by simp
      _ = commRingSheafTensorMap R (𝟙 M) e.hom ≫
          commRingSheafTensorMap R f (𝟙 L₂) :=
        (commRingSheafTensorMap_comp R (𝟙 M) e.hom f (𝟙 L₂)).symm)

/-- Passage to the over-site of a sheaf of commutative rings. -/
noncomputable abbrev commRingSheafOver (R : Sheaf J CommRingCat.{u}) (X : C) :
    Sheaf (J.over X) CommRingCat.{u} :=
  ((Over.forget X).sheafPushforwardContinuous CommRingCat.{u} (J.over X) J).obj R

/-- The underlying ring sheaf of the commutative over-site structure is
isomorphic to the over-site of the underlying ring sheaf.  The two objects
have the same presheaf components; this explicit isomorphism records the
otherwise troublesome type-level distinction between
`commRingSheafToRingSheaf (commRingSheafOver R X)` and
`(commRingSheafToRingSheaf R).over X`. -/
noncomputable def commRingSheafOverToRingSheafIso
    (R : Sheaf J CommRingCat.{u}) (X : C) :
    commRingSheafToRingSheaf (commRingSheafOver R X) ≅
      (commRingSheafToRingSheaf R).over X := by
  refine ObjectProperty.isoMk _ ?_
  exact NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    rfl)

/-- The forward canonical over-site ring-sheaf transport is componentwise the
identity.  Naming this formula keeps later change-of-rings calculations from
unfolding the `ObjectProperty` construction of the ring-sheaf isomorphism. -/
@[simp]
theorem commRingSheafOverToRingSheafIso_hom_app
    (R : Sheaf J CommRingCat.{u}) (X : C) (Y : (Over X)ᵒᵖ) :
    (commRingSheafOverToRingSheafIso R X).hom.hom.app Y = 𝟙 _ := by
  rfl

/-- The inverse canonical over-site ring-sheaf transport is componentwise the
identity. -/
@[simp]
theorem commRingSheafOverToRingSheafIso_inv_app
    (R : Sheaf J CommRingCat.{u}) (X : C) (Y : (Over X)ᵒᵖ) :
    (commRingSheafOverToRingSheafIso R X).inv.hom.app Y = 𝟙 _ := by
  rfl

/-- The identity-site pushforward comparison for ring sheaves is
componentwise the identity.  This gives an explicit normal form when a
change-of-rings construction exposes identity-site pushforward wrappers. -/
@[simp]
theorem sheafPushforwardContinuousIdRing_hom_app
    (R : Sheaf J RingCat.{u}) (Y : Cᵒᵖ) :
    ((Functor.sheafPushforwardContinuousId (A := RingCat.{u}) (J := J)).hom.app R).hom.app Y =
      𝟙 _ := by
  rfl

/-- The inverse identity-site pushforward comparison for ring sheaves is
componentwise the identity. -/
@[simp]
theorem sheafPushforwardContinuousIdRing_inv_app
    (R : Sheaf J RingCat.{u}) (Y : Cᵒᵖ) :
    ((Functor.sheafPushforwardContinuousId (A := RingCat.{u}) (J := J)).inv.app R).hom.app Y =
      𝟙 _ := by
  rfl

/-- The forward over-site transport followed by the identity-site pushforward
normalization is componentwise the identity. -/
@[simp]
theorem commRingSheafOverToRingSheafIso_hom_comp_idPush_app
    (R : Sheaf J CommRingCat.{u}) (X : C) (Y : (Over X)ᵒᵖ) :
    ((commRingSheafOverToRingSheafIso R X).hom ≫
      (Functor.sheafPushforwardContinuousId (A := RingCat.{u}) (J := J.over X)).inv.app
        ((commRingSheafToRingSheaf R).over X)).hom.app Y = 𝟙 _ := by
  rfl

/-- The inverse over-site transport followed by the identity-site pushforward
normalization is componentwise the identity. -/
@[simp]
theorem commRingSheafOverToRingSheafIso_inv_comp_idPush_app
    (R : Sheaf J CommRingCat.{u}) (X : C) (Y : (Over X)ᵒᵖ) :
    ((commRingSheafOverToRingSheafIso R X).inv ≫
      (Functor.sheafPushforwardContinuousId (A := RingCat.{u}) (J := J.over X)).inv.app
        (commRingSheafToRingSheaf (commRingSheafOver R X))).hom.app Y = 𝟙 _ := by
  rfl

/- The preceding ring-sheaf isomorphism also transports the corresponding
unit modules.  Keeping this as an explicit isomorphism is useful when a
module on the over-site is produced by restriction (and hence is initially
typed over the underlying over-site ring sheaf). -/
noncomputable def commRingSheafOverToRingSheafUnitIso
    (R : Sheaf J CommRingCat.{u}) (X : C) :
    (SheafOfModules.pushforward (F := 𝟭 (Over X))
      (commRingSheafOverToRingSheafIso R X).hom).obj
      (SheafOfModules.unit ((commRingSheafToRingSheaf R).over X)) ≅
      SheafOfModules.unit (commRingSheafToRingSheaf (commRingSheafOver R X)) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso ?_
  exact PresheafOfModules.isoMk (fun U => Iso.refl _) (by
    intro U V f
    rfl)

/-- Transport modules on the underlying over-site ring sheaf to modules over
the underlying commutative over-site ring sheaf. -/
noncomputable def commRingSheafOverToRingSheafTransport
    (R : Sheaf J CommRingCat.{u}) (X : C) :
    SheafOfModules ((commRingSheafToRingSheaf R).over X) ⥤
      SheafOfModules (commRingSheafToRingSheaf (commRingSheafOver R X)) :=
  SheafOfModules.pushforward (F := 𝟭 (Over X))
    (commRingSheafOverToRingSheafIso R X).hom

/-- A globally trivial module remains trivial after restriction and transport
across the canonical over-site ring-sheaf isomorphism. -/
noncomputable def commRingSheafOverToRingSheafTransport_globalUnitIso
    (R : Sheaf J CommRingCat.{u}) (X : C)
    {T : SheafOfModules (commRingSheafToRingSheaf R)}
    (eT : T ≅ SheafOfModules.unit (commRingSheafToRingSheaf R)) :
    (commRingSheafOverToRingSheafTransport R X).obj
        ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) X).obj T) ≅
      SheafOfModules.unit (commRingSheafToRingSheaf (commRingSheafOver R X)) :=
  (commRingSheafOverToRingSheafTransport R X).mapIso
      ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) X).mapIso eT) ≪≫
    commRingSheafOverToRingSheafUnitIso R X

/-- The presheaf-level tensor comparison for restriction, written in the
module-sheaf presentation used by the over-site.  Keeping this transport as a
separate lemma avoids unfolding the two definitionally equal presentations of
the restricted ring sheaf inside a larger naturality proof. -/
theorem overFunctor_pushforward₀_tensorIso_naturality
    (R : Sheaf J CommRingCat.{u}) (X : C)
    {M₁ M₂ N₁ N₂ : SheafOfModules (commRingSheafToRingSheaf R)}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    (PresheafOfModules.pushforward
      (𝟙 ((commRingSheafToRingSheaf R).over X).obj)).map
      (PresheafOfModules.Monoidal.tensorHom f.val g.val) ≫
      (PresheafOfModules.pushforward₀_tensorIso
        (F := Over.forget X) M₂.val N₂.val).hom =
    (PresheafOfModules.pushforward₀_tensorIso
      (F := Over.forget X) M₁.val N₁.val).hom ≫
      PresheafOfModules.Monoidal.tensorHom
        ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) X).map f).val
        ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) X).map g).val := by
  exact PresheafOfModules.pushforward₀_tensorIso_naturality
    (F := Over.forget X) f.val g.val

/-- Sheafifying the preceding over-site tensor comparison preserves its
naturality.  This form can be composed directly with the sheafification
comparison isomorphism. -/
theorem sheafification_overFunctor_pushforward₀_tensorIso_naturality
    (R : Sheaf J CommRingCat.{u}) (X : C)
    {M₁ M₂ N₁ N₂ : SheafOfModules (commRingSheafToRingSheaf R)}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    (PresheafOfModules.sheafification
      (𝟙 ((commRingSheafToRingSheaf R).over X).obj)).map
      ((PresheafOfModules.pushforward
        (𝟙 ((commRingSheafToRingSheaf R).over X).obj)).map
        (PresheafOfModules.Monoidal.tensorHom f.val g.val) ≫
        (PresheafOfModules.pushforward₀_tensorIso
          (F := Over.forget X) M₂.val N₂.val).hom) =
    (PresheafOfModules.sheafification
      (𝟙 ((commRingSheafToRingSheaf R).over X).obj)).map
      ((PresheafOfModules.pushforward₀_tensorIso
        (F := Over.forget X) M₁.val N₁.val).hom ≫
        PresheafOfModules.Monoidal.tensorHom
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) X).map f).val
          ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) X).map g).val) := by
  exact congrArg _ (overFunctor_pushforward₀_tensorIso_naturality R X f g)

/-- Restriction to an over-site commutes with tensor products of module
sheaves.  The first factor is the proven module-sheafification comparison;
the second is the strong monoidality of presheaf restriction. -/
noncomputable def overFunctor_commRingSheafTensorIso
    (R : Sheaf J CommRingCat.{u}) (X : C)
    (M N : SheafOfModules (commRingSheafToRingSheaf R)) :
    (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) X).obj
      (commRingSheafTensor R M N) ≅
    commRingSheafTensor (commRingSheafOver R X)
      ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) X).obj M)
      ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) X).obj N) := by
  let P : PresheafOfModules (commRingSheafToRingSheaf R).obj :=
    PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
  exact (overFunctor_sheafificationComparisonIso X P).symm ≪≫
    (PresheafOfModules.sheafification
      (𝟙 ((commRingSheafToRingSheaf R).over X).obj)).mapIso
      (PresheafOfModules.pushforward₀_tensorIso
        (F := Over.forget X) M.val N.val)

end OverTensor

end SheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- Pushforward of sheaves of modules preserves finite limits.  The
forgetful functor to module presheaves creates finite limits, and the
underlying presheaf functor is left exact by
`PresheafOfModules.pushforwardPreservesFiniteLimits`. -/
theorem pushforward_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.pushforward φ) where
  preservesFiniteLimits L _ _ :=
    { preservesLimit := fun {G} ↦
        { preserves := fun {c} hc ↦ by
            let : PreservesFiniteLimits (PresheafOfModules.pushforward φ.hom) :=
              PresheafOfModules.pushforward_preservesFiniteLimits φ.hom
            refine ⟨isLimitOfReflects (SheafOfModules.forget S) ?_⟩
            change IsLimit ((PresheafOfModules.pushforward φ.hom).mapCone
              ((SheafOfModules.forget R).mapCone c))
            exact isLimitOfPreserves (PresheafOfModules.pushforward φ.hom)
              (isLimitOfPreserves (SheafOfModules.forget R) hc) } }

section Over

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- Restriction of a module sheaf to the site over an object preserves finite
limits. -/
theorem overFunctor_preservesFiniteLimits (R : Sheaf J RingCat.{u}) (X : C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor R X) := by
  change PreservesFiniteLimits (SheafOfModules.pushforward (𝟙 _))
  exact pushforward_preservesFiniteLimits _

/-- A short exact sequence of module sheaves remains short exact after
restriction to the site over any object. -/
theorem ShortComplex.shortExact_map_overFunctor
    [HasBinaryProducts C] (R : Sheaf J RingCat.{u}) (X : C)
    (S : ShortComplex (SheafOfModules R)) (hS : S.ShortExact) :
    letI : (SheafOfModules.overFunctor R X).IsLeftAdjoint := by
      change (SheafOfModules.pushforward (𝟙 (R.over X))).IsLeftAdjoint
      exact (SheafOfModules.overPushforwardOverAdj (R := R) X).isLeftAdjoint
    letI : (SheafOfModules.overFunctor R X).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_isLeftAdjoint _
    letI : PreservesFiniteLimits (SheafOfModules.overFunctor R X) :=
      overFunctor_preservesFiniteLimits R X
    (S.map (SheafOfModules.overFunctor R X)).ShortExact := by
  let : (SheafOfModules.overFunctor R X).IsLeftAdjoint := by
    change (SheafOfModules.pushforward (𝟙 (R.over X))).IsLeftAdjoint
    exact (SheafOfModules.overPushforwardOverAdj (R := R) X).isLeftAdjoint
  let : (SheafOfModules.overFunctor R X).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  let : PreservesFiniteLimits (SheafOfModules.overFunctor R X) :=
    overFunctor_preservesFiniteLimits R X
  exact hS.map_of_exact (SheafOfModules.overFunctor R X)

end Over

section LocalDetection

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- Restriction to an over-site preserves zero morphisms.  This is the
zero-morphism consequence of its explicit right adjoint. -/
noncomputable instance overFunctor_preservesZeroMorphisms [HasBinaryProducts C]
    (R : Sheaf J RingCat.{u}) (Y : C) :
    (SheafOfModules.overFunctor.{u} R Y).PreservesZeroMorphisms := by
  letI : (SheafOfModules.overFunctor.{u} R Y).IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := R) Y).isLeftAdjoint
  infer_instance

/-- Restriction to the members of a covering family jointly reflects
isomorphisms of module sheaves. -/
theorem overFunctors_jointlyReflectIsomorphisms
    {R : Sheaf J RingCat.{u}} [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} (X : ι → C) (hX : J.CoversTop X) :
    JointlyReflectIsomorphisms
      (fun i => SheafOfModules.overFunctor.{u} R (X i)) := by
  constructor
  intro M N f inst
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf R)]
  apply CategoryTheory.Sheaf.isIso_of_coversTop hX
  intro i
  change IsIso ((SheafOfModules.toSheaf (R.over (X i))).map
    ((SheafOfModules.overFunctor.{u} R (X i)).map f))
  infer_instance

variable {R : Sheaf J RingCat.{u}}
  [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A module sheaf is zero when it becomes zero over every member of a
covering family.  The proof detects the isomorphism to the zero object on
underlying additive sheaves, where isomorphisms are local on the site. -/
theorem isZero_of_coversTop {ι : Type u} (X : ι → C) (hX : J.CoversTop X)
    (M : SheafOfModules.{u} R)
    (h : ∀ i, IsZero ((SheafOfModules.overFunctor.{u} R (X i)).obj M)) :
    IsZero M := by
  let Z : SheafOfModules.{u} R := 0
  let hZ : IsZero Z := isZero_zero _
  let z : M ⟶ Z := 0
  haveI : IsIso z := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf R)]
    apply CategoryTheory.Sheaf.isIso_of_coversTop hX
    intro i
    change IsIso ((SheafOfModules.toSheaf (R.over (X i))).map
      ((SheafOfModules.overFunctor.{u} R (X i)).map z))
    haveI : IsIso ((SheafOfModules.overFunctor.{u} R (X i)).map z) :=
      (h i).isIso (Functor.map_isZero (SheafOfModules.overFunctor.{u} R (X i)) hZ) _
    infer_instance
  exact IsZero.of_iso hZ (asIso z)

/-- A short complex of module sheaves is short exact when its restrictions to
each member of a covering family are short exact.  Restriction preserves the
finite limits and colimits involved in homology, while the preceding theorem
detects the resulting isomorphisms globally. -/
theorem ShortComplex.shortExact_of_coversTop
    [∀ Y, HasSheafify (J.over Y) AddCommGrpCat.{u}]
    [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} (X : ι → C)
    (hX : J.CoversTop X) (S : ShortComplex (SheafOfModules.{u} R))
    (h : ∀ i, (S.map (SheafOfModules.overFunctor.{u} R (X i))).ShortExact) :
    S.ShortExact := by
  let F : ∀ i, SheafOfModules.{u} R ⥤ SheafOfModules.{u} (R.over (X i)) :=
    fun i => SheafOfModules.overFunctor R (X i)
  let hF : JointlyReflectIsomorphisms F :=
    overFunctors_jointlyReflectIsomorphisms X hX
  letI : ∀ i, (F i).IsLeftAdjoint := fun i => by
    dsimp [F]
    exact (SheafOfModules.overPushforwardOverAdj (R := R) (X i)).isLeftAdjoint
  letI : ∀ i, PreservesFiniteLimits (F i) := fun i => by
    dsimp [F]
    exact overFunctor_preservesFiniteLimits R (X i)
  letI : ∀ i, PreservesFiniteColimits (F i) := fun i => by
    infer_instance
  exact (hF.shortExact_iff S).mpr h

end LocalDetection

end SheafOfModules

open AlgebraicGeometry

/-- Restriction of module sheaves along an open immersion preserves finite
limits.  It is a module-sheaf pushforward along the induced functor on open
sets, so this follows from the general left-exact pushforward theorem above. -/
theorem restrictFunctor_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  change PreservesFiniteLimits (SheafOfModules.pushforward _)
  exact SheafOfModules.pushforward_preservesFiniteLimits _

/-- Short exact sequences of module sheaves stay short exact after
restriction to an open subscheme. -/
theorem ShortComplex.shortExact_map_restrictFunctor
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (S : ShortComplex Y.Modules) (hS : S.ShortExact) :
    (S.map (Scheme.Modules.restrictFunctor f)).ShortExact := by
  let : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
    restrictFunctor_preservesFiniteLimits f
  exact hS.map_of_exact (Scheme.Modules.restrictFunctor f)

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

end SheafOfModules

end PfaffianDescent
