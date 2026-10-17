import PfaffianDescent.SchemeModuleTensor

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IdealSheafDataModule MonoidalCategory

universe u

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

/-- The canonical comparison from sheafifying a presheaf tensor product to
first sheafifying its left factor and then tensoring module sheaves. -/
noncomputable def commRingSheafTensorSheafificationRightComparison
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    (N : SheafOfModules (commRingSheafToRingSheaf R)) :
    (PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)).obj
      (PresheafOfModules.Monoidal.tensorObj P N.val) ⟶
    commRingSheafTensor R
      ((PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)).obj P) N := by
  let F := PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (commRingSheafToRingSheaf R).obj)
  exact F.map (PresheafOfModules.Monoidal.tensorHom
    (adj.unit.app P) (𝟙 N.val))

/-- Raw restriction compatibility for the unit-tensor map.  This exposes the
local adjunction normalization separately from the outer tensor comparison. -/
noncomputable def globalTensorUnitRestrictedRaw
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    (N : SheafOfModules (commRingSheafToRingSheaf R)) := by
  let F := PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)
  let FU := PresheafOfModules.sheafification (𝟙 ((commRingSheafToRingSheaf R).over U).obj)
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app P
  exact FU.map
    (((PresheafOfModules.pushforward₀OfCommRingCat
      (Over.forget U) ((sheafToPresheaf J CommRingCat).obj R)).map
      (PresheafOfModules.Monoidal.tensorHom η (𝟙 N.val))) ≫
      (PresheafOfModules.pushforward₀_tensorIso
        (R := (sheafToPresheaf J CommRingCat).obj R)
        (F := Over.forget U) (F.obj P).val N.val).hom)

noncomputable def localTensorUnitRestrictedRaw
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    (N : SheafOfModules (commRingSheafToRingSheaf R)) := by
  let FU := PresheafOfModules.sheafification (𝟙 ((commRingSheafToRingSheaf R).over U).obj)
  let eP := overFunctor_sheafificationComparisonIso (R := commRingSheafToRingSheaf R) U P
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).unit.app
    ((PresheafOfModules.pushforward₀OfCommRingCat
      (Over.forget U) ((sheafToPresheaf J CommRingCat).obj R)).obj P)
  exact FU.map
    ((PresheafOfModules.pushforward₀_tensorIso
      (R := (sheafToPresheaf J CommRingCat).obj R)
      (F := Over.forget U) P N.val).hom ≫
      PresheafOfModules.Monoidal.tensorHom
        (η ≫ eP.hom.val) ((PresheafOfModules.pushforward₀OfCommRingCat
          (Over.forget U) ((sheafToPresheaf J CommRingCat).obj R)).map (𝟙 N.val)))

theorem globalTensorUnitRestrictedRaw_eq_localTensorUnitRestrictedRaw
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    (N : SheafOfModules (commRingSheafToRingSheaf R)) :
    globalTensorUnitRestrictedRaw R U P N =
      localTensorUnitRestrictedRaw R U P N := by
  unfold globalTensorUnitRestrictedRaw localTensorUnitRestrictedRaw
  dsimp
  let F := PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)
  let FU := PresheafOfModules.sheafification (𝟙 ((commRingSheafToRingSheaf R).over U).obj)
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app P
  let ηU := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).unit.app
    ((PresheafOfModules.pushforward₀OfCommRingCat
      (Over.forget U) ((sheafToPresheaf J CommRingCat).obj R)).obj P)
  let eP := overFunctor_sheafificationComparisonIso (R := commRingSheafToRingSheaf R) U P
  have hunit : ηU ≫ eP.hom.val =
      (PresheafOfModules.pushforward
        (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map η := by
    exact overFunctor_sheafificationComparison_unit_comp
      (R := commRingSheafToRingSheaf R) U P
  have hpre := PresheafOfModules.pushforward₀_tensorIso_naturality
    (F := Over.forget U) η (𝟙 N.val)
  have hunit₀ : ηU ≫ eP.hom.val =
      (PresheafOfModules.pushforward₀OfCommRingCat
        (Over.forget U) ((sheafToPresheaf J CommRingCat).obj R)).map η := by
    exact hunit
  have hpreF := congrArg FU.map hpre
  rw [← hunit₀] at hpreF
  exact hpreF

/-- The normalized restricted unit-tensor map can be read as two successive
sheafification maps: first the strong-monoidal restriction comparison, then
the local unit followed by the sheafification comparison.  Keeping this
factorization explicit avoids asking Lean to normalize both over-site
ring-sheaf presentations inside the final global-to-local tensor square. -/
theorem globalTensorUnitRestrictedRaw_eq_normalized_composite
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    (N : SheafOfModules (commRingSheafToRingSheaf R)) :
    globalTensorUnitRestrictedRaw R U P N =
      (PresheafOfModules.sheafification
        (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map
        (PresheafOfModules.pushforward₀_tensorIso
          (R := R.obj) (F := Over.forget U) P N.val).hom ≫
      (PresheafOfModules.sheafification
        (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map
        (PresheafOfModules.Monoidal.tensorHom
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).unit.app
            ((PresheafOfModules.pushforward₀OfCommRingCat
              (Over.forget U) ((sheafToPresheaf J CommRingCat).obj R)).obj P) ≫
            (overFunctor_sheafificationComparisonIso U P).hom.val)
          ((PresheafOfModules.pushforward₀OfCommRingCat
            (Over.forget U) ((sheafToPresheaf J CommRingCat).obj R)).map
            (𝟙 N.val))) := by
  rw [globalTensorUnitRestrictedRaw_eq_localTensorUnitRestrictedRaw]
  unfold localTensorUnitRestrictedRaw
  dsimp
  let FU := PresheafOfModules.sheafification
    (𝟙 ((commRingSheafToRingSheaf R).over U).obj)
  change FU.map (_ ≫ _) = FU.map _ ≫ FU.map _
  exact FU.map_comp _ _

/-- Postcomposing the generic comparison by a tensor map in its left factor
combines the local unit and that map before sheafification. -/
theorem commRingSheafTensorSheafificationRightComparison_comp_tensorMap_left
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    (N M : SheafOfModules (commRingSheafToRingSheaf R))
    (f : (PresheafOfModules.sheafification
      (𝟙 (commRingSheafToRingSheaf R).obj)).obj P ⟶ M) :
    commRingSheafTensorSheafificationRightComparison R P N ≫
      commRingSheafTensorMap R f (𝟙 N) =
    (PresheafOfModules.sheafification
      (𝟙 (commRingSheafToRingSheaf R).obj)).map
      (PresheafOfModules.Monoidal.tensorHom
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app P ≫ f.val)
        (𝟙 N.val)) := by
  let F := PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheafToRingSheaf R).obj)
  letI : MonoidalCategory (PresheafOfModules (commRingSheafToRingSheaf R).obj) :=
    PresheafOfModules.monoidalCategory
  change F.map (PresheafOfModules.Monoidal.tensorHom
      (adj.unit.app P) (𝟙 N.val)) ≫
      F.map (PresheafOfModules.Monoidal.tensorHom f.val (𝟙 N.val)) = _
  calc
    F.map (PresheafOfModules.Monoidal.tensorHom (adj.unit.app P) (𝟙 N.val)) ≫
        F.map (PresheafOfModules.Monoidal.tensorHom f.val (𝟙 N.val)) =
      F.map (PresheafOfModules.Monoidal.tensorHom (adj.unit.app P) (𝟙 N.val) ≫
        PresheafOfModules.Monoidal.tensorHom f.val (𝟙 N.val)) :=
      (F.map_comp _ _).symm
    _ = F.map (PresheafOfModules.Monoidal.tensorHom
        ((adj.unit.app P) ≫ f.val) ((𝟙 N.val) ≫ (𝟙 N.val))) :=
      congrArg F.map (tensorHom_comp_tensorHom (adj.unit.app P) (𝟙 N.val) f.val (𝟙 N.val))
    _ = F.map (PresheafOfModules.Monoidal.tensorHom
        ((adj.unit.app P) ≫ f.val) (𝟙 N.val)) := by
      congr 1
    _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem overFunctor_commRingSheafTensorSheafificationRightComparison_comp_left (R : Sheaf J CommRingCat.{u}) (U : C)
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    (N : SheafOfModules (commRingSheafToRingSheaf R)) :
    commRingSheafTensorSheafificationRightComparison (commRingSheafOver R U)
      ((PresheafOfModules.pushforward
        (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).obj P)
      ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N) ≫
    commRingSheafTensorMap (commRingSheafOver R U)
      (overFunctor_sheafificationComparisonIso U P).hom
      (𝟙 ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N)) =
    (PresheafOfModules.sheafification
      (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map
      (PresheafOfModules.Monoidal.tensorHom
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).unit.app
          ((PresheafOfModules.pushforward
            (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).obj P) ≫
          (overFunctor_sheafificationComparisonIso U P).hom.val)
        (𝟙 ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N).val)) := by
  exact commRingSheafTensorSheafificationRightComparison_comp_tensorMap_left
    (commRingSheafOver R U)
    ((PresheafOfModules.pushforward
      (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).obj P)
    ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N) _
    (overFunctor_sheafificationComparisonIso U P).hom

/-- The generic sheafification--right-tensor comparison is natural in its
right module factor. -/
theorem commRingSheafTensorSheafificationRightComparison_naturality
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    {N N' : SheafOfModules (commRingSheafToRingSheaf R)} (f : N ⟶ N') :
    commRingSheafTensorSheafificationRightComparison R P N ≫
      commRingSheafTensorMap R (𝟙 _) f =
    (PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)).map
      (PresheafOfModules.Monoidal.tensorHom (𝟙 P) f.val) ≫
      commRingSheafTensorSheafificationRightComparison R P N' := by
  let F := PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (commRingSheafToRingSheaf R).obj)
  let P' : PresheafOfModules (commRingSheafToRingSheaf R).obj := P
  let N₀ : PresheafOfModules (commRingSheafToRingSheaf R).obj := N.val
  let N₁ : PresheafOfModules (commRingSheafToRingSheaf R).obj := N'.val
  let f' : N₀ ⟶ N₁ := f.val
  letI : MonoidalCategory (PresheafOfModules (commRingSheafToRingSheaf R).obj) :=
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

noncomputable def commRingSheafTensorSheafificationRightComparisonUnitRawIso
    (R : Sheaf J CommRingCat.{u}) (P : PresheafOfModules (commRingSheafToRingSheaf R).obj) :
    PresheafOfModules.Monoidal.tensorObj P
      (SheafOfModules.unit (commRingSheafToRingSheaf R)).val ≅ P := by
  let P' : PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat) := P
  letI : MonoidalCategory
      (PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.monoidalCategory
  change P' ⊗ (PresheafOfModules.unit
    (R.obj ⋙ forget₂ CommRingCat RingCat)) ≅ P'
  exact ρ_ P'

/-- A unit normal form for the source and target of the canonical
sheafification--right-tensor comparison. -/
noncomputable def commRingSheafTensorSheafificationRightComparisonUnitNormalFormIso
    (R : Sheaf J CommRingCat.{u}) (P : PresheafOfModules (commRingSheafToRingSheaf R).obj) :
    (PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)).obj
      (PresheafOfModules.Monoidal.tensorObj P
        (SheafOfModules.unit (commRingSheafToRingSheaf R)).val) ≅
    commRingSheafTensor R
      ((PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)).obj P)
      (SheafOfModules.unit (commRingSheafToRingSheaf R)) := by
  let F := PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)
  let P' : PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat) := P
  letI : MonoidalCategory
      (PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.monoidalCategory
  have e : PresheafOfModules.Monoidal.tensorObj P'
      (SheafOfModules.unit (commRingSheafToRingSheaf R)).val ≅ P' := by
    change P' ⊗ (PresheafOfModules.unit
      (R.obj ⋙ forget₂ CommRingCat RingCat)) ≅ P'
    exact ρ_ P'
  exact F.mapIso e ≪≫
    (commRingSheafTensorUnitRightIso R (F.obj P)).symm

/-- The sheafification--right-tensor comparison is invertible on the unit. -/
theorem commRingSheafTensorSheafificationRightComparison_unit_isIso
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj) :
    IsIso (commRingSheafTensorSheafificationRightComparison R P
      (SheafOfModules.unit (commRingSheafToRingSheaf R))) := by
  let F := PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheafToRingSheaf R).obj)
  let P' : PresheafOfModules (commRingSheafToRingSheaf R).obj := P
  let FP : SheafOfModules (commRingSheafToRingSheaf R) := F.obj P
  let FP' : PresheafOfModules (commRingSheafToRingSheaf R).obj := FP.val
  letI : MonoidalCategory (PresheafOfModules (commRingSheafToRingSheaf R).obj) :=
    PresheafOfModules.monoidalCategory
  letI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  have hraw : PresheafOfModules.Monoidal.tensorHom
      (adj.unit.app P') (𝟙 (SheafOfModules.unit (commRingSheafToRingSheaf R)).val) ≫
      (ρ_ FP').hom =
      (commRingSheafTensorSheafificationRightComparisonUnitRawIso R P').hom ≫
        adj.unit.app P' := by
    unfold commRingSheafTensorSheafificationRightComparisonUnitRawIso
    dsimp
    exact rightUnitor_naturality (adj.unit.app P')
  have hcomp : commRingSheafTensorSheafificationRightComparison R P
      (SheafOfModules.unit (commRingSheafToRingSheaf R)) ≫
      (commRingSheafTensorUnitRightIso R (F.obj P)).hom =
      F.map (commRingSheafTensorSheafificationRightComparisonUnitRawIso R P).hom := by
    change F.map (PresheafOfModules.Monoidal.tensorHom
      (adj.unit.app P') (𝟙 (SheafOfModules.unit (commRingSheafToRingSheaf R)).val)) ≫
      (F.map (ρ_ FP').hom ≫ adj.counit.app FP) =
      F.map (commRingSheafTensorSheafificationRightComparisonUnitRawIso R P').hom
    calc
      F.map (PresheafOfModules.Monoidal.tensorHom
          (adj.unit.app P') (𝟙 (SheafOfModules.unit (commRingSheafToRingSheaf R)).val)) ≫
          (F.map (ρ_ FP').hom ≫ adj.counit.app FP) =
          (F.map (PresheafOfModules.Monoidal.tensorHom
            (adj.unit.app P') (𝟙 (SheafOfModules.unit (commRingSheafToRingSheaf R)).val)) ≫
            F.map (ρ_ FP').hom) ≫ adj.counit.app FP :=
        (Category.assoc _ _ _).symm
      _ = F.map (PresheafOfModules.Monoidal.tensorHom
            (adj.unit.app P') (𝟙 (SheafOfModules.unit (commRingSheafToRingSheaf R)).val) ≫
            (ρ_ FP').hom) ≫ adj.counit.app FP :=
        congrArg (fun q => q ≫ adj.counit.app FP)
          (F.map_comp _ _).symm
      _ = F.map ((commRingSheafTensorSheafificationRightComparisonUnitRawIso R P').hom ≫
            adj.unit.app P') ≫ adj.counit.app FP :=
        congrArg (fun q => q ≫ adj.counit.app FP) (congrArg F.map hraw)
      _ = (F.map (commRingSheafTensorSheafificationRightComparisonUnitRawIso R P').hom ≫
            F.map (adj.unit.app P')) ≫ adj.counit.app FP :=
        congrArg (fun q => q ≫ adj.counit.app FP) (F.map_comp _ _)
      _ = F.map (commRingSheafTensorSheafificationRightComparisonUnitRawIso R P').hom ≫
          (F.map (adj.unit.app P') ≫ adj.counit.app FP) := Category.assoc _ _ _
      _ = F.map (commRingSheafTensorSheafificationRightComparisonUnitRawIso R P').hom := by
        have htri : F.map (adj.unit.app P') ≫ adj.counit.app FP = 𝟙 _ := by
          change F.map (adj.unit.app P') ≫ adj.counit.app (F.obj P') = 𝟙 _
          exact adj.left_triangle_components P'
        rw [htri]
        exact Category.comp_id _
  have heq : commRingSheafTensorSheafificationRightComparison R P
      (SheafOfModules.unit (commRingSheafToRingSheaf R)) =
      (commRingSheafTensorSheafificationRightComparisonUnitNormalFormIso R P).hom := by
    calc
      commRingSheafTensorSheafificationRightComparison R P
          (SheafOfModules.unit (commRingSheafToRingSheaf R)) =
          commRingSheafTensorSheafificationRightComparison R P
            (SheafOfModules.unit (commRingSheafToRingSheaf R)) ≫ 𝟙 _ :=
        (Category.comp_id _).symm
      _ = commRingSheafTensorSheafificationRightComparison R P
          (SheafOfModules.unit (commRingSheafToRingSheaf R)) ≫
          ((commRingSheafTensorUnitRightIso R (F.obj P)).hom ≫
            (commRingSheafTensorUnitRightIso R (F.obj P)).inv) := by
        exact congrArg (fun q =>
          commRingSheafTensorSheafificationRightComparison R P
            (SheafOfModules.unit (commRingSheafToRingSheaf R)) ≫ q)
          (commRingSheafTensorUnitRightIso R (F.obj P)).hom_inv_id.symm
      _ = (commRingSheafTensorSheafificationRightComparison R P
          (SheafOfModules.unit (commRingSheafToRingSheaf R)) ≫
          (commRingSheafTensorUnitRightIso R (F.obj P)).hom) ≫
          (commRingSheafTensorUnitRightIso R (F.obj P)).inv := (Category.assoc _ _ _).symm
      _ = F.map (commRingSheafTensorSheafificationRightComparisonUnitRawIso R P).hom ≫
          (commRingSheafTensorUnitRightIso R (F.obj P)).inv :=
        congrArg (fun q => q ≫ (commRingSheafTensorUnitRightIso R (F.obj P)).inv) hcomp
      _ = (commRingSheafTensorSheafificationRightComparisonUnitNormalFormIso R P).hom := by
        unfold commRingSheafTensorSheafificationRightComparisonUnitNormalFormIso
        dsimp
        rfl
  rw [heq]
  exact (commRingSheafTensorSheafificationRightComparisonUnitNormalFormIso R P).isIso_hom


/-- An isomorphism of right factors induces the corresponding isomorphism of
presheaf tensor products before sheafification. -/
noncomputable def commRingSheafTensorSheafificationRightComparisonSourceCongr
    (R : Sheaf J CommRingCat.{u}) (P : PresheafOfModules (commRingSheafToRingSheaf R).obj) {N : SheafOfModules (commRingSheafToRingSheaf R)}
    (e : N ≅ SheafOfModules.unit (commRingSheafToRingSheaf R)) :
    PresheafOfModules.Monoidal.tensorObj P N.val ≅
      PresheafOfModules.Monoidal.tensorObj P (SheafOfModules.unit (commRingSheafToRingSheaf R)).val := by
  let eVal : N.val ≅ (SheafOfModules.unit (commRingSheafToRingSheaf R)).val :=
    { hom := e.hom.val
      inv := e.inv.val
      hom_inv_id := by
        exact congrArg (fun q => q.val) e.hom_inv_id
      inv_hom_id := by
        exact congrArg (fun q => q.val) e.inv_hom_id }
  letI : MonoidalCategory (PresheafOfModules (commRingSheafToRingSheaf R).obj) :=
    PresheafOfModules.monoidalCategory
  exact tensorIso (Iso.refl P) eVal


/-- The generic comparison is invertible whenever its right factor is
isomorphic to the structure module. -/
theorem commRingSheafTensorSheafificationRightComparison_isIso_of_iso_unit
    (R : Sheaf J CommRingCat.{u}) (P : PresheafOfModules (commRingSheafToRingSheaf R).obj) {N : SheafOfModules (commRingSheafToRingSheaf R)}
    (e : N ≅ SheafOfModules.unit (commRingSheafToRingSheaf R)) :
    IsIso (commRingSheafTensorSheafificationRightComparison R P N) := by
  let F := PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)
  let eRaw := commRingSheafTensorSheafificationRightComparisonSourceCongr R P e
  let eSource := F.mapIso eRaw
  let eTarget := SheafOfModules.commRingSheafTensorMapIso R (Iso.refl (F.obj P)) e
  letI : IsIso (commRingSheafTensorSheafificationRightComparison R P
      (SheafOfModules.unit (commRingSheafToRingSheaf R))) :=
    commRingSheafTensorSheafificationRightComparison_unit_isIso R P
  let eUnit := asIso (commRingSheafTensorSheafificationRightComparison R P
    (SheafOfModules.unit (commRingSheafToRingSheaf R)))
  have hnat := commRingSheafTensorSheafificationRightComparison_naturality R P e.hom
  have hnat' : commRingSheafTensorSheafificationRightComparison R P N ≫ eTarget.hom =
      eSource.hom ≫ commRingSheafTensorSheafificationRightComparison R P
        (SheafOfModules.unit (commRingSheafToRingSheaf R)) := by
    exact hnat
  let eComp := eSource ≪≫ eUnit ≪≫ eTarget.symm
  have heq : commRingSheafTensorSheafificationRightComparison R P N = eComp.hom := by
    calc
      commRingSheafTensorSheafificationRightComparison R P N =
          commRingSheafTensorSheafificationRightComparison R P N ≫ 𝟙 _ :=
        (Category.comp_id _).symm
      _ = commRingSheafTensorSheafificationRightComparison R P N ≫
          (eTarget.hom ≫ eTarget.inv) := by
        exact congrArg (fun q =>
          commRingSheafTensorSheafificationRightComparison R P N ≫ q)
          eTarget.hom_inv_id.symm
      _ = (commRingSheafTensorSheafificationRightComparison R P N ≫
          eTarget.hom) ≫ eTarget.inv := (Category.assoc _ _ _).symm
      _ = (eSource.hom ≫ commRingSheafTensorSheafificationRightComparison R P
          (SheafOfModules.unit (commRingSheafToRingSheaf R))) ≫ eTarget.inv :=
        congrArg (fun q => q ≫ eTarget.inv) hnat'
      _ = eComp.hom := by rfl
  rw [heq]
  exact eComp.isIso_hom



/-- The generic comparison packaged as an isomorphism after a chosen local
unit trivialization. -/
noncomputable def commRingSheafTensorSheafificationRightComparisonIso_of_iso_unit
    (R : Sheaf J CommRingCat.{u})
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    {N : SheafOfModules (commRingSheafToRingSheaf R)}
    (e : N ≅ SheafOfModules.unit (commRingSheafToRingSheaf R)) :
    (PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)).obj
      (PresheafOfModules.Monoidal.tensorObj P N.val) ≅
    commRingSheafTensor R
      ((PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf R).obj)).obj P) N := by
  letI : IsIso (commRingSheafTensorSheafificationRightComparison R P N) :=
    commRingSheafTensorSheafificationRightComparison_isIso_of_iso_unit R P e
  exact asIso (commRingSheafTensorSheafificationRightComparison R P N)

/-- On an over-site, the generic comparison is invertible whenever the
restricted right factor is trivial there. -/
theorem overFunctor_commRingSheafTensorSheafificationRightComparison_isIso_of_iso_unit
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    (N : SheafOfModules (commRingSheafToRingSheaf R))
    (e : (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N ≅
      SheafOfModules.unit ((commRingSheafToRingSheaf R).over U)) :
    IsIso (commRingSheafTensorSheafificationRightComparison (commRingSheafOver R U)
      ((PresheafOfModules.pushforward
        (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).obj P)
      ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N)) := by
  apply commRingSheafTensorSheafificationRightComparison_isIso_of_iso_unit
  exact e

/- The restricted raw unit-tensor map is invertible when the restricted right
factor is locally the structure module. -/
set_option backward.isDefEq.respectTransparency false in
theorem globalTensorUnitRestrictedRaw_isIso_of_iso_unit
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    (N : SheafOfModules (commRingSheafToRingSheaf R))
    (e : (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N ≅
      SheafOfModules.unit ((commRingSheafToRingSheaf R).over U)) :
    IsIso (globalTensorUnitRestrictedRaw R U P N) := by
  let c := commRingSheafTensorSheafificationRightComparison (commRingSheafOver R U)
      ((PresheafOfModules.pushforward
        (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).obj P)
      ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N)
  let t := commRingSheafTensorMap (commRingSheafOver R U)
      (overFunctor_sheafificationComparisonIso U P).hom
      (𝟙 ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N))
  letI : IsIso c :=
    overFunctor_commRingSheafTensorSheafificationRightComparison_isIso_of_iso_unit
      R U P N e
  letI : IsIso t := by
    let et := commRingSheafTensorMapIso (commRingSheafOver R U)
      (overFunctor_sheafificationComparisonIso U P)
      (Iso.refl ((SheafOfModules.overFunctor
        (commRingSheafToRingSheaf R) U).obj N))
    exact et.isIso_hom
  have hsecond : IsIso
      ((PresheafOfModules.sheafification
        (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map
        (PresheafOfModules.Monoidal.tensorHom
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).unit.app
            ((PresheafOfModules.pushforward₀OfCommRingCat
              (Over.forget U) ((sheafToPresheaf J CommRingCat).obj R)).obj P) ≫
            (overFunctor_sheafificationComparisonIso U P).hom.val)
          ((PresheafOfModules.pushforward₀OfCommRingCat
            (Over.forget U) ((sheafToPresheaf J CommRingCat).obj R)).map
            (𝟙 N.val)))) := by
    erw [← overFunctor_commRingSheafTensorSheafificationRightComparison_comp_left R U P N]
    change IsIso (c ≫ t)
    infer_instance
  rw [globalTensorUnitRestrictedRaw_eq_normalized_composite]
  infer_instance

/- After restriction, the global comparison differs from the local comparison
only by the canonical sheafification and tensor-restriction isomorphisms. -/
set_option backward.isDefEq.respectTransparency false in
theorem overFunctor_commRingSheafTensorSheafificationRightComparison_factorization
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    (N : SheafOfModules (commRingSheafToRingSheaf R)) :
    (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map
        (commRingSheafTensorSheafificationRightComparison R P N) ≫
      (overFunctor_commRingSheafTensorIso R U
        ((PresheafOfModules.sheafification
          (𝟙 (commRingSheafToRingSheaf R).obj)).obj P) N).hom =
    (overFunctor_sheafificationComparisonIso
      (R := commRingSheafToRingSheaf R) U
      (PresheafOfModules.Monoidal.tensorObj P N.val)).inv ≫
      globalTensorUnitRestrictedRaw R U P N := by
  rw [overFunctor_commRingSheafTensorIso_hom_eq]
  let F := PresheafOfModules.sheafification
    (𝟙 (commRingSheafToRingSheaf R).obj)
  let FU := PresheafOfModules.sheafification
    (𝟙 ((commRingSheafToRingSheaf R).over U).obj)
  let a := PresheafOfModules.Monoidal.tensorHom
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app P) (𝟙 N.val)
  have hn := overFunctor_sheafificationComparison_inv_naturality
    (R := commRingSheafToRingSheaf R) U a
  have hc : commRingSheafTensorSheafificationRightComparison R P N =
      F.map a := by rfl
  rw [hc]
  erw [← Category.assoc, hn, Category.assoc]
  unfold globalTensorUnitRestrictedRaw
  rw [← FU.map_comp]
  rfl

/- Restricting the global comparison to an open where its right factor is
trivial produces an isomorphism. -/
set_option backward.isDefEq.respectTransparency false in
theorem overFunctor_map_commRingSheafTensorSheafificationRightComparison_isIso_of_iso_unit
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (P : PresheafOfModules (commRingSheafToRingSheaf R).obj)
    (N : SheafOfModules (commRingSheafToRingSheaf R))
    (e : (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N ≅
      SheafOfModules.unit ((commRingSheafToRingSheaf R).over U)) :
    IsIso ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map
      (commRingSheafTensorSheafificationRightComparison R P N)) := by
  let g := (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map
      (commRingSheafTensorSheafificationRightComparison R P N)
  let q := (overFunctor_commRingSheafTensorIso R U
      ((PresheafOfModules.sheafification
        (𝟙 (commRingSheafToRingSheaf R).obj)).obj P) N).hom
  let p := (overFunctor_sheafificationComparisonIso
      (R := commRingSheafToRingSheaf R) U
      (PresheafOfModules.Monoidal.tensorObj P N.val)).inv
  let a := globalTensorUnitRestrictedRaw R U P N
  letI : IsIso q := by
    exact (overFunctor_commRingSheafTensorIso R U
      ((PresheafOfModules.sheafification
        (𝟙 (commRingSheafToRingSheaf R).obj)).obj P) N).isIso_hom
  letI : IsIso p := by
    exact (overFunctor_sheafificationComparisonIso
      (R := commRingSheafToRingSheaf R) U
      (PresheafOfModules.Monoidal.tensorObj P N.val)).isIso_inv
  letI : IsIso a := globalTensorUnitRestrictedRaw_isIso_of_iso_unit R U P N e
  haveI : IsIso (g ≫ q) := by
    rw [overFunctor_commRingSheafTensorSheafificationRightComparison_factorization]
    change IsIso (p ≫ a)
    infer_instance
  exact IsIso.of_isIso_comp_right g q

end SheafOfModules

/- Scheme-facing form of the local criterion for the global comparison. -/
set_option backward.isDefEq.respectTransparency false in
theorem restrict_schemeModuleTensorSheafificationRightComparison_isIso_of_over_iso_unit
    {X : Scheme.{u}} (U : X.Opens)
    (P : PresheafOfModules X.ringCatSheaf.obj) (N : X.Modules)
    (e : (SheafOfModules.overFunctor X.ringCatSheaf U).obj N ≅
      SheafOfModules.unit (X.ringCatSheaf.over U)) :
    IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map
      (schemeModuleTensorSheafificationRightComparison P N)) := by
  exact SheafOfModules.overFunctor_map_commRingSheafTensorSheafificationRightComparison_isIso_of_iso_unit
    X.sheaf U P N e

end PfaffianDescent
