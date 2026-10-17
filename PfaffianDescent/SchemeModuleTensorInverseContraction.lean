import PfaffianDescent.SchemeModuleTensor

/-!
# Canonical contraction for inverse module-sheaf tensor factors

This file constructs the actual morphism
`(M ⊗ N) ⊗ P ⟶ M` determined by a pairing `N ⊗ P ≅ O_X`.
The construction keeps both sheafification steps explicit.  It is the
component map needed to package tensoring by mutually inverse projective
twists as a categorical equivalence.
-/

noncomputable section
namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
universe u

variable {X : Scheme.{u}}

/- Forgetting a module-sheaf isomorphism gives an isomorphism of its
underlying presheaves. -/
noncomputable def schemeModuleIsoVal {M N : X.Modules} (e : M ≅ N) :
    M.val ≅ N.val where
  hom := e.hom.val
  inv := e.inv.val
  hom_inv_id := congrArg (fun q => q.val) e.hom_inv_id
  inv_hom_id := congrArg (fun q => q.val) e.inv_hom_id

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/- Forgetting an isomorphism of module sheaves gives an isomorphism of the
underlying presheaves. -/
noncomputable def isoVal {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules R} (e : M ≅ N) : M.val ≅ N.val where
  hom := e.hom.val
  inv := e.inv.val
  hom_inv_id := congrArg (fun q => q.val) e.hom_inv_id
  inv_hom_id := congrArg (fun q => q.val) e.inv_hom_id

/- Invertibility of a sheafification unit transports across an isomorphism
of presheaves. -/
set_option backward.isDefEq.respectTransparency false in
theorem sheafificationUnit_isIso_of_iso
    (R : Sheaf J RingCat.{u})
    {P Q : PresheafOfModules R.obj} (e : P ≅ Q)
    [IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 R.obj)).unit.app Q)] :
    IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 R.obj)).unit.app P) := by
  let F := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let feVal := isoVal (F.mapIso e)
  haveI : IsIso e.hom := e.isIso_hom
  haveI : IsIso feVal.hom := feVal.isIso_hom
  have hn := adj.unit.naturality e.hom
  have hn' : e.hom ≫ adj.unit.app Q =
      adj.unit.app P ≫ feVal.hom := by
    exact hn
  haveI : IsIso (adj.unit.app P ≫ feVal.hom) := by
    rw [← hn']
    infer_instance
  exact IsIso.of_isIso_comp_right (adj.unit.app P) feVal.hom

/- The sheafification unit on the presheaf tensor of two trivial module
sheaves is already an isomorphism. -/
set_option backward.isDefEq.respectTransparency false in
theorem sheafificationUnit_tensor_isIso_of_iso_units
    (R : Sheaf J CommRingCat.{u})
    (N P : SheafOfModules (commRingSheafToRingSheaf R))
    (eN : N ≅ SheafOfModules.unit (commRingSheafToRingSheaf R))
    (eP : P ≅ SheafOfModules.unit (commRingSheafToRingSheaf R)) :
    IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app
        (PresheafOfModules.Monoidal.tensorObj N.val P.val)) := by
  let F := PresheafOfModules.sheafification
    (𝟙 (commRingSheafToRingSheaf R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (commRingSheafToRingSheaf R).obj)
  let Q := PresheafOfModules.Monoidal.tensorObj N.val P.val
  let U := PresheafOfModules.unit (commRingSheafToRingSheaf R).obj
  let eRaw : Q ≅ U := by
    letI : MonoidalCategory
        (PresheafOfModules (commRingSheafToRingSheaf R).obj) :=
      PresheafOfModules.monoidalCategory
    exact tensorIso (isoVal eN) (isoVal eP) ≪≫
      commRingSheafTensorUnitRightRawIso R
        (SheafOfModules.unit (commRingSheafToRingSheaf R))
  haveI hunitU : IsIso (adj.unit.app U) := by
    let S := SheafOfModules.unit (commRingSheafToRingSheaf R)
    let ec := asIso (adj.counit.app S)
    let ecVal := isoVal ec
    haveI : IsIso ecVal.hom := ecVal.isIso_hom
    have ht := adj.right_triangle_components S
    have ht' : adj.unit.app U ≫ ecVal.hom = 𝟙 U := by
      exact ht
    haveI : IsIso (adj.unit.app U ≫ ecVal.hom) := by
      rw [ht']
      infer_instance
    exact IsIso.of_isIso_comp_right (adj.unit.app U) ecVal.hom
  haveI : IsIso eRaw.hom := eRaw.isIso_hom
  let mapRawVal := isoVal (F.mapIso eRaw)
  haveI : IsIso mapRawVal.hom := mapRawVal.isIso_hom
  have hn := adj.unit.naturality eRaw.hom
  have hn' : eRaw.hom ≫ adj.unit.app U =
      adj.unit.app Q ≫ mapRawVal.hom := by
    exact hn
  haveI : IsIso (adj.unit.app Q ≫ mapRawVal.hom) := by
    rw [← hn']
    infer_instance
  exact IsIso.of_isIso_comp_right (adj.unit.app Q) mapRawVal.hom

/- Restricting the global sheafification unit on a tensor of two module
sheaves is invertible on any open where both factors are trivial. -/
set_option backward.isDefEq.respectTransparency false in
theorem pushforward_sheafificationUnit_tensor_isIso_of_over_iso_units
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (N P : SheafOfModules (commRingSheafToRingSheaf R))
    (eN : (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N ≅
      SheafOfModules.unit ((commRingSheafToRingSheaf R).over U))
    (eP : (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj P ≅
      SheafOfModules.unit ((commRingSheafToRingSheaf R).over U)) :
    IsIso ((PresheafOfModules.pushforward
      (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app
          (PresheafOfModules.Monoidal.tensorObj N.val P.val))) := by
  let H := SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U
  let G := PresheafOfModules.pushforward
    (𝟙 ((commRingSheafToRingSheaf R).over U).obj)
  let adjU := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((commRingSheafToRingSheaf R).over U).obj)
  let Q := PresheafOfModules.Monoidal.tensorObj N.val P.val
  let QU := PresheafOfModules.Monoidal.tensorObj
    (R := (commRingSheafOver R U).obj) (H.obj N).val (H.obj P).val
  let t : G.obj Q ≅ QU := PresheafOfModules.pushforward₀_tensorIso
    (R := R.obj) (F := Over.forget U) N.val P.val
  haveI hunitQU : IsIso (adjU.unit.app QU) :=
    sheafificationUnit_tensor_isIso_of_iso_units
      (commRingSheafOver R U) (H.obj N) (H.obj P) eN eP
  haveI hunitGQ : IsIso (adjU.unit.app (G.obj Q)) :=
    sheafificationUnit_isIso_of_iso
      ((commRingSheafToRingSheaf R).over U) t
  let c := overFunctor_sheafificationComparisonIso
    (R := commRingSheafToRingSheaf R) U Q
  let cVal := isoVal c
  haveI hcVal : IsIso cVal.hom := cVal.isIso_hom
  have hglobal := overFunctor_sheafificationComparison_unit_comp
    (R := commRingSheafToRingSheaf R) U Q
  have hglobal' : adjU.unit.app (G.obj Q) ≫ cVal.hom =
      G.map ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app Q) := by
    exact hglobal
  rw [← hglobal']
  infer_instance

/- The restricted raw adjoint of an inverse pairing is an isomorphism of
presheaves wherever both paired factors are trivial. -/
set_option backward.isDefEq.respectTransparency false in
theorem pushforward_pairingRaw_isIso_of_over_iso_units
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (N P : SheafOfModules (commRingSheafToRingSheaf R))
    (e : commRingSheafTensor R N P ≅
      SheafOfModules.unit (commRingSheafToRingSheaf R))
    (eN : (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N ≅
      SheafOfModules.unit ((commRingSheafToRingSheaf R).over U))
    (eP : (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj P ≅
      SheafOfModules.unit ((commRingSheafToRingSheaf R).over U)) :
    IsIso ((PresheafOfModules.pushforward
      (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app
            (PresheafOfModules.Monoidal.tensorObj N.val P.val) ≫ e.hom.val)) := by
  let G := PresheafOfModules.pushforward
    (𝟙 ((commRingSheafToRingSheaf R).over U).obj)
  let Q := PresheafOfModules.Monoidal.tensorObj N.val P.val
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app Q
  haveI hη : IsIso (G.map η) :=
    pushforward_sheafificationUnit_tensor_isIso_of_over_iso_units
      R U N P eN eP
  let eVal := isoVal e
  haveI : IsIso eVal.hom := eVal.isIso_hom
  haveI : IsIso (G.map eVal.hom) := by infer_instance
  change IsIso (G.map (η ≫ eVal.hom))
  rw [G.map_comp]
  infer_instance

/- Restriction carries an arbitrary left tensor of the raw pairing to an
isomorphism of presheaves on an open where both paired factors are trivial. -/
set_option backward.isDefEq.respectTransparency false in
theorem pushforward_pairingRaw_tensor_isIso_of_over_iso_units
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (M N P : SheafOfModules (commRingSheafToRingSheaf R))
    (e : commRingSheafTensor R N P ≅
      SheafOfModules.unit (commRingSheafToRingSheaf R))
    (eN : (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N ≅
      SheafOfModules.unit ((commRingSheafToRingSheaf R).over U))
    (eP : (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj P ≅
      SheafOfModules.unit ((commRingSheafToRingSheaf R).over U)) :
    IsIso ((PresheafOfModules.pushforward
      (𝟙 ((commRingSheafToRingSheaf R).over U).obj)).map
      (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app
            (PresheafOfModules.Monoidal.tensorObj N.val P.val) ≫ e.hom.val))) := by
  let G := PresheafOfModules.pushforward
    (𝟙 ((commRingSheafToRingSheaf R).over U).obj)
  let Q := PresheafOfModules.Monoidal.tensorObj N.val P.val
  let pair := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app Q ≫ e.hom.val
  let h := PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) pair
  haveI hpair : IsIso (G.map pair) :=
    pushforward_pairingRaw_isIso_of_over_iso_units R U N P e eN eP
  haveI hid : IsIso (G.map (𝟙 M.val)) := by infer_instance
  letI : MonoidalCategory
      (PresheafOfModules ((commRingSheafToRingSheaf R).over U).obj) := by
    change MonoidalCategory (PresheafOfModules
      ((commRingSheafOver R U).obj ⋙ forget₂ CommRingCat RingCat))
    exact PresheafOfModules.monoidalCategory
  let localTensor := PresheafOfModules.Monoidal.tensorHom
    (R := (commRingSheafOver R U).obj) (G.map (𝟙 M.val)) (G.map pair)
  let localTensorIso := tensorIso (asIso (G.map (𝟙 M.val)))
    (asIso (G.map pair))
  haveI hlocalTensor : IsIso localTensor := by
    exact localTensorIso.isIso_hom
  let tSource := PresheafOfModules.pushforward₀_tensorIso
    (R := R.obj) (F := Over.forget U) M.val Q
  let tTarget := PresheafOfModules.pushforward₀_tensorIso
    (R := R.obj) (F := Over.forget U) M.val
      (PresheafOfModules.unit (commRingSheafToRingSheaf R).obj)
  haveI : IsIso tSource.hom := tSource.isIso_hom
  haveI : IsIso tTarget.hom := tTarget.isIso_hom
  have hn := PresheafOfModules.pushforward₀_tensorIso_naturality
    (F := Over.forget U) (𝟙 M.val) pair
  have hn' : G.map h ≫ tTarget.hom =
      tSource.hom ≫ localTensor := by
    exact hn
  haveI : IsIso (G.map h ≫ tTarget.hom) := by
    rw [hn']
    exact (tSource ≪≫ localTensorIso).isIso_hom
  exact IsIso.of_isIso_comp_right (G.map h) tTarget.hom

/- The sheafified tensor of an inverse pairing restricts to an isomorphism
on every open where both inverse factors are trivial. -/
set_option backward.isDefEq.respectTransparency false in
theorem overFunctor_map_pairingRaw_tensor_isIso_of_iso_units
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (M N P : SheafOfModules (commRingSheafToRingSheaf R))
    (e : commRingSheafTensor R N P ≅
      SheafOfModules.unit (commRingSheafToRingSheaf R))
    (eN : (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj N ≅
      SheafOfModules.unit ((commRingSheafToRingSheaf R).over U))
    (eP : (SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).obj P ≅
      SheafOfModules.unit ((commRingSheafToRingSheaf R).over U)) :
    IsIso ((SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U).map
      ((PresheafOfModules.sheafification
        (𝟙 (commRingSheafToRingSheaf R).obj)).map
        (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app
              (PresheafOfModules.Monoidal.tensorObj N.val P.val) ≫ e.hom.val)))) := by
  let H := SheafOfModules.overFunctor (commRingSheafToRingSheaf R) U
  let G := PresheafOfModules.pushforward
    (𝟙 ((commRingSheafToRingSheaf R).over U).obj)
  let F := PresheafOfModules.sheafification
    (𝟙 (commRingSheafToRingSheaf R).obj)
  let FU := PresheafOfModules.sheafification
    (𝟙 ((commRingSheafToRingSheaf R).over U).obj)
  let Q := PresheafOfModules.Monoidal.tensorObj N.val P.val
  let pair := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (commRingSheafToRingSheaf R).obj)).unit.app Q ≫ e.hom.val
  let A := PresheafOfModules.Monoidal.tensorObj M.val Q
  let B := PresheafOfModules.Monoidal.tensorObj M.val
    (SheafOfModules.unit (commRingSheafToRingSheaf R)).val
  let h := PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) pair
  haveI hpush : IsIso (G.map h) :=
    pushforward_pairingRaw_tensor_isIso_of_over_iso_units
      R U M N P e eN eP
  let localMapIso := FU.mapIso (asIso (G.map h))
  let cA := overFunctor_sheafificationComparisonIso
    (R := commRingSheafToRingSheaf R) U A
  let cB := overFunctor_sheafificationComparisonIso
    (R := commRingSheafToRingSheaf R) U B
  have hn := overFunctor_sheafificationComparison_inv_naturality
    (R := commRingSheafToRingSheaf R) U h
  have hn' : H.map (F.map h) ≫ cB.inv =
      cA.inv ≫ localMapIso.hom := by
    exact hn
  haveI : IsIso cB.inv := cB.isIso_inv
  haveI : IsIso (H.map (F.map h) ≫ cB.inv) := by
    rw [hn']
    exact (cA.symm ≪≫ localMapIso).isIso_hom
  exact IsIso.of_isIso_comp_right (H.map (F.map h)) cB.inv

end SheafOfModules

noncomputable def schemeModuleTensorRawAssociator (M N P : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModules.Monoidal.tensorObj
        (PresheafOfModules.Monoidal.tensorObj M.val N.val) P.val) ≅
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModules.Monoidal.tensorObj M.val
        (PresheafOfModules.Monoidal.tensorObj N.val P.val)) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let M' : PresheafOfModules X.ringCatSheaf.obj := M.val
  let N' : PresheafOfModules X.ringCatSheaf.obj := N.val
  let P' : PresheafOfModules X.ringCatSheaf.obj := P.val
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  exact F.mapIso (α_ M' N' P')

noncomputable def schemeModuleTensorPairingRaw
    (N P : X.Modules)
    (e : schemeModuleTensor N P ≅ SheafOfModules.unit X.ringCatSheaf) :
    PresheafOfModules.Monoidal.tensorObj N.val P.val ⟶
      PresheafOfModules.unit X.ringCatSheaf.obj := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  exact adj.unit.app
      (PresheafOfModules.Monoidal.tensorObj N.val P.val) ≫ e.hom.val

/- An isomorphism of sheaf tensor products induces an isomorphism after
sheafifying its raw adjoint pairing. -/
set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleTensorPairingRaw_sheafification_isIso (N P : X.Modules)
    (e : schemeModuleTensor N P ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (schemeModuleTensorPairingRaw N P e)) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let Q := PresheafOfModules.Monoidal.tensorObj N.val P.val
  haveI hu : IsIso (F.map (adj.unit.app Q)) := by
    haveI hc : IsIso (adj.counit.app (F.obj Q)) := inferInstance
    have ht := adj.left_triangle_components Q
    change F.map (adj.unit.app Q) ≫ adj.counit.app (F.obj Q) =
      𝟙 (F.obj Q) at ht
    haveI hcomp : IsIso
        (F.map (adj.unit.app Q) ≫ adj.counit.app (F.obj Q)) := by
      rw [ht]
      infer_instance
    exact IsIso.of_isIso_comp_right (F.map (adj.unit.app Q))
      (adj.counit.app (F.obj Q))
  have hrestrict :
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map e.hom.val =
        e.hom.val := by rfl
  have hn := adj.counit.naturality e.hom
  change F.map ((PresheafOfModules.restrictScalars
      (𝟙 X.ringCatSheaf.obj)).map e.hom.val) ≫
      adj.counit.app (SheafOfModules.unit X.ringCatSheaf) =
    adj.counit.app (schemeModuleTensor N P) ≫ e.hom at hn
  rw [hrestrict] at hn
  haveI hcTarget : IsIso
      (adj.counit.app (SheafOfModules.unit X.ringCatSheaf)) := inferInstance
  haveI hcompE : IsIso (F.map e.hom.val ≫
      adj.counit.app (SheafOfModules.unit X.ringCatSheaf)) := by
    rw [hn]
    infer_instance
  haveI hef : IsIso (F.map e.hom.val) :=
    IsIso.of_isIso_comp_right (F.map e.hom.val)
      (adj.counit.app (SheafOfModules.unit X.ringCatSheaf))
  change IsIso (F.map (adj.unit.app Q ≫ e.hom.val))
  rw [F.map_comp]
  infer_instance

/- If both factors are trivial module sheaves, their raw pairing is already
an isomorphism before sheafification. -/
set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleTensorPairingRaw_isIso_of_iso_units (N P : X.Modules)
    (e : schemeModuleTensor N P ≅ SheafOfModules.unit X.ringCatSheaf)
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (eP : P ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (schemeModuleTensorPairingRaw N P e) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let Q := PresheafOfModules.Monoidal.tensorObj N.val P.val
  let U := PresheafOfModules.unit X.ringCatSheaf.obj
  let eRaw : Q ≅ U := by
    letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
      PresheafOfModules.monoidalCategory
    exact tensorIso (schemeModuleIsoVal eN) (schemeModuleIsoVal eP) ≪≫
      schemeModuleTensorUnitRightRawIso (SheafOfModules.unit X.ringCatSheaf)
  haveI hunitU : IsIso (adj.unit.app U) := by
    let S := SheafOfModules.unit X.ringCatSheaf
    let ec := asIso (adj.counit.app S)
    let ecVal := schemeModuleIsoVal ec
    haveI : IsIso ecVal.hom := ecVal.isIso_hom
    have ht := adj.right_triangle_components S
    have ht' : adj.unit.app U ≫ ecVal.hom = 𝟙 U := by
      exact ht
    haveI : IsIso (adj.unit.app U ≫ ecVal.hom) := by
      rw [ht']
      infer_instance
    exact IsIso.of_isIso_comp_right (adj.unit.app U) ecVal.hom
  haveI heRaw : IsIso eRaw.hom := eRaw.isIso_hom
  haveI hmapRaw : IsIso (F.map eRaw.hom) := by infer_instance
  let mapRawVal := schemeModuleIsoVal (F.mapIso eRaw)
  haveI hmapRawVal : IsIso mapRawVal.hom := mapRawVal.isIso_hom
  have hn := adj.unit.naturality eRaw.hom
  have hn' : eRaw.hom ≫ adj.unit.app U =
      adj.unit.app Q ≫ mapRawVal.hom := by
    exact hn
  haveI hcomp : IsIso (adj.unit.app Q ≫ mapRawVal.hom) := by
    rw [← hn']
    infer_instance
  haveI hunitQ : IsIso (adj.unit.app Q) :=
    IsIso.of_isIso_comp_right (adj.unit.app Q) mapRawVal.hom
  haveI heVal : IsIso e.hom.val := by
    let ee := schemeModuleIsoVal e
    exact ee.isIso_hom
  change IsIso (adj.unit.app Q ≫ e.hom.val)
  infer_instance

/- Tensoring a raw pairing between locally trivial factors by an arbitrary
underlying module presheaf preserves invertibility, hence so does
sheafification. -/
set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleTensorPairingRaw_tensor_isIso_of_iso_units (M N P : X.Modules)
    (e : schemeModuleTensor N P ≅ SheafOfModules.unit X.ringCatSheaf)
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (eP : P ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
          (schemeModuleTensorPairingRaw N P e))) := by
  letI : IsIso (schemeModuleTensorPairingRaw N P e) :=
    schemeModuleTensorPairingRaw_isIso_of_iso_units N P e eN eP
  let pairIso := asIso (schemeModuleTensorPairingRaw N P e)
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  let tensorPairIso := tensorIso (Iso.refl M.val) pairIso
  exact ((PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).mapIso tensorPairIso).isIso_hom

/- Local trivializations of both inverse factors on a cover make every
left tensor of their raw pairing invertible after sheafification. -/
set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleTensorPairingRaw_tensor_isIso_of_coversTop
    {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (M N P : X.Modules)
    (e : schemeModuleTensor N P ≅ SheafOfModules.unit X.ringCatSheaf)
    (eN : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj N ≅
      SheafOfModules.unit (X.ringCatSheaf.over (U j)))
    (eP : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj P ≅
      SheafOfModules.unit (X.ringCatSheaf.over (U j))) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
          (schemeModuleTensorPairingRaw N P e))) := by
  let f := (PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
        (schemeModuleTensorPairingRaw N P e))
  let H : ∀ j, Functor X.Modules
      (SheafOfModules (X.ringCatSheaf.over (U j))) :=
    fun j => SheafOfModules.overFunctor X.ringCatSheaf (U j)
  let hH : JointlyReflectIsomorphisms H :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U hU
  letI : ∀ j, IsIso ((H j).map f) := by
    intro j
    exact SheafOfModules.overFunctor_map_pairingRaw_tensor_isIso_of_iso_units
      X.sheaf (U j) M N P e (eN j) (eP j)
  exact hH.isIso f

noncomputable def schemeModuleTensorContraction
    (M N P : X.Modules)
    (e : schemeModuleTensor N P ≅ SheafOfModules.unit X.ringCatSheaf)
    [IsIso (schemeModuleTensorSheafificationRightComparison
      (PresheafOfModules.Monoidal.tensorObj M.val N.val) P)] :
    schemeModuleTensor (schemeModuleTensor M N) P ⟶ M := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let M' : PresheafOfModules X.ringCatSheaf.obj := M.val
  let N' : PresheafOfModules X.ringCatSheaf.obj := N.val
  let P' : PresheafOfModules X.ringCatSheaf.obj := P.val
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  let c := schemeModuleTensorSheafificationRightComparison
    (PresheafOfModules.Monoidal.tensorObj M.val N.val) P
  let hc : IsIso c := by
    dsimp only [c]
    infer_instance
  exact
    (@inv _ _ _ _ c hc) ≫
    (schemeModuleTensorRawAssociator M N P).hom ≫
    F.map (PresheafOfModules.Monoidal.tensorHom (𝟙 M')
      (schemeModuleTensorPairingRaw N P e)) ≫
    F.map (ρ_ M').hom ≫
    adj.counit.app M

end PfaffianDescent

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
universe u
variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleTensorSheafificationRightComparison_naturality_left
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (h : P ⟶ Q)
    (N : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom h (𝟙 N.val)) ≫
      schemeModuleTensorSheafificationRightComparison Q N =
    schemeModuleTensorSheafificationRightComparison P N ≫
      schemeModuleTensorMap
        ((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map h) (𝟙 N) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  change F.map (PresheafOfModules.Monoidal.tensorHom h (𝟙 N.val)) ≫
      F.map (PresheafOfModules.Monoidal.tensorHom
        (adj.unit.app Q) (𝟙 N.val)) =
    F.map (PresheafOfModules.Monoidal.tensorHom
        (adj.unit.app P) (𝟙 N.val)) ≫
      F.map (PresheafOfModules.Monoidal.tensorHom
        (F.map h).val (𝟙 N.val))
  let a := PresheafOfModules.Monoidal.tensorHom h (𝟙 N.val)
  let b := PresheafOfModules.Monoidal.tensorHom
    (adj.unit.app Q) (𝟙 N.val)
  let c := PresheafOfModules.Monoidal.tensorHom
    (adj.unit.app P) (𝟙 N.val)
  let d := PresheafOfModules.Monoidal.tensorHom
    (F.map h).val (𝟙 N.val)
  have hraw : a ≫ b = c ≫ d := by
    dsimp only [a, b, c, d]
    calc
      PresheafOfModules.Monoidal.tensorHom h (𝟙 N.val) ≫
          PresheafOfModules.Monoidal.tensorHom
            (adj.unit.app Q) (𝟙 N.val) =
        PresheafOfModules.Monoidal.tensorHom
          (h ≫ adj.unit.app Q) ((𝟙 N.val) ≫ (𝟙 N.val)) :=
        tensorHom_comp_tensorHom h (𝟙 N.val)
          (adj.unit.app Q) (𝟙 N.val)
      _ = PresheafOfModules.Monoidal.tensorHom
          (adj.unit.app P ≫ (F.map h).val)
          ((𝟙 N.val) ≫ (𝟙 N.val)) := by
        have hu : h ≫ adj.unit.app Q =
            adj.unit.app P ≫ (F.map h).val := by
          exact adj.unit.naturality h
        exact congrArg (fun q => PresheafOfModules.Monoidal.tensorHom q
          ((𝟙 N.val) ≫ (𝟙 N.val))) hu
      _ = PresheafOfModules.Monoidal.tensorHom
            (adj.unit.app P) (𝟙 N.val) ≫
          PresheafOfModules.Monoidal.tensorHom
            (F.map h).val (𝟙 N.val) :=
        (tensorHom_comp_tensorHom (adj.unit.app P) (𝟙 N.val)
          (F.map h).val (𝟙 N.val)).symm
  exact (F.map_comp a b).symm.trans
    ((congrArg F.map hraw).trans (F.map_comp c d))

/- Inverse form of left naturality for the sheafification--right-tensor
comparison.  This is the form needed to prove naturality of contraction by an
invertible tensor factor. -/
set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleTensorSheafificationRightComparison_inv_naturality_left
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (h : P ⟶ Q)
    (N : X.Modules)
    [hP : IsIso (schemeModuleTensorSheafificationRightComparison P N)]
    [hQ : IsIso (schemeModuleTensorSheafificationRightComparison Q N)] :
    schemeModuleTensorMap
        ((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map h) (𝟙 N) ≫
      (@inv _ _ _ _
        (schemeModuleTensorSheafificationRightComparison Q N) hQ) =
    (@inv _ _ _ _
      (schemeModuleTensorSheafificationRightComparison P N) hP) ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom h (𝟙 N.val)) := by
  letI : Mono (schemeModuleTensorSheafificationRightComparison Q N) :=
    @IsIso.mono_of_iso _ _ _ _ _ hQ
  rw [← cancel_mono (schemeModuleTensorSheafificationRightComparison Q N)]
  simp only [Category.assoc]
  rw [← Category.assoc,
    schemeModuleTensorSheafificationRightComparison_naturality_left]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleTensorContraction_naturality
    {M M' N P : X.Modules} (f : M ⟶ M')
    (e : schemeModuleTensor N P ≅ SheafOfModules.unit X.ringCatSheaf)
    [IsIso (schemeModuleTensorSheafificationRightComparison
      (PresheafOfModules.Monoidal.tensorObj M.val N.val) P)]
    [IsIso (schemeModuleTensorSheafificationRightComparison
      (PresheafOfModules.Monoidal.tensorObj M'.val N.val) P)] :
    schemeModuleTensorMap (schemeModuleTensorMap f (𝟙 N)) (𝟙 P) ≫
      schemeModuleTensorContraction M' N P e =
    schemeModuleTensorContraction M N P e ≫ f := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let h := PresheafOfModules.Monoidal.tensorHom f.val (𝟙 N.val)
  have hout :
      schemeModuleTensorMap (schemeModuleTensorMap f (𝟙 N)) (𝟙 P) =
        schemeModuleTensorMap (F.map h) (𝟙 P) := by
    rfl
  rw [hout]
  simp only [schemeModuleTensorContraction]
  rw [← Category.assoc,
    schemeModuleTensorSheafificationRightComparison_inv_naturality_left]
  simp only [Category.assoc]
  rw [cancel_epi]
  let pair := schemeModuleTensorPairingRaw N P e
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  have hfactor :
      f.val ⊗ₘ pair =
        ((𝟙 M.val) ⊗ₘ pair) ≫
          (f.val ⊗ₘ (𝟙 (PresheafOfModules.unit X.ringCatSheaf.obj))) := by
    simpa only [Category.id_comp, Category.comp_id] using
      (tensorHom_comp_tensorHom (𝟙 M.val) pair f.val
        (𝟙 (PresheafOfModules.unit X.ringCatSheaf.obj))).symm
  have hunit :
      (f.val ⊗ₘ (𝟙 (PresheafOfModules.unit X.ringCatSheaf.obj))) ≫
          (ρ_ M'.val).hom =
        (ρ_ M.val).hom ≫ f.val := by
    change (f.val ▷ (𝟙_ (PresheafOfModules X.ringCatSheaf.obj))) ≫
        (ρ_ M'.val).hom = (ρ_ M.val).hom ≫ f.val
    exact rightUnitor_naturality f.val
  have hmiddle :
      (f.val ⊗ₘ pair) ≫ (ρ_ M'.val).hom =
        ((𝟙 M.val) ⊗ₘ pair) ≫ (ρ_ M.val).hom ≫ f.val := by
    rw [hfactor, Category.assoc, hunit]
  have hraw :
      PresheafOfModules.Monoidal.tensorHom
          (PresheafOfModules.Monoidal.tensorHom f.val (𝟙 N.val)) (𝟙 P.val) ≫
        (α_ M'.val N.val P.val).hom ≫
        PresheafOfModules.Monoidal.tensorHom (𝟙 M'.val) pair ≫
        (ρ_ M'.val).hom =
      (α_ M.val N.val P.val).hom ≫
        PresheafOfModules.Monoidal.tensorHom (𝟙 M.val) pair ≫
        (ρ_ M.val).hom ≫ f.val := by
    change (((f.val ⊗ₘ (𝟙 N.val)) ⊗ₘ (𝟙 P.val)) ≫
        (α_ M'.val N.val P.val).hom ≫
        ((𝟙 M'.val) ⊗ₘ pair) ≫ (ρ_ M'.val).hom) =
      ((α_ M.val N.val P.val).hom ≫ ((𝟙 M.val) ⊗ₘ pair) ≫
        (ρ_ M.val).hom ≫ f.val)
    rw [associator_naturality_assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    have hids : (𝟙 N.val) ⊗ₘ (𝟙 P.val) =
        𝟙 (N.val ⊗ P.val) := by simp
    rw [hids]
    simp only [Category.comp_id, Category.id_comp]
    rw [hmiddle]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  simp only [schemeModuleTensorRawAssociator, h, pair]
  have hfr :
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f.val =
        f.val := by
    rfl
  have hcounit : adj.counit.app M ≫ f =
      F.map f.val ≫ adj.counit.app M' := by
    have hn := (adj.counit.naturality f).symm
    change adj.counit.app M ≫ f =
      F.map ((PresheafOfModules.restrictScalars
        (𝟙 X.ringCatSheaf.obj)).map f.val) ≫ adj.counit.app M' at hn
    rw [hfr] at hn
    exact hn
  rw [hcounit]
  rw [F.mapIso_hom, F.mapIso_hom]
  dsimp only [F]
  have hmap := congrArg F.map hraw
  have hmapc := congrArg (fun q => q ≫ adj.counit.app M') hmap
  simpa only [F.map_comp, Category.assoc, pair] using hmapc

/- Once the raw pairing stays invertible after tensoring and sheafification,
the canonical contraction is invertible.  This isolates the final local
tensor-compatibility input from the formal associativity and adjunction
bookkeeping. -/
set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleTensorContraction_isIso_of_pairingTensorMap_isIso
    (M N P : X.Modules)
    (e : schemeModuleTensor N P ≅ SheafOfModules.unit X.ringCatSheaf)
    [IsIso (schemeModuleTensorSheafificationRightComparison
      (PresheafOfModules.Monoidal.tensorObj M.val N.val) P)]
    [IsIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
          (schemeModuleTensorPairingRaw N P e)))] :
    IsIso (schemeModuleTensorContraction M N P e) := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  let a := inv (schemeModuleTensorSheafificationRightComparison
    (PresheafOfModules.Monoidal.tensorObj M.val N.val) P)
  let b := (schemeModuleTensorRawAssociator M N P).hom
  let c := (PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
        (schemeModuleTensorPairingRaw N P e))
  let d := (PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).map (ρ_ M.val).hom
  let z := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit.app M
  haveI ha : IsIso a := by dsimp only [a]; infer_instance
  haveI hb : IsIso b := by dsimp only [b]; infer_instance
  haveI hc : IsIso c := by dsimp only [c]; infer_instance
  haveI hd : IsIso d := by dsimp only [d]; infer_instance
  haveI hz : IsIso z := by dsimp only [z]; infer_instance
  haveI hdz : IsIso (d ≫ z) := IsIso.comp_isIso
  haveI hcdz : IsIso (c ≫ d ≫ z) := IsIso.comp_isIso
  haveI hbcdz : IsIso (b ≫ c ≫ d ≫ z) := IsIso.comp_isIso
  haveI habcdz : IsIso (a ≫ b ≫ c ≫ d ≫ z) := IsIso.comp_isIso
  change IsIso (a ≫ b ≫ c ≫ d ≫ z)
  exact habcdz

/-- The contractions against a fixed inverse pairing assemble into a natural
transformation.  The explicit comparison hypothesis isolates the one local
flatness input needed by the concrete sheaf tensor construction. -/
noncomputable def schemeModuleTensorContractionNatTrans
    (N P : X.Modules)
    (e : schemeModuleTensor N P ≅ SheafOfModules.unit X.ringCatSheaf)
    (hcomparison : ∀ M : X.Modules,
      IsIso (schemeModuleTensorSheafificationRightComparison
        (PresheafOfModules.Monoidal.tensorObj M.val N.val) P)) :
    schemeModuleTensorRight N ⋙ schemeModuleTensorRight P ⟶ 𝟭 X.Modules where
  app M := by
    letI := hcomparison M
    exact schemeModuleTensorContraction M N P e
  naturality {M M'} f := by
    letI := hcomparison M
    letI := hcomparison M'
    exact schemeModuleTensorContraction_naturality f e

/-- The contraction natural transformation is a natural isomorphism once
its raw tensor-pairing maps and the sheafification comparisons are known to
be invertible objectwise. -/
noncomputable def schemeModuleTensorContractionNatIso
    (N P : X.Modules)
    (e : schemeModuleTensor N P ≅ SheafOfModules.unit X.ringCatSheaf)
    (hcomparison : ∀ M : X.Modules,
      IsIso (schemeModuleTensorSheafificationRightComparison
        (PresheafOfModules.Monoidal.tensorObj M.val N.val) P))
    (hpairTensor : ∀ M : X.Modules,
      IsIso ((PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
            (schemeModuleTensorPairingRaw N P e)))) :
    schemeModuleTensorRight N ⋙ schemeModuleTensorRight P ≅ 𝟭 X.Modules :=
  NatIso.ofComponents (fun M => by
    letI := hcomparison M
    letI := hpairTensor M
    let hc : IsIso (schemeModuleTensorContraction M N P e) :=
      schemeModuleTensorContraction_isIso_of_pairingTensorMap_isIso M N P e
    exact @asIso _ _ _ _ (schemeModuleTensorContraction M N P e) hc) (by
      intro M M' f
      letI := hcomparison M
      letI := hcomparison M'
      exact schemeModuleTensorContraction_naturality f e)

/-- Two inverse tensor pairings, together with the objectwise compatibility
of raw tensoring and sheafification, give the actual right-tensor
equivalence. -/
noncomputable def schemeModuleTensorRightEquivalenceOfInversePairings
    (T Tinv : X.Modules)
    (eForward :
      schemeModuleTensor T Tinv ≅ SheafOfModules.unit X.ringCatSheaf)
    (eBackward :
      schemeModuleTensor Tinv T ≅ SheafOfModules.unit X.ringCatSheaf)
    (hcomparisonForward : ∀ M : X.Modules,
      IsIso (schemeModuleTensorSheafificationRightComparison
        (PresheafOfModules.Monoidal.tensorObj M.val T.val) Tinv))
    (hpairTensorForward : ∀ M : X.Modules,
      IsIso ((PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
            (schemeModuleTensorPairingRaw T Tinv eForward))))
    (hcomparisonBackward : ∀ M : X.Modules,
      IsIso (schemeModuleTensorSheafificationRightComparison
        (PresheafOfModules.Monoidal.tensorObj M.val Tinv.val) T))
    (hpairTensorBackward : ∀ M : X.Modules,
      IsIso ((PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
            (schemeModuleTensorPairingRaw Tinv T eBackward)))) :
    X.Modules ≌ X.Modules :=
  schemeModuleTensorRightEquivalenceOfInverse T Tinv
    (schemeModuleTensorContractionNatIso Tinv T eBackward
      hcomparisonBackward hpairTensorBackward).symm
    (schemeModuleTensorContractionNatIso T Tinv eForward
      hcomparisonForward hpairTensorForward)

end PfaffianDescent
