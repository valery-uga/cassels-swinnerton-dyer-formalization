import PfaffianDescent.SchemeModuleCanonicalTensorFieldMultiplication
import PfaffianDescent.SchemeModuleTensor
import PfaffianDescent.SchemeModuleSectionOnOpen

/-! Bounded original over-site section frames. SOURCE ONLY / UNVERIFIED.
Resumed successor: actual native tensor section frames and their ORIGINAL
morphism compatibility. Frame invertibility and the own/global Cartier
tensor-power Iso are separate remaining tasks. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- The compatible over-site section induced by the SAME original
section on U, using only its literal original restriction maps. -/
def nativeOriginalOverSection (M : X.Modules) (U : X.Opens)
    (m : M.val.obj (op U)) : (M.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun V => M.val.map V.unop.hom.op m)
    (by
      intro V W f
      change M.val.map f.unop.left.op (M.val.map V.unop.hom.op m) =
        M.val.map W.unop.hom.op m
      have hc : V.unop.hom.op ≫ f.unop.left.op = W.unop.hom.op := by
        rw [← op_comp, Over.w]
      have he : M.val.map (V.unop.hom.op ≫ f.unop.left.op) m =
          M.val.map W.unop.hom.op m :=
        congrArg (fun k : op U ⟶ op W.unop.left =>
          (show M.val.obj (op W.unop.left) from (M.val.map k).hom m)) hc
      exact (PresheafOfModules.map_comp_apply M.val
        V.unop.hom.op f.unop.left.op m).symm.trans he)

/-- The original unit-module/section adjunction gives the actual
over-site section frame, with no frame Iso premise or replaced map. -/
def nativeOriginalOverSectionHom (M : X.Modules) (U : X.Opens)
    (m : M.val.obj (op U)) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M.over U :=
  (M.over U).unitHomEquiv.symm (nativeOriginalOverSection M U m)

/-- At EVERY original over-site object, the frame sends one to the
literal original restriction of m. This is the native adjunction inverse
law, with no coordinate/value equality assumption. -/
theorem nativeOriginalOverSectionHom_one (M : X.Modules) (U : X.Opens)
    (m : M.val.obj (op U)) (V : (Over U)ᵒᵖ) :
    (nativeOriginalOverSectionHom M U m).val.app V
      (1 : (X.ringCatSheaf.over U).obj.obj V) = M.val.map V.unop.hom.op m := by
  have h := congrArg (fun s : (M.over U).sections => s.val V)
    ((M.over U).unitHomEquiv.apply_symm_apply (nativeOriginalOverSection M U m))
  exact h

/-- The ORIGINAL over-site tensor Iso inverse sends the actual local
pure section to the actual global pure section. This is its inverse law
and the existing exact forward pure-section normalization. -/
theorem nativeOriginalTensorOverIso_inv_pureSection
    (U : X.Opens) (M N : X.Modules) (V : (Over U)ᵒᵖ)
    (m : M.val.obj (op V.unop.left)) (n : N.val.obj (op V.unop.left)) :
    (schemeModuleTensorOverIso U M N).inv.val.app V
      (SheafOfModules.commRingSheafTensorPureSection
        (SheafOfModules.commRingSheafOver X.sheaf U) (M.over U) (N.over U) V m n) =
      SheafOfModules.commRingSheafTensorPureSection X.sheaf M N
        (op V.unop.left) m n := by
  let e := schemeModuleTensorOverIso U M N
  let t := SheafOfModules.commRingSheafTensorPureSection X.sheaf M N
    (op V.unop.left) m n
  have h := congrArg (fun s => e.inv.val.app V s)
    (schemeModuleTensorOverIso_pureSection U M N V m n)
  have hi := congrArg (fun k => (k.val.app V).hom t) e.hom_inv_id
  exact h.symm.trans hi

/-- The actual unit tensor inverse sends one to the actual sheafified
pure tensor of two ones; no unitor coefficient equation is input. -/
theorem nativeOriginalOverTensorUnit_inv_one
    (U : X.Opens) (V : (Over U)ᵒᵖ) :
    let O := SheafOfModules.unit (X.ringCatSheaf.over U)
    (SheafOfModules.commRingSheafTensorUnitRightIso
      (SheafOfModules.commRingSheafOver X.sheaf U) O).inv.val.app V
        (1 : (X.ringCatSheaf.over U).obj.obj V) =
      SheafOfModules.commRingSheafTensorPureSection
        (SheafOfModules.commRingSheafOver X.sheaf U) O O V
        (1 : (X.ringCatSheaf.over U).obj.obj V)
        (1 : (X.ringCatSheaf.over U).obj.obj V) := by
  dsimp only
  let R := SheafOfModules.commRingSheafOver X.sheaf U
  let O := SheafOfModules.unit (X.ringCatSheaf.over U)
  let e := SheafOfModules.commRingSheafTensorUnitRightIso R O
  let t := SheafOfModules.commRingSheafTensorPureSection R O O V
    (1 : (X.ringCatSheaf.over U).obj.obj V)
    (1 : (X.ringCatSheaf.over U).obj.obj V)
  have ht : e.hom.val.app V t = (1 : (X.ringCatSheaf.over U).obj.obj V) := by
    have hp := SheafOfModules.commRingSheafTensorUnitRightIso_pureSection R O V
      (1 : (X.ringCatSheaf.over U).obj.obj V)
      (1 : (X.ringCatSheaf.over U).obj.obj V)
    change e.hom.val.app V t =
      (1 : (X.ringCatSheaf.over U).obj.obj V) *
        (1 : (X.ringCatSheaf.over U).obj.obj V) at hp
    exact hp.trans (one_mul (1 : (X.ringCatSheaf.over U).obj.obj V))
  have hi := congrArg (fun k => (k.val.app V).hom t) e.hom_inv_id
  exact (congrArg (fun s => e.inv.val.app V s) ht).symm.trans hi

/-- The canonical tensor of the two ORIGINAL section frames, transported
back along the ORIGINAL restriction/tensor Iso. No frame Iso is input. -/
def nativeOriginalTensorSectionFrame
    (M N : X.Modules) (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      (schemeModuleTensor M N).over U :=
  (SheafOfModules.commRingSheafTensorUnitRightIso
      (SheafOfModules.commRingSheafOver X.sheaf U)
      (SheafOfModules.unit (X.ringCatSheaf.over U))).inv ≫
    SheafOfModules.commRingSheafTensorMap
      (SheafOfModules.commRingSheafOver X.sheaf U)
      (nativeOriginalOverSectionHom M U m) (nativeOriginalOverSectionHom N U n) ≫
    (schemeModuleTensorOverIso U M N).inv

/-- On EVERY over-site object the original tensor frame sends one to
the original pure section of the two original restricted generators. -/
theorem nativeOriginalTensorSectionFrame_one
    (M N : X.Modules) (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) (V : (Over U)ᵒᵖ) :
    (nativeOriginalTensorSectionFrame M N U m n).val.app V
      (1 : (X.ringCatSheaf.over U).obj.obj V) =
      SheafOfModules.commRingSheafTensorPureSection X.sheaf M N
        (op V.unop.left) (M.val.map V.unop.hom.op m) (N.val.map V.unop.hom.op n) := by
  let R := SheafOfModules.commRingSheafOver X.sheaf U
  let O := SheafOfModules.unit (X.ringCatSheaf.over U)
  let fm := nativeOriginalOverSectionHom M U m
  let fn := nativeOriginalOverSectionHom N U n
  change (schemeModuleTensorOverIso U M N).inv.val.app V
    ((SheafOfModules.commRingSheafTensorMap R fm fn).val.app V
      ((SheafOfModules.commRingSheafTensorUnitRightIso R O).inv.val.app V
        (1 : (X.ringCatSheaf.over U).obj.obj V))) = _
  have hu := nativeOriginalOverTensorUnit_inv_one U V
  have hm := nativeOriginalOverSectionHom_one M U m V
  have hn := nativeOriginalOverSectionHom_one N U n V
  have hmap := SheafOfModules.commRingSheafTensorPureSection_map R fm fn V
    (1 : (X.ringCatSheaf.over U).obj.obj V)
    (1 : (X.ringCatSheaf.over U).obj.obj V)
  have hvals := congrArg₂
    (fun a b => SheafOfModules.commRingSheafTensorPureSection R (M.over U) (N.over U) V a b)
    hm hn
  have hlocal := (congrArg
    (fun s => (SheafOfModules.commRingSheafTensorMap R fm fn).val.app V s) hu).trans
      (hmap.trans hvals)
  exact (congrArg (fun s => (schemeModuleTensorOverIso U M N).inv.val.app V s) hlocal).trans
    (nativeOriginalTensorOverIso_inv_pureSection U M N V
      (M.val.map V.unop.hom.op m) (N.val.map V.unop.hom.op n))

/-- The canonical tensor frame is exactly the ORIGINAL section frame
of the original sheafification-unit pure tensor, not just an abstract
rank-one source equivalence. -/
theorem nativeOriginalTensorSectionFrame_eq_sectionHom
    (M N : X.Modules) (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    nativeOriginalTensorSectionFrame M N U m n =
      nativeOriginalOverSectionHom (schemeModuleTensor M N) U
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) m n) := by
  apply ((schemeModuleTensor M N).over U).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  exact (nativeOriginalTensorSectionFrame_one M N U m n V).trans
    ((SheafOfModules.commRingSheafTensorPureSection_restrict X.sheaf M N
      V.unop.hom.op m n).symm.trans
        (nativeOriginalOverSectionHom_one (schemeModuleTensor M N) U
          (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) m n) V).symm)

/-- Postcomposition with ANY ORIGINAL module map commutes with the
original over-site section-frame construction, by original naturality. -/
theorem nativeOriginalOverSectionHom_comp
    {M P : X.Modules} (U : X.Opens) (m : M.val.obj (op U)) (k : M ⟶ P) :
    nativeOriginalOverSectionHom M U m ≫
        (SheafOfModules.overFunctor X.ringCatSheaf U).map k =
      nativeOriginalOverSectionHom P U (k.val.app (op U) m) := by
  apply (P.over U).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  change k.val.app (op V.unop.left)
    ((nativeOriginalOverSectionHom M U m).val.app V
      (1 : (X.ringCatSheaf.over U).obj.obj V)) =
    (nativeOriginalOverSectionHom P U (k.val.app (op U) m)).val.app V
      (1 : (X.ringCatSheaf.over U).obj.obj V)
  exact (congrArg (fun s => k.val.app (op V.unop.left) s)
    (nativeOriginalOverSectionHom_one M U m V)).trans
      ((PresheafOfModules.naturality_apply k.val V.unop.hom.op m).trans
        (nativeOriginalOverSectionHom_one P U (k.val.app (op U) m) V).symm)

/-- EXACT original-map frame compatibility for ANY tensor morphism.
In particular actual ideal multiplication has this square internally;
neither the square nor invertibility of the tensor morphism is an input. -/
theorem nativeOriginalTensorSectionFrame_comp
    {M N P : X.Modules} (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U))
    (k : schemeModuleTensor M N ⟶ P) :
    nativeOriginalTensorSectionFrame M N U m n ≫
        (SheafOfModules.overFunctor X.ringCatSheaf U).map k =
      nativeOriginalOverSectionHom P U
        (k.val.app (op U)
          (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) m n)) := by
  exact (congrArg
    (fun f => f ≫ (SheafOfModules.overFunctor X.ringCatSheaf U).map k)
      (nativeOriginalTensorSectionFrame_eq_sectionHom M N U m n)).trans
        (nativeOriginalOverSectionHom_comp U
          (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) m n) k)

end PfaffianDescent.Coray
