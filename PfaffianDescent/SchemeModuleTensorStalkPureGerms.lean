import PfaffianDescent.SchemeModuleCanonicalTensorFieldMultiplication
import PfaffianDescent.VoisinSheafStalk

/-! The canonical pure-germ pairing of the ACTUAL tensor sheaf stalk.
Germ equivalence and original pure-section restriction prove independence;
actual unit charts make this pairing surjective in rank one. No stalk
tensor comparison, generation or image certificate is assumed.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem additiveRestriction_comp
    {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{u})
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D)
    (he : f ≫ g = h) (s : F.obj A) :
    F.map g (F.map f s) = F.map h s :=
  (ConcreteCategory.congr_hom (F.map_comp f g) s).symm.trans
    (congrArg (fun k : A ⟶ D => F.map k s) he)

private theorem tensorPureGerm_congr
    (M N : X.Modules) (x : X) {U V : X.Opens}
    (hxU : x ∈ U) (hxV : x ∈ V)
    (mU : M.val.obj (op U)) (nU : N.val.obj (op U))
    (mV : M.val.obj (op V)) (nV : N.val.obj (op V))
    (hm : M.presheaf.germ U x hxU mU = M.presheaf.germ V x hxV mV)
    (hn : N.presheaf.germ U x hxU nU = N.presheaf.germ V x hxV nV) :
    (schemeModuleTensor M N).presheaf.germ U x hxU
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) mU nU) =
      (schemeModuleTensor M N).presheaf.germ V x hxV
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op V) mV nV) := by
  obtain ⟨A, hxA, iAU, iAV, hA⟩ := M.presheaf.germ_eq x hxU hxV mU mV hm
  obtain ⟨B, hxB, iBU, iBV, hB⟩ := N.presheaf.germ_eq x hxU hxV nU nV hn
  let W := A ⊓ B
  have hxW : x ∈ W := ⟨hxA, hxB⟩
  let kA : W ⟶ A := homOfLE inf_le_left
  let kB : W ⟶ B := homOfLE inf_le_right
  let kU : W ⟶ U := kA ≫ iAU
  let kV : W ⟶ V := kA ≫ iAV
  have hmW : M.val.map kU.op mU = M.val.map kV.op mV :=
    (additiveRestriction_comp M.val.presheaf iAU.op kA.op kU.op
      (Subsingleton.elim _ _) mU).symm.trans
        ((congrArg (M.val.map kA.op) hA).trans
          (additiveRestriction_comp M.val.presheaf iAV.op kA.op kV.op
            (Subsingleton.elim _ _) mV))
  have hnW : N.val.map kU.op nU = N.val.map kV.op nV :=
    (additiveRestriction_comp N.val.presheaf iBU.op kB.op kU.op
      (Subsingleton.elim _ _) nU).symm.trans
        ((congrArg (N.val.map kB.op) hB).trans
          (additiveRestriction_comp N.val.presheaf iBV.op kB.op kV.op
            (Subsingleton.elim _ _) nV))
  let T := schemeModuleTensor M N
  have hU : T.presheaf.germ U x hxU
      (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) mU nU) =
      T.presheaf.germ W x hxW
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op W)
          (M.val.map kU.op mU) (N.val.map kU.op nU)) :=
    (T.presheaf.germ_res_apply kU x hxW _).symm.trans
      (congrArg (T.presheaf.germ W x hxW)
        (SheafOfModules.commRingSheafTensorPureSection_restrict X.sheaf M N kU.op mU nU))
  have hV : T.presheaf.germ V x hxV
      (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op V) mV nV) =
      T.presheaf.germ W x hxW
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op W)
          (M.val.map kV.op mV) (N.val.map kV.op nV)) :=
    (T.presheaf.germ_res_apply kV x hxW _).symm.trans
      (congrArg (T.presheaf.germ W x hxW)
        (SheafOfModules.commRingSheafTensorPureSection_restrict X.sheaf M N kV.op mV nV))
  exact hU.trans
    ((congrArg (T.presheaf.germ W x hxW)
      (congrArg₂ (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op W))
        hmW hnW)).trans hV.symm)

private theorem tensorPureGerm_value_exists
    (M N : X.Modules) (x : X)
    (a : M.presheaf.stalk x) (b : N.presheaf.stalk x) :
    ∃ t : (schemeModuleTensor M N).presheaf.stalk x,
      ∀ (U : X.Opens) (hxU : x ∈ U) (m : M.val.obj (op U)) (n : N.val.obj (op U)),
        M.presheaf.germ U x hxU m = a → N.presheaf.germ U x hxU n = b →
        (schemeModuleTensor M N).presheaf.germ U x hxU
          (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) m n) = t := by
  obtain ⟨A, hxA, mA, hA⟩ := M.presheaf.exists_germ_eq a
  obtain ⟨V, hVA, hxV, nV, hV⟩ := N.presheaf.exists_le_germ_eq b hxA
  let mV : M.val.obj (op V) := M.val.map (homOfLE hVA).op mA
  have hmV : M.presheaf.germ V x hxV mV = a :=
    (M.presheaf.germ_res_apply (homOfLE hVA) x hxV mA).trans hA
  refine ⟨(schemeModuleTensor M N).presheaf.germ V x hxV
    (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op V) mV nV), ?_⟩
  intro U hxU m n hm hn
  exact tensorPureGerm_congr M N x hxU hxV m n mV nV
    (hm.trans hmV.symm) (hn.trans hV.symm)

/-- Canonical pairing into the LITERAL actual tensor-sheaf stalk. The
internally chosen representative has a proved value independent of EVERY
choice; this is the original sheafification-unit pure tensor followed by
the actual germ, not a transported or assumed tensor-stalk comparison. -/
def schemeModuleTensorStalkPureGerm
    (M N : X.Modules) (x : X) :
    M.presheaf.stalk x → N.presheaf.stalk x → (schemeModuleTensor M N).presheaf.stalk x :=
  fun a b => Classical.choose (tensorPureGerm_value_exists M N x a b)

/-- Every local representative evaluates to the SAME canonical pairing;
the smaller-open equivalence is proved from actual germ equality. -/
theorem schemeModuleTensorStalkPureGerm_germ
    (M N : X.Modules) (x : X) (U : X.Opens) (hxU : x ∈ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    schemeModuleTensorStalkPureGerm M N x
        (M.presheaf.germ U x hxU m) (N.presheaf.germ U x hxU n) =
      (schemeModuleTensor M N).presheaf.germ U x hxU
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) m n) :=
  (Classical.choose_spec (tensorPureGerm_value_exists M N x
    (M.presheaf.germ U x hxU m) (N.presheaf.germ U x hxU n)) U hxU m n rfl rfl).symm

/-- EVERY actual tensor stalk value is an original pure tensor germ in
rank one. Actual pointwise unit charts and the proved canonical tensor
coefficient identity supply generation; it is never a hypothesis. -/
theorem schemeModuleTensorStalkPureGerm_surjective_of_locallyRankOne
    (M N : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (hN : schemeModuleLocallyRankOne N) (x : X) :
    Function.Surjective (fun p : M.presheaf.stalk x × N.presheaf.stalk x =>
      schemeModuleTensorStalkPureGerm M N x p.1 p.2) := by
  intro t
  obtain ⟨A, hxA, ⟨eA⟩⟩ := hM x
  obtain ⟨B, hxB, ⟨eB⟩⟩ := hN x
  let U := A ⊓ B
  have hxU : x ∈ U := ⟨hxA, hxB⟩
  let T := schemeModuleTensor M N
  obtain ⟨V, hVU, hxV, s, hs⟩ := T.presheaf.exists_le_germ_eq t hxU
  let eM := SchemeModuleInternalHom.overUnitChartRestrict M
    (homOfLE (hVU.trans inf_le_left)) eA
  let eN := SchemeModuleInternalHom.overUnitChartRestrict N
    (homOfLE (hVU.trans inf_le_right)) eB
  let qM := SchemeModuleInternalHom.overTopLinearEquiv M V eM
  let qN := SchemeModuleInternalHom.overTopLinearEquiv N V eN
  let qT := SchemeModuleInternalHom.overTopLinearEquiv T V
    (schemeModuleTensorOverUnitIso M N V eM eN)
  let m : M.val.obj (op V) := qM.symm (qT s)
  let n : N.val.obj (op V) := qN.symm (1 : Γ(X, V))
  have hpure : SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op V) m n = s := by
    apply qT.injective
    exact (schemeModuleTensorOverUnitIso_pureSection M N V eM eN m n).trans
      ((congrArg₂ (fun r c : Γ(X, V) => r * c)
        (qM.apply_symm_apply (qT s)) (qN.apply_symm_apply (1 : Γ(X, V)))).trans
          (mul_one (qT s)))
  refine ⟨⟨M.presheaf.germ V x hxV m, N.presheaf.germ V x hxV n⟩, ?_⟩
  exact (schemeModuleTensorStalkPureGerm_germ M N x V hxV m n).trans
    ((congrArg (T.presheaf.germ V x hxV) hpure).trans hs)

variable {K : Type u} [Field K] [IsIntegral X]

/-- Local (rather than only top-open) original-pi chart maps multiply
on the actual sheafification-unit pure section. The charts are actual
generic unit charts; no multiplicativity comparison is an input. -/
theorem schemeModuleChartSectionsToFunctionFieldLinearMap_tensorPureSection
    (pi : X ⟶ Spec (CommRingCat.of K)) (M N : X.Modules)
    (U : X.Opens) [Nonempty U]
    (eM : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (eN : N.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (m : SchemeModuleOpenSectionsOver pi M U) (n : SchemeModuleOpenSectionsOver pi N U) :
    (schemeModuleChartSectionsToFunctionFieldLinearMap pi (schemeModuleTensor M N) U
        (schemeModuleTensorOverUnitIso M N U eM eN)
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) m n) :
          X.functionField) =
      @HMul.hMul X.functionField X.functionField X.functionField inferInstance
        (schemeModuleChartSectionsToFunctionFieldLinearMap pi M U eM m)
        (schemeModuleChartSectionsToFunctionFieldLinearMap pi N U eN n) := by
  change X.germToFunctionField U
      (SchemeModuleInternalHom.overTopLinearEquiv (schemeModuleTensor M N) U
        (schemeModuleTensorOverUnitIso M N U eM eN)
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) m n)) =
    X.germToFunctionField U (SchemeModuleInternalHom.overTopLinearEquiv M U eM m) *
      X.germToFunctionField U (SchemeModuleInternalHom.overTopLinearEquiv N U eN n)
  exact (congrArg (X.germToFunctionField U)
    (schemeModuleTensorOverUnitIso_pureSection M N U eM eN m n)).trans
      ((X.germToFunctionField U).hom.map_mul _ _)

end PfaffianDescent
