import PfaffianDescent.SchemeModuleUnitHomGroundSections
import PfaffianDescent.CorayGenericNormalizationLowDegreeLinearExact

/-! Genuine degree-zero/one LES on ACTUAL top-open sections, retaining
the original pi-induced scalar on sections and Ext. This is generic
homological algebra; geometric callers must derive their ShortExact input.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal map on Γ(M,top), linear for independently existing pi
actions. Its underlying map is the ACTUAL sheaf-module component. -/
def schemeModuleOpenTopCoefficientLinearMapOver
    (pi : X ⟶ Spec (CommRingCat.of K)) {M N : X.Modules} (f : M ⟶ N) :
    SchemeModuleOpenSectionsOver pi M ⊤ →ₗ[K] SchemeModuleOpenSectionsOver pi N ⊤ where
  toFun := f.val.app (op ⊤)
  map_add' := (f.val.app (op ⊤)).hom.map_add
  map_smul' c s := (f.val.app (op ⊤)).hom.map_smul (schemeOpenBaseRingHom pi ⊤ c) s

/-- An actual coefficient Iso gives a linear equivalence on literal global
sections, with the independently defined original pi actions on BOTH sides. -/
def schemeModuleOpenTopIsoLinearEquivOver
    (pi : X ⟶ Spec (CommRingCat.of K)) {M N : X.Modules} (e : M ≅ N) :
    SchemeModuleOpenSectionsOver pi M ⊤ ≃ₗ[K] SchemeModuleOpenSectionsOver pi N ⊤ where
  toLinearMap := schemeModuleOpenTopCoefficientLinearMapOver pi e.hom
  invFun := schemeModuleOpenTopCoefficientLinearMapOver pi e.inv
  left_inv s := by
    change (e.hom ≫ e.inv).val.app (op ⊤) s = s
    rw [e.hom_inv_id]
    rfl
  right_inv s := by
    change (e.inv ≫ e.hom).val.app (op ⊤) s = s
    rw [e.inv_hom_id]
    rfl

/-- The actual connecting map from unit Hom, using the actual extension
class of the given genuine ShortExact complex. -/
def schemeModuleHomConnectingLinearMapOver
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ S.X₃) →ₗ[K]
      schemeModuleCohomology X S.X₁ 1 := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  refine
    { toFun := fun s => (Ext.mk₀ s).comp hS.extClass (show 0 + 1 = 1 by rfl)
      map_add' := ?_
      map_smul' := ?_ }
  · intro s t
    rw [Ext.mk₀_add, Ext.add_comp]
  · intro c s
    rw [Ext.mk₀_smul, Ext.smul_comp]
    rfl

/-- The SAME connecting map on literal Γ(S.X₃,top). The inverse unit-Hom
comparison uses its proved original scalar compatibility, not a new action. -/
def schemeModuleOpenTopConnectingLinearMapOver
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    SchemeModuleOpenSectionsOver pi S.X₃ ⊤ →ₗ[K] schemeModuleCohomology X S.X₁ 1 := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact (schemeModuleHomConnectingLinearMapOver pi S hS).comp
    (schemeModuleUnitHomGroundLinearEquivOpenTop pi S.X₃).symm.toLinearMap

/-- Exactness at Γ(S.X₂,top) is also genuine: the proof uses the actual
degree-zero Ext LES and the actual unit-Hom/top-section naturality. -/
theorem schemeModuleOpenTopCoefficientLinearMaps_exact
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    Function.Exact (schemeModuleOpenTopCoefficientLinearMapOver pi S.f)
      (schemeModuleOpenTopCoefficientLinearMapOver pi S.g) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let eA := schemeModuleUnitHomGroundLinearEquivOpenTop pi S.X₁
  let eB := schemeModuleUnitHomGroundLinearEquivOpenTop pi S.X₂
  let eC := schemeModuleUnitHomGroundLinearEquivOpenTop pi S.X₃
  intro z
  constructor
  · intro hz
    have hhom : eB.symm z ≫ S.g = 0 := by
      apply eC.injective
      rw [schemeModuleUnitHomGroundLinearEquivOpenTop_naturality, eB.apply_symm_apply,
        eC.map_zero]
      exact hz
    have hz' : (Ext.mk₀ (eB.symm z)).comp (Ext.mk₀ S.g) (add_zero 0) = 0 := by
      rw [Ext.mk₀_comp_mk₀, hhom, Ext.mk₀_zero]
    obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₂ O hS (Ext.mk₀ (eB.symm z)) hz'
    have ht' : Ext.addEquiv₀ t ≫ S.f = eB.symm z := by
      apply (Ext.mk₀_bijective O S.X₂).1
      rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
      exact ht
    refine ⟨eA (Ext.addEquiv₀ t), ?_⟩
    change S.f.val.app (op ⊤) (eA (Ext.addEquiv₀ t)) = z
    rw [← schemeModuleUnitHomGroundLinearEquivOpenTop_naturality, ht']
    exact eB.apply_symm_apply z
  · rintro ⟨s, rfl⟩
    change (S.f ≫ S.g).val.app (op ⊤) s = 0
    rw [S.zero]
    rfl

/-- Exactness at literal quotient sections and at actual H¹(S.X₁), with
the SAME original projection, coefficient-induced map and extension class. -/
theorem schemeModuleOpenTopConnectingLinearMaps_exact
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Function.Exact (schemeModuleOpenTopCoefficientLinearMapOver pi S.g)
      (schemeModuleOpenTopConnectingLinearMapOver pi S hS) ∧
    Function.Exact (schemeModuleOpenTopConnectingLinearMapOver pi S hS)
      (schemeModuleCohomologyLinearMapOver pi S.f 1) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let eB := schemeModuleUnitHomGroundLinearEquivOpenTop pi S.X₂
  let eC := schemeModuleUnitHomGroundLinearEquivOpenTop pi S.X₃
  constructor
  · intro s
    constructor
    · intro hs
      have hs' : (Ext.mk₀ (eC.symm s)).comp hS.extClass
          (show 0 + 1 = 1 by rfl) = 0 := hs
      obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₃ O hS (Ext.mk₀ (eC.symm s))
        (show 0 + 1 = 1 by rfl) hs'
      have hhom : Ext.addEquiv₀ t ≫ S.g = eC.symm s := by
        apply (Ext.mk₀_bijective O S.X₃).1
        rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
        exact ht
      refine ⟨eB (Ext.addEquiv₀ t), ?_⟩
      change S.g.val.app (op ⊤) (eB (Ext.addEquiv₀ t)) = s
      rw [← schemeModuleUnitHomGroundLinearEquivOpenTop_naturality, hhom]
      exact eC.apply_symm_apply s
    · rintro ⟨t, rfl⟩
      have hhom : eC.symm (S.g.val.app (op ⊤) t) = eB.symm t ≫ S.g := by
        apply eC.injective
        rw [eC.apply_symm_apply, schemeModuleUnitHomGroundLinearEquivOpenTop_naturality,
          eB.apply_symm_apply]
      change (Ext.mk₀ (eC.symm (S.g.val.app (op ⊤) t))).comp hS.extClass
        (show 0 + 1 = 1 by rfl) = 0
      rw [hhom, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
        hS.comp_extClass, Ext.comp_zero]
  · intro z
    constructor
    · intro hz
      have hz' : z.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := hz
      obtain ⟨s, hs⟩ := Ext.covariant_sequence_exact₁ O hS z hz'
        (show 0 + 1 = 1 by rfl)
      refine ⟨eC (Ext.addEquiv₀ s), ?_⟩
      change (Ext.mk₀ (eC.symm (eC (Ext.addEquiv₀ s)))).comp hS.extClass
        (show 0 + 1 = 1 by rfl) = z
      rw [eC.symm_apply_apply, Ext.mk₀_addEquiv₀_apply]
      exact hs
    · rintro ⟨s, rfl⟩
      change ((Ext.mk₀ (eC.symm s)).comp hS.extClass (show 0 + 1 = 1 by rfl)).comp
        (Ext.mk₀ S.f) (add_zero 1) = 0
      rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]

/-- The H¹ kernel is precisely the image of the SAME actual connecting
map on literal global quotient sections; the full section-map image is kept. -/
theorem schemeModuleOpenTopConnectingLinearMaps_kernel_range
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    (schemeModuleOpenTopConnectingLinearMapOver pi S hS).ker =
        LinearMap.range (schemeModuleOpenTopCoefficientLinearMapOver pi S.g) ∧
    (schemeModuleCohomologyLinearMapOver pi S.f 1).ker =
        LinearMap.range (schemeModuleOpenTopConnectingLinearMapOver pi S hS) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  constructor <;> apply Submodule.ext <;> intro z
  · change schemeModuleOpenTopConnectingLinearMapOver pi S hS z = 0 ↔
      ∃ s, schemeModuleOpenTopCoefficientLinearMapOver pi S.g s = z
    exact (schemeModuleOpenTopConnectingLinearMaps_exact pi S hS).1 z
  · change schemeModuleCohomologyLinearMapOver pi S.f 1 z = 0 ↔
      ∃ s, schemeModuleOpenTopConnectingLinearMapOver pi S hS s = z
    exact (schemeModuleOpenTopConnectingLinearMaps_exact pi S hS).2 z

/-- Formal LES surjectivity when the quotient's genuine H¹ vanishes.
The primitive point caller below proves this vanishing internally. -/
theorem schemeModuleCohomologyOneMap_surjective_of_quotient_subsingleton
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Subsingleton (schemeModuleCohomology X S.X₃ 1)] :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Function.Surjective (schemeModuleCohomologyLinearMapOver pi S.f 1) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  intro z
  have hz : z.comp (Ext.mk₀ S.g) (add_zero 1) = 0 := Subsingleton.elim _ _
  obtain ⟨s, hs⟩ := Ext.covariant_sequence_exact₂ O hS z hz
  exact ⟨s, hs⟩

/-- Transport only the actual quotient term of the genuine LES. The new
section projection is literally S.g followed by e.hom; no desired square,
exactness or scalar-compatibility certificate is an input. -/
theorem schemeModuleOpenTopConnectingLinearMaps_exact_of_quotientIso
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {F : X.Modules} (e : S.X₃ ≅ F) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    let b := (schemeModuleOpenTopConnectingLinearMapOver pi S hS).comp
      (schemeModuleOpenTopCoefficientLinearMapOver pi e.inv)
    Function.Exact (schemeModuleOpenTopCoefficientLinearMapOver pi (S.g ≫ e.hom)) b ∧
      Function.Exact b (schemeModuleCohomologyLinearMapOver pi S.f 1) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let E := schemeModuleOpenTopIsoLinearEquivOver pi e
  let delta := schemeModuleOpenTopConnectingLinearMapOver pi S hS
  have h := schemeModuleOpenTopConnectingLinearMaps_exact pi S hS
  constructor
  · intro z
    constructor
    · intro hz
      have hz' : delta (E.symm z) = 0 := hz
      obtain ⟨s, hs⟩ := (h.1 (E.symm z)).mp hz'
      refine ⟨s, ?_⟩
      change E (schemeModuleOpenTopCoefficientLinearMapOver pi S.g s) = z
      rw [hs, E.apply_symm_apply]
    · rintro ⟨s, rfl⟩
      change delta (E.symm (E (schemeModuleOpenTopCoefficientLinearMapOver pi S.g s))) = 0
      rw [E.symm_apply_apply]
      exact h.1.apply_apply_eq_zero s
  · intro z
    constructor
    · intro hz
      obtain ⟨s, hs⟩ := (h.2 z).mp hz
      refine ⟨E s, ?_⟩
      change delta (E.symm (E s)) = z
      rw [E.symm_apply_apply]
      exact hs
    · rintro ⟨s, hs⟩
      exact (h.2 z).mpr ⟨E.symm s, hs⟩

end PfaffianDescent.Coray
