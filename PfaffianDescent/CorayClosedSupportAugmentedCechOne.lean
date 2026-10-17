import PfaffianDescent.CorayClosedSupportIntersectionSections

/-! SOURCE ONLY / UNVERIFIED. Actual ordered Čech sections in degrees 0, 1,
and 2, with the usual alternating restriction maps over the original field.
Adding the support-containing open as a distinguished vertex gives an explicit
linear primitive for every 1-cocycle. This is a Čech statement, not Ext-H¹.
-/

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) {ι : Type u}

abbrev SchemeModuleCechZeroCoefficients (V : ι → X.Opens) :=
  ∀ i, SchemeModuleOpenSectionsOver pi M (V i)

abbrev SchemeModuleCechOneCoefficients (V : ι → X.Opens) :=
  ∀ i j, SchemeModuleOpenSectionsOver pi M (V i ⊓ V j)

abbrev SchemeModuleCechTwoCoefficients (V : ι → X.Opens) :=
  ∀ i j k, SchemeModuleOpenSectionsOver pi M (V i ⊓ (V j ⊓ V k))

def schemeModuleCechZeroDifferential (V : ι → X.Opens) :
    SchemeModuleCechZeroCoefficients pi M V →ₗ[K]
      SchemeModuleCechOneCoefficients pi M V where
  toFun s i j :=
    schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right (s j) -
      schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_left (s i)
  map_add' s t := by
    funext i j
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' c s := by
    funext i j
    simp only [Pi.smul_apply, map_smul, smul_sub]
    rfl

def schemeModuleCechOneDifferential (V : ι → X.Opens) :
    SchemeModuleCechOneCoefficients pi M V →ₗ[K]
      SchemeModuleCechTwoCoefficients pi M V where
  toFun z i j k :=
    schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right (z j k) -
      schemeModuleOpenSectionsRestrictionLinearMap pi M
        (inf_le_inf_left (V i) inf_le_right) (z i k) +
      schemeModuleOpenSectionsRestrictionLinearMap pi M
        (inf_le_inf_left (V i) inf_le_left) (z i j)
  map_add' s t := by
    funext i j k
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' c s := by
    funext i j k
    simp only [Pi.smul_apply, map_smul, smul_sub, smul_add]
    rfl

theorem schemeModuleCechOneDifferential_comp_zeroDifferential (V : ι → X.Opens) :
    (schemeModuleCechOneDifferential pi M V).comp
      (schemeModuleCechZeroDifferential pi M V) = 0 := by
  apply LinearMap.ext
  intro s
  funext i j k
  change
    schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right
        (schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right (s k) -
          schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_left (s j)) -
      schemeModuleOpenSectionsRestrictionLinearMap pi M
        (inf_le_inf_left (V i) inf_le_right)
        (schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right (s k) -
          schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_left (s i)) +
      schemeModuleOpenSectionsRestrictionLinearMap pi M
        (inf_le_inf_left (V i) inf_le_left)
        (schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right (s j) -
          schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_left (s i)) = 0
  simp only [map_sub, schemeModule_groundRestriction_comp]
  abel

def supportAugmentedOpenFamily (U : X.Opens) (V : ι → X.Opens) :
    Option ι → X.Opens
  | none => U
  | some i => V i

theorem supportAugmentedOpenFamily_covers (U : X.Opens) (V : ι → X.Opens)
    (hV : ⊤ ≤ ⨆ i, V i) :
    ⊤ ≤ ⨆ a, supportAugmentedOpenFamily U V a := by
  apply hV.trans
  apply iSup_le
  intro i
  exact le_iSup (supportAugmentedOpenFamily U V) (some i)

def schemeModule_augmentedCechOneContraction
    (U : X.Opens) (V : ι → X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U) :
    SchemeModuleCechOneCoefficients pi M (supportAugmentedOpenFamily U V) →ₗ[K]
      SchemeModuleCechZeroCoefficients pi M (supportAugmentedOpenFamily U V) where
  toFun z i :=
    (schemeModule_groundIntersectionSectionsEquiv_of_closedSupport_subset pi M U
      (supportAugmentedOpenFamily U V i) C hC hsupport hCU).symm (z none i)
  map_add' s t := by
    funext i
    exact (schemeModule_groundIntersectionSectionsEquiv_of_closedSupport_subset pi M U
      (supportAugmentedOpenFamily U V i) C hC hsupport hCU).symm.map_add _ _
  map_smul' c s := by
    funext i
    exact (schemeModule_groundIntersectionSectionsEquiv_of_closedSupport_subset pi M U
      (supportAugmentedOpenFamily U V i) C hC hsupport hCU).symm.map_smul _ _

def schemeModule_augmentedCechTwoContraction
    (U : X.Opens) (V : ι → X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U) :
    SchemeModuleCechTwoCoefficients pi M (supportAugmentedOpenFamily U V) →ₗ[K]
      SchemeModuleCechOneCoefficients pi M (supportAugmentedOpenFamily U V) where
  toFun w i j :=
    (schemeModule_groundIntersectionSectionsEquiv_of_closedSupport_subset pi M U
      (supportAugmentedOpenFamily U V i ⊓ supportAugmentedOpenFamily U V j)
      C hC hsupport hCU).symm (w none i j)
  map_add' s t := by
    funext i j
    exact (schemeModule_groundIntersectionSectionsEquiv_of_closedSupport_subset pi M U
      (supportAugmentedOpenFamily U V i ⊓ supportAugmentedOpenFamily U V j)
      C hC hsupport hCU).symm.map_add _ _
  map_smul' c s := by
    funext i j
    exact (schemeModule_groundIntersectionSectionsEquiv_of_closedSupport_subset pi M U
      (supportAugmentedOpenFamily U V i ⊓ supportAugmentedOpenFamily U V j)
      C hC hsupport hCU).symm.map_smul _ _

theorem schemeModule_augmentedCechOne_homotopy_identity
    (U : X.Opens) (V : ι → X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U)
    (z : SchemeModuleCechOneCoefficients pi M (supportAugmentedOpenFamily U V)) :
    schemeModuleCechZeroDifferential pi M (supportAugmentedOpenFamily U V)
        (schemeModule_augmentedCechOneContraction pi M U V C hC hsupport hCU z) +
      schemeModule_augmentedCechTwoContraction pi M U V C hC hsupport hCU
        (schemeModuleCechOneDifferential pi M (supportAugmentedOpenFamily U V) z) = z := by
  funext i j
  let A := supportAugmentedOpenFamily U V
  let e := schemeModule_groundIntersectionSectionsEquiv_of_closedSupport_subset
    pi M U (A i ⊓ A j) C hC hsupport hCU
  apply e.injective
  change
    schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right
      ((schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right
          ((schemeModule_groundIntersectionSectionsEquiv_of_closedSupport_subset
            pi M U (A j) C hC hsupport hCU).symm (z none j)) -
        schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_left
          ((schemeModule_groundIntersectionSectionsEquiv_of_closedSupport_subset
            pi M U (A i) C hC hsupport hCU).symm (z none i))) +
        e.symm (schemeModuleCechOneDifferential pi M A z none i j)) =
      schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right (z i j)
  rw [map_add, map_sub,
    schemeModule_groundIntersectionExtension_naturality pi M U C hC hsupport hCU
      (show A i ⊓ A j ≤ A j from inf_le_right) (z none j),
    schemeModule_groundIntersectionExtension_naturality pi M U C hC hsupport hCU
      (show A i ⊓ A j ≤ A i from inf_le_left) (z none i)]
  have he : schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right
      (e.symm (schemeModuleCechOneDifferential pi M A z none i j)) =
        schemeModuleCechOneDifferential pi M A z none i j :=
    e.apply_symm_apply _
  erw [he]
  let a := schemeModuleOpenSectionsRestrictionLinearMap pi M
    (inf_le_inf_left U (show A i ⊓ A j ≤ A i from inf_le_left)) (z none i)
  let b := schemeModuleOpenSectionsRestrictionLinearMap pi M
    (inf_le_inf_left U (show A i ⊓ A j ≤ A j from inf_le_right)) (z none j)
  let c := schemeModuleOpenSectionsRestrictionLinearMap pi M
    (show U ⊓ (A i ⊓ A j) ≤ A i ⊓ A j from inf_le_right) (z i j)
  change (b - a) + (c - b + a) = c
  abel

theorem schemeModule_augmentedCechOne_cocycle_is_boundary
    (U : X.Opens) (V : ι → X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U)
    (z : SchemeModuleCechOneCoefficients pi M (supportAugmentedOpenFamily U V))
    (hz : schemeModuleCechOneDifferential pi M (supportAugmentedOpenFamily U V) z = 0) :
    schemeModuleCechZeroDifferential pi M (supportAugmentedOpenFamily U V)
      (schemeModule_augmentedCechOneContraction pi M U V C hC hsupport hCU z) = z := by
  have h := schemeModule_augmentedCechOne_homotopy_identity pi M U V C hC hsupport hCU z
  rw [hz, map_zero, add_zero] at h
  exact h

theorem schemeModule_augmentedCech_exact_one_of_closedSupport_subset
    (U : X.Opens) (V : ι → X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U) :
    Function.Exact
      (schemeModuleCechZeroDifferential pi M (supportAugmentedOpenFamily U V))
      (schemeModuleCechOneDifferential pi M (supportAugmentedOpenFamily U V)) := by
  intro z
  constructor
  · intro hz
    exact ⟨schemeModule_augmentedCechOneContraction pi M U V C hC hsupport hCU z,
      schemeModule_augmentedCechOne_cocycle_is_boundary pi M U V C hC hsupport hCU z hz⟩
  · rintro ⟨s, rfl⟩
    exact LinearMap.congr_fun
      (schemeModuleCechOneDifferential_comp_zeroDifferential pi M
        (supportAugmentedOpenFamily U V)) s

end PfaffianDescent.Coray
