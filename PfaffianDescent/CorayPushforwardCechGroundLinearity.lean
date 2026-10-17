import PfaffianDescent.SchemeModuleBaseLinearCategory
import PfaffianDescent.CorayPushforwardCechHomTransport
import PfaffianDescent.CorayCechIntersectionHomTerms

/-! Ground-field compatibility of the ACTUAL preimage Čech comparison.
The source action is induced by actual pi; the target action is induced by
actual f ≫ pi. Original section actions and actual pushforward are retained.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {X Y : Scheme.{u}} {ι : Type u}

/-- Actual scheme pullback carries actual original base constants to the
actual constants for the composed original base morphism. -/
theorem schemeOpenBaseRingHom_pullback
    (pi : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) (U : X.Opens) (c : K) :
    f.app U (schemeOpenBaseRingHom pi U c) =
      schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U) c := by
  change f.app U
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (affineFunctionHom pi c)) =
    Y.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op
      (affineFunctionHom (f ≫ pi) c)
  rw [affineFunctionHom_comp]
  have h := ConcreteCategory.congr_hom (f.naturality
    (homOfLE (show U ≤ ⊤ from le_top)).op) (affineFunctionHom pi c)
  change f.app U
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (affineFunctionHom pi c)) =
    Y.presheaf.map ((TopologicalSpace.Opens.map f.base).map
      (homOfLE (show U ≤ ⊤ from le_top))).op (f.appTop (affineFunctionHom pi c)) at h
  have hi : (TopologicalSpace.Opens.map f.base).map (homOfLE (show U ≤ ⊤ from le_top)) =
      homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top) := Subsingleton.elim _ _
  rw [hi] at h
  exact h

/-- Actual pushed-forward sections preserve the existing pi and f≫pi
K-actions, using the actual pushed module's restriction of scalars. -/
def schemeModulePushforward_openSectionsLinearEquiv
    (pi : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) (M : Y.Modules) (U : X.Opens) :
    SchemeModuleOpenSectionsOver pi ((Scheme.Modules.pushforward f).obj M) U ≃ₗ[K]
      SchemeModuleOpenSectionsOver (f ≫ pi) M (f ⁻¹ᵁ U) where
  toAddEquiv := schemeModulePushforward_openSectionsAddEquiv f M U
  map_smul' c s := by
    change f.app U (schemeOpenBaseRingHom pi U c) •
        (show M.val.obj (op (f ⁻¹ᵁ U)) from s) =
      schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U) c •
        (show M.val.obj (op (f ⁻¹ᵁ U)) from s)
    rw [schemeOpenBaseRingHom_pullback]

/-- The actual equality-of-opens transport preserves the existing base
field action on sections. It is not used to define either scalar action. -/
theorem schemeModule_openEqSectionsAddEquiv_smul
    (pi : Y ⟶ Spec (CommRingCat.of K)) (M : Y.Modules)
    {U V : Y.Opens} (h : U = V) (c : K)
    (s : SchemeModuleOpenSectionsOver pi M U) :
    (show SchemeModuleOpenSectionsOver pi M V from
      schemeModule_openEqSectionsAddEquiv M h (c • s)) =
      c • (show SchemeModuleOpenSectionsOver pi M V from
        schemeModule_openEqSectionsAddEquiv M h s) := by
  subst V
  rfl

/-- Actual tuple-valued section-representer Yoneda is linear for the
actual base-linear category and existing original section K-actions. -/
def schemeModuleCechHomLinearEquivPi
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (U : ι → X.Opens) (n : ℕ) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ((show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X n) ⟶ M) ≃ₗ[K]
      (∀ a : Fin (n + 1) → ι,
        SchemeModuleOpenSectionsOver pi M (∏ᶜ fun b : Fin (n + 1) => U (a b))) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  refine
    { toAddEquiv := sectionRepresenterCechHomAddEquivPi X.ringCatSheaf U M n
      map_smul' := ?_ }
  intro c h
  funext a
  change schemeSectionRepresenterHomLinearEquiv pi _ M
      (Sigma.ι (fun t : Fin (n + 1) → ι =>
          sectionRepresenter X.ringCatSheaf
            (∏ᶜ fun b : Fin (n + 1) => U (t b))) a ≫ (c • h)) =
    c • schemeSectionRepresenterHomLinearEquiv pi _ M
      (Sigma.ι (fun t : Fin (n + 1) → ι =>
          sectionRepresenter X.ringCatSheaf
            (∏ᶜ fun b : Fin (n + 1) => U (t b))) a ≫ h)
  rw [Linear.comp_smul]
  exact (schemeSectionRepresenterHomLinearEquiv pi _ M).map_smul c _

/-- The genuine Hom cochain comparison commutes with the actual base
field actions, constructed independently on the two actual categories. -/
theorem schemeModulePushforwardCechHomAddEquiv_smul
    (pi : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) (M : Y.Modules)
    (U : ι → X.Opens) (n : ℕ) (c : K)
    (h : (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X n) ⟶
      (Scheme.Modules.pushforward f).obj M) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
    schemeModulePushforwardCechHomAddEquiv f M U n (c • h) =
      c • (show
        (show Y.Modules from
          (sectionRepresenterCechChain Y.ringCatSheaf (fun i => f ⁻¹ᵁ U i)).X n) ⟶ M from
        schemeModulePushforwardCechHomAddEquiv f M U n h) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
  let AX := schemeModuleCechHomLinearEquivPi pi ((Scheme.Modules.pushforward f).obj M) U n
  let AY := schemeModuleCechHomLinearEquivPi (f ≫ pi) M (fun i => f ⁻¹ᵁ U i) n
  apply AY.injective
  rw [AY.map_smul]
  funext a
  change sectionRepresenterCechHomEquivPi Y.ringCatSheaf (fun i => f ⁻¹ᵁ U i) M n
      (schemeModulePushforwardCechHomAddEquiv f M U n (c • h)) a =
    c • (show SchemeModuleOpenSectionsOver (f ≫ pi) M
        (∏ᶜ fun b : Fin (n + 1) => f ⁻¹ᵁ U (a b)) from
      sectionRepresenterCechHomEquivPi Y.ringCatSheaf (fun i => f ⁻¹ᵁ U i) M n
        (schemeModulePushforwardCechHomAddEquiv f M U n h) a)
  rw [schemeModulePushforwardCechHomAddEquiv_apply,
    schemeModulePushforwardCechHomAddEquiv_apply]
  change schemeModule_openEqSectionsAddEquiv M
      (schemeOpen_preimage_finiteProduct f (fun b : Fin (n + 1) => U (a b)))
      (schemeModulePushforward_openSectionsLinearEquiv pi f M _ (AX (c • h) a)) = _
  rw [AX.map_smul]
  change schemeModule_openEqSectionsAddEquiv M
      (schemeOpen_preimage_finiteProduct f (fun b : Fin (n + 1) => U (a b)))
      (schemeModulePushforward_openSectionsLinearEquiv pi f M _ (c • AX h a)) = _
  rw [(schemeModulePushforward_openSectionsLinearEquiv pi f M _).map_smul]
  exact schemeModule_openEqSectionsAddEquiv_smul (f ≫ pi) M _ c _

/-- Linear upgrade of the SAME actual cochain comparison from the frozen
additive packet. No replacement map or transported scalar structure. -/
def schemeModulePushforwardCechHomLinearEquiv
    (pi : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) (M : Y.Modules)
    (U : ι → X.Opens) (n : ℕ) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
    ((show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X n) ⟶
      (Scheme.Modules.pushforward f).obj M) ≃ₗ[K]
    ((show Y.Modules from
      (sectionRepresenterCechChain Y.ringCatSheaf (fun i => f ⁻¹ᵁ U i)).X n) ⟶ M) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
  exact
    { toAddEquiv := schemeModulePushforwardCechHomAddEquiv f M U n
      map_smul' := schemeModulePushforwardCechHomAddEquiv_smul pi f M U n }

/-- The existing actual represented ground-scalar endomorphism on a
Čech term is exactly categorical K-multiplication on that SAME term. -/
theorem schemeModuleCechGroundScalarEndomorphism_eq_smul_id
    (pi : X ⟶ Spec (CommRingCat.of K)) (U : ι → X.Opens) (n : ℕ) (c : K) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    schemeModuleCechGroundScalarEndomorphism pi U n c =
      c • 𝟙 (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X n) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let C : X.Modules := (sectionRepresenterCechChain X.ringCatSheaf U).X n
  let A := schemeModuleCechHomLinearEquivPi pi C U n
  apply A.injective
  rw [A.map_smul]
  funext a
  have hc := schemeModuleCechHomEquivPi_groundScalar pi C U n c (𝟙 C) a
  change A (schemeModuleCechGroundScalarEndomorphism pi U n c ≫ 𝟙 C) a =
    c • A (𝟙 C) a at hc
  change A (schemeModuleCechGroundScalarEndomorphism pi U n c) a = c • A (𝟙 C) a
  exact (congrArg (fun h : C ⟶ C => A h a)
    (Category.comp_id (show C ⟶ C from
      schemeModuleCechGroundScalarEndomorphism pi U n c))).symm.trans hc

end PfaffianDescent.Coray
