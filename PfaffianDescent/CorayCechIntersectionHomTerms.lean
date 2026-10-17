import PfaffianDescent.CorayClosedSupportAugmentedCechOne
import PfaffianDescent.SectionRepresenterScalar
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! SOURCE ONLY / UNVERIFIED. The existing section-representer Čech chain
uses chosen categorical products of opens. These terms are identified with
the actual original-ground-field sections on the literal intersections in
degrees 0, 1, and 2. No cohomology or acyclicity premise is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) {ι : Type u}

/-- Transport along equality of opens preserves the given ground-field
module structure, rather than choosing a new scalar structure. -/
def schemeModule_openEqSectionsLinearEquiv {W T : X.Opens} (h : W = T) :
    SchemeModuleOpenSectionsOver pi M W ≃ₗ[K]
      SchemeModuleOpenSectionsOver pi M T := by
  subst T
  exact LinearEquiv.refl K _

/-- Equality transport is the actual sheaf restriction along the equality. -/
theorem schemeModule_openEqSectionsLinearEquiv_apply
    {W T : X.Opens} (h : W = T) (s : SchemeModuleOpenSectionsOver pi M W) :
    schemeModule_openEqSectionsLinearEquiv pi M h s =
      schemeModuleOpenSectionsRestrictionLinearMap pi M h.symm.le s := by
  subst T
  change s = M.presheaf.map (homOfLE (show W ≤ W from le_rfl)).op s
  simpa using (ConcreteCategory.congr_hom (M.presheaf.map_id (op W)) s).symm

/-- Equality transport commutes with every actual restriction of sections.
The map `f` is a morphism of opens, so thinness identifies it with the
corresponding inclusion; no comparison-map hypothesis is required. -/
theorem schemeModule_openEqSectionsLinearEquiv_naturality
    {W T W' T' : X.Opens} (hW : W = W') (hT : T = T')
    (f : T ⟶ W) (hTW : T' ≤ W') (s : SchemeModuleOpenSectionsOver pi M W) :
    schemeModule_openEqSectionsLinearEquiv pi M hT (M.val.map f.op s) =
      schemeModuleOpenSectionsRestrictionLinearMap pi M hTW
        (schemeModule_openEqSectionsLinearEquiv pi M hW s) := by
  subst W'
  subst T'
  have hf : f = homOfLE hTW := Subsingleton.elim _ _
  subst f
  rfl

theorem schemeOpenCechProduct_zero_eq (V : ι → X.Opens) (f : Fin 1 → ι) :
    (∏ᶜ fun a : Fin 1 => V (f a)) = V (f 0) := by
  apply le_antisymm
  · exact (Pi.π (fun a : Fin 1 => V (f a)) 0).le
  · exact (Pi.lift fun a => homOfLE (by fin_cases a; exact le_rfl)).le

theorem schemeOpenCechProduct_one_eq (V : ι → X.Opens) (f : Fin 2 → ι) :
    (∏ᶜ fun a : Fin 2 => V (f a)) = V (f 0) ⊓ V (f 1) := by
  apply le_antisymm
  · exact le_inf (Pi.π (fun a : Fin 2 => V (f a)) 0).le
      (Pi.π (fun a : Fin 2 => V (f a)) 1).le
  · exact (Pi.lift fun a => homOfLE (by
      fin_cases a
      · exact inf_le_left
      · exact inf_le_right)).le

theorem schemeOpenCechProduct_two_eq (V : ι → X.Opens) (f : Fin 3 → ι) :
    (∏ᶜ fun a : Fin 3 => V (f a)) = V (f 0) ⊓ (V (f 1) ⊓ V (f 2)) := by
  apply le_antisymm
  · exact le_inf (Pi.π (fun a : Fin 3 => V (f a)) 0).le
      (le_inf (Pi.π (fun a : Fin 3 => V (f a)) 1).le
        (Pi.π (fun a : Fin 3 => V (f a)) 2).le)
  · exact (Pi.lift fun a => homOfLE (by
      fin_cases a
      · exact inf_le_left
      · exact inf_le_right.trans inf_le_left
      · exact inf_le_right.trans inf_le_right)).le

def schemeModuleCechTupleZeroLinearEquiv (V : ι → X.Opens) :
    (∀ f : Fin 1 → ι,
      SchemeModuleOpenSectionsOver pi M (∏ᶜ fun a : Fin 1 => V (f a))) ≃ₗ[K]
      SchemeModuleCechZeroCoefficients pi M V where
  toFun s i := schemeModule_openEqSectionsLinearEquiv pi M
    (schemeOpenCechProduct_zero_eq V ![i]) (s ![i])
  invFun z f := (schemeModule_openEqSectionsLinearEquiv pi M
    (schemeOpenCechProduct_zero_eq V f)).symm (z (f 0))
  left_inv s := by
    funext f
    obtain ⟨i, rfl⟩ : ∃ i : ι, f = ![i] := by
      refine ⟨f 0, ?_⟩
      funext a
      fin_cases a <;> rfl
    exact (schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_zero_eq V ![i])).symm_apply_apply (s ![i])
  right_inv z := by
    funext i
    exact (schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_zero_eq V ![i])).apply_symm_apply (z i)
  map_add' s t := by
    funext i
    exact (schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_zero_eq V ![i])).map_add _ _
  map_smul' c s := by
    funext i
    exact (schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_zero_eq V ![i])).map_smul _ _

def schemeModuleCechTupleOneLinearEquiv (V : ι → X.Opens) :
    (∀ f : Fin 2 → ι,
      SchemeModuleOpenSectionsOver pi M (∏ᶜ fun a : Fin 2 => V (f a))) ≃ₗ[K]
      SchemeModuleCechOneCoefficients pi M V where
  toFun s i j := schemeModule_openEqSectionsLinearEquiv pi M
    (schemeOpenCechProduct_one_eq V ![i, j]) (s ![i, j])
  invFun z f := (schemeModule_openEqSectionsLinearEquiv pi M
    (schemeOpenCechProduct_one_eq V f)).symm (z (f 0) (f 1))
  left_inv s := by
    funext f
    obtain ⟨i, j, rfl⟩ : ∃ i j : ι, f = ![i, j] := by
      refine ⟨f 0, f 1, ?_⟩
      funext a
      fin_cases a <;> rfl
    exact (schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V ![i, j])).symm_apply_apply (s ![i, j])
  right_inv z := by
    funext i j
    exact (schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V ![i, j])).apply_symm_apply (z i j)
  map_add' s t := by
    funext i j
    exact (schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V ![i, j])).map_add _ _
  map_smul' c s := by
    funext i j
    exact (schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V ![i, j])).map_smul _ _

def schemeModuleCechTupleTwoLinearEquiv (V : ι → X.Opens) :
    (∀ f : Fin 3 → ι,
      SchemeModuleOpenSectionsOver pi M (∏ᶜ fun a : Fin 3 => V (f a))) ≃ₗ[K]
      SchemeModuleCechTwoCoefficients pi M V where
  toFun s i j k := schemeModule_openEqSectionsLinearEquiv pi M
    (schemeOpenCechProduct_two_eq V ![i, j, k]) (s ![i, j, k])
  invFun z f := (schemeModule_openEqSectionsLinearEquiv pi M
    (schemeOpenCechProduct_two_eq V f)).symm (z (f 0) (f 1) (f 2))
  left_inv s := by
    funext f
    obtain ⟨i, j, k, rfl⟩ : ∃ i j k : ι, f = ![i, j, k] := by
      refine ⟨f 0, f 1, f 2, ?_⟩
      funext a
      fin_cases a <;> rfl
    exact (schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_two_eq V ![i, j, k])).symm_apply_apply (s ![i, j, k])
  right_inv z := by
    funext i j k
    exact (schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_two_eq V ![i, j, k])).apply_symm_apply (z i j k)
  map_add' s t := by
    funext i j k
    exact (schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_two_eq V ![i, j, k])).map_add _ _
  map_smul' c s := by
    funext i j k
    exact (schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_two_eq V ![i, j, k])).map_smul _ _

/-- The actual ground scalar on a categorical Čech term: on each
section-representer summand, use the original base morphism to obtain the
constant ring section, then the genuine represented scalar endomorphism. -/
def schemeModuleCechGroundScalarEndomorphism (V : ι → X.Opens) (n : ℕ) (c : K) :
    (sectionRepresenterCechChain X.ringCatSheaf V).X n ⟶
      (sectionRepresenterCechChain X.ringCatSheaf V).X n :=
  Sigma.desc fun f : Fin (n + 1) → ι =>
    sectionRepresenterScalarEndomorphism X.ringCatSheaf
        (∏ᶜ fun a : Fin (n + 1) => V (f a))
        (schemeOpenBaseRingHom pi (∏ᶜ fun a : Fin (n + 1) => V (f a)) c) ≫
      Sigma.ι (fun g : Fin (n + 1) → ι =>
        sectionRepresenter X.ringCatSheaf
          (∏ᶜ fun a : Fin (n + 1) => V (g a))) f

theorem schemeModuleCechHomEquivPi_groundScalar (V : ι → X.Opens) (n : ℕ) (c : K)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X n ⟶ M)
    (f : Fin (n + 1) → ι) :
    (show SchemeModuleOpenSectionsOver pi M (∏ᶜ fun a : Fin (n + 1) => V (f a)) from
      sectionRepresenterCechHomEquivPi X.ringCatSheaf V M n
        (schemeModuleCechGroundScalarEndomorphism pi V n c ≫ h) f) =
      c • (show SchemeModuleOpenSectionsOver pi M
          (∏ᶜ fun a : Fin (n + 1) => V (f a)) from
        sectionRepresenterCechHomEquivPi X.ringCatSheaf V M n h f) := by
  change sectionRepresenterHomEquiv X.ringCatSheaf
      (∏ᶜ fun a : Fin (n + 1) => V (f a)) M
      (Sigma.ι (fun g : Fin (n + 1) → ι =>
        sectionRepresenter X.ringCatSheaf
          (∏ᶜ fun a : Fin (n + 1) => V (g a))) f ≫
        (schemeModuleCechGroundScalarEndomorphism pi V n c ≫ h)) = _
  rw [← Category.assoc]
  change sectionRepresenterHomEquiv X.ringCatSheaf
      (∏ᶜ fun a : Fin (n + 1) => V (f a)) M
      ((Sigma.ι (fun g : Fin (n + 1) → ι =>
          sectionRepresenter X.ringCatSheaf
            (∏ᶜ fun a : Fin (n + 1) => V (g a))) f ≫
        Sigma.desc (fun g : Fin (n + 1) → ι =>
          sectionRepresenterScalarEndomorphism X.ringCatSheaf
            (∏ᶜ fun a : Fin (n + 1) => V (g a))
            (schemeOpenBaseRingHom pi (∏ᶜ fun a : Fin (n + 1) => V (g a)) c) ≫
          Sigma.ι (fun t : Fin (n + 1) → ι =>
            sectionRepresenter X.ringCatSheaf
              (∏ᶜ fun a : Fin (n + 1) => V (t a))) g)) ≫ h) = _
  rw [Sigma.ι_desc, Category.assoc]
  exact sectionRepresenterHomEquiv_scalarEndomorphism_comp X.ringCatSheaf _ M _ _

def schemeModuleCechHomZeroAddEquiv (V : ι → X.Opens) :
    ((sectionRepresenterCechChain X.ringCatSheaf V).X 0 ⟶ M) ≃+
      SchemeModuleCechZeroCoefficients pi M V :=
  (sectionRepresenterCechHomAddEquivPi X.ringCatSheaf V M 0).trans
    (schemeModuleCechTupleZeroLinearEquiv pi M V).toAddEquiv

def schemeModuleCechHomOneAddEquiv (V : ι → X.Opens) :
    ((sectionRepresenterCechChain X.ringCatSheaf V).X 1 ⟶ M) ≃+
      SchemeModuleCechOneCoefficients pi M V :=
  (sectionRepresenterCechHomAddEquivPi X.ringCatSheaf V M 1).trans
    (schemeModuleCechTupleOneLinearEquiv pi M V).toAddEquiv

def schemeModuleCechHomTwoAddEquiv (V : ι → X.Opens) :
    ((sectionRepresenterCechChain X.ringCatSheaf V).X 2 ⟶ M) ≃+
      SchemeModuleCechTwoCoefficients pi M V :=
  (sectionRepresenterCechHomAddEquivPi X.ringCatSheaf V M 2).trans
    (schemeModuleCechTupleTwoLinearEquiv pi M V).toAddEquiv

theorem schemeModuleCechHomZeroAddEquiv_groundScalar (V : ι → X.Opens) (c : K)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X 0 ⟶ M) :
    schemeModuleCechHomZeroAddEquiv pi M V
        (schemeModuleCechGroundScalarEndomorphism pi V 0 c ≫ h) =
      c • schemeModuleCechHomZeroAddEquiv pi M V h := by
  change schemeModuleCechTupleZeroLinearEquiv pi M V
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0
        (schemeModuleCechGroundScalarEndomorphism pi V 0 c ≫ h)) =
    c • schemeModuleCechTupleZeroLinearEquiv pi M V
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h)
  rw [← map_smul]
  apply congrArg (schemeModuleCechTupleZeroLinearEquiv pi M V)
  funext f
  exact schemeModuleCechHomEquivPi_groundScalar pi M V 0 c h f

theorem schemeModuleCechHomOneAddEquiv_groundScalar (V : ι → X.Opens) (c : K)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X 1 ⟶ M) :
    schemeModuleCechHomOneAddEquiv pi M V
        (schemeModuleCechGroundScalarEndomorphism pi V 1 c ≫ h) =
      c • schemeModuleCechHomOneAddEquiv pi M V h := by
  change schemeModuleCechTupleOneLinearEquiv pi M V
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1
        (schemeModuleCechGroundScalarEndomorphism pi V 1 c ≫ h)) =
    c • schemeModuleCechTupleOneLinearEquiv pi M V
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h)
  rw [← map_smul]
  apply congrArg (schemeModuleCechTupleOneLinearEquiv pi M V)
  funext f
  exact schemeModuleCechHomEquivPi_groundScalar pi M V 1 c h f

theorem schemeModuleCechHomTwoAddEquiv_groundScalar (V : ι → X.Opens) (c : K)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X 2 ⟶ M) :
    schemeModuleCechHomTwoAddEquiv pi M V
        (schemeModuleCechGroundScalarEndomorphism pi V 2 c ≫ h) =
      c • schemeModuleCechHomTwoAddEquiv pi M V h := by
  change schemeModuleCechTupleTwoLinearEquiv pi M V
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 2
        (schemeModuleCechGroundScalarEndomorphism pi V 2 c ≫ h)) =
    c • schemeModuleCechTupleTwoLinearEquiv pi M V
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 2 h)
  rw [← map_smul]
  apply congrArg (schemeModuleCechTupleTwoLinearEquiv pi M V)
  funext f
  exact schemeModuleCechHomEquivPi_groundScalar pi M V 2 c h f

end PfaffianDescent.Coray
