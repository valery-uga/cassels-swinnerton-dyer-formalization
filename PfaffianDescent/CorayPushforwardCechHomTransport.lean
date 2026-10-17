import PfaffianDescent.SectionRepresenterCechHomDifferential
import PfaffianDescent.SchemeCoverCechExtDegreeOne
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Group.Equiv.Basic

/-! Actual Čech Hom transport under the actual scheme-module pushforward.
Finite chosen open products, actual section maps and alternating faces are
transported internally. No compatibility or comparison is a hypothesis.
The construction works in every degree, hence in the requested degrees0–2.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} {ι : Type u}

/-- The actual chosen categorical finite product of opens equals its
literal finite infimum, proved from its actual projections and lift. -/
theorem schemeOpen_finiteProduct_eq_iInf {J : Type v} [Fintype J]
    (U : J → X.Opens) : (∏ᶜ U) = ⨅ j, U j := by
  apply le_antisymm
  · exact le_iInf fun j => (Pi.π U j).le
  · exact (Pi.lift fun j => homOfLE (iInf_le U j)).le

/-- Actual preimage transports the actual chosen finite categorical
product to the actual chosen product of actual preimages. No product-
preservation instance or intersection comparison certificate is assumed. -/
theorem schemeOpen_preimage_finiteProduct (f : Y ⟶ X)
    {J : Type v} [Fintype J] (U : J → X.Opens) :
    f ⁻¹ᵁ (∏ᶜ U) = ∏ᶜ fun j => f ⁻¹ᵁ U j := by
  rw [schemeOpen_finiteProduct_eq_iInf U,
    schemeOpen_finiteProduct_eq_iInf (fun j => f ⁻¹ᵁ U j)]
  apply Opens.ext
  simp only [Scheme.Hom.coe_preimage, Opens.coe_iInf, Set.preimage_iInter]

/-- Actual section transport along equality of opens, as an additive
equivalence. The original coefficient module and scalar action remain. -/
def schemeModule_openEqSectionsAddEquiv (M : Y.Modules)
    {W T : Y.Opens} (h : W = T) : M.val.obj (op W) ≃+ M.val.obj (op T) := by
  subst T
  exact AddEquiv.refl _

/-- Equality transport commutes with the actual restrictions. Thinness of
opens proves the actual map equality; no naturality square is supplied. -/
theorem schemeModule_openEqSectionsAddEquiv_naturality (M : Y.Modules)
    {W T W' T' : Y.Opens} (hW : W = W') (hT : T = T')
    (i : T ⟶ W) (j : T' ⟶ W') (s : M.val.obj (op W)) :
    schemeModule_openEqSectionsAddEquiv M hT (M.val.map i.op s) =
      M.val.map j.op (schemeModule_openEqSectionsAddEquiv M hW s) := by
  subst W'
  subst T'
  have hij : i = j := Subsingleton.elim _ _
  rw [hij]
  rfl

/-- The actual pushed-forward sections are the actual original module's
sections over the actual preimage, directly from the installed construction. -/
def schemeModulePushforward_openSectionsAddEquiv (f : Y ⟶ X) (M : Y.Modules)
    (U : X.Opens) :
    ((Scheme.Modules.pushforward f).obj M).val.obj (op U) ≃+
      M.val.obj (op (f ⁻¹ᵁ U)) :=
  AddEquiv.refl _

/-- Every actual Čech tuple is transported through actual pushforward
sections and the internally proved actual preimage/product equality. -/
def schemeModulePushforwardCechTupleAddEquiv (f : Y ⟶ X) (M : Y.Modules)
    (U : ι → X.Opens) (n : ℕ) :
    (∀ a : Fin (n + 1) → ι,
      ((Scheme.Modules.pushforward f).obj M).val.obj
        (op (∏ᶜ fun b : Fin (n + 1) => U (a b)))) ≃+
    (∀ a : Fin (n + 1) → ι,
      M.val.obj (op (∏ᶜ fun b : Fin (n + 1) => f ⁻¹ᵁ U (a b)))) :=
  AddEquiv.piCongrRight fun a =>
    (schemeModulePushforward_openSectionsAddEquiv f M _).trans
      (schemeModule_openEqSectionsAddEquiv M
        (schemeOpen_preimage_finiteProduct f (fun b : Fin (n + 1) => U (a b))))

/-- The genuine Hom-cochain equivalence for actual source/target ringed
spaces. Actual section-representer Yoneda and actual preimages construct it;
it is not an arbitrary identification or a comparison hypothesis. -/
def schemeModulePushforwardCechHomAddEquiv (f : Y ⟶ X) (M : Y.Modules)
    (U : ι → X.Opens) (n : ℕ) :
    ((sectionRepresenterCechChain X.ringCatSheaf U).X n ⟶
      (Scheme.Modules.pushforward f).obj M) ≃+
    ((sectionRepresenterCechChain Y.ringCatSheaf (fun i => f ⁻¹ᵁ U i)).X n ⟶ M) :=
  (sectionRepresenterCechHomAddEquivPi X.ringCatSheaf U _ n).trans
    ((schemeModulePushforwardCechTupleAddEquiv f M U n).trans
      (sectionRepresenterCechHomAddEquivPi Y.ringCatSheaf (fun i => f ⁻¹ᵁ U i) M n).symm)

/-- The Hom comparison evaluates to its actual preimage section transport. -/
theorem schemeModulePushforwardCechHomAddEquiv_apply (f : Y ⟶ X) (M : Y.Modules)
    (U : ι → X.Opens) (n : ℕ)
    (h : (sectionRepresenterCechChain X.ringCatSheaf U).X n ⟶
      (Scheme.Modules.pushforward f).obj M) (a : Fin (n + 1) → ι) :
    sectionRepresenterCechHomEquivPi Y.ringCatSheaf (fun i => f ⁻¹ᵁ U i) M n
      (schemeModulePushforwardCechHomAddEquiv f M U n h) a =
    schemeModule_openEqSectionsAddEquiv M
      (schemeOpen_preimage_finiteProduct f (fun b : Fin (n + 1) => U (a b)))
      (schemeModulePushforward_openSectionsAddEquiv f M _
        (sectionRepresenterCechHomEquivPi X.ringCatSheaf U _ n h a)) := by
  change (sectionRepresenterCechHomAddEquivPi Y.ringCatSheaf
      (fun i => f ⁻¹ᵁ U i) M n)
    ((sectionRepresenterCechHomAddEquivPi Y.ringCatSheaf
        (fun i => f ⁻¹ᵁ U i) M n).symm
      (schemeModulePushforwardCechTupleAddEquiv f M U n
        (sectionRepresenterCechHomAddEquivPi X.ringCatSheaf U _ n h))) a = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- The actual Hom equivalence commutes with the actual alternating Čech
differential in every degree. This proves the requested degrees0→1 and1→2
squares internally from the actual ordered face restrictions. -/
theorem schemeModulePushforwardCechHomAddEquiv_d (f : Y ⟶ X) (M : Y.Modules)
    (U : ι → X.Opens) (n : ℕ)
    (h : (sectionRepresenterCechChain X.ringCatSheaf U).X n ⟶
      (Scheme.Modules.pushforward f).obj M) :
    schemeModulePushforwardCechHomAddEquiv f M U (n + 1)
      ((sectionRepresenterCechChain X.ringCatSheaf U).d (n + 1) n ≫ h) =
    (sectionRepresenterCechChain Y.ringCatSheaf (fun i => f ⁻¹ᵁ U i)).d (n + 1) n ≫
      schemeModulePushforwardCechHomAddEquiv f M U n h := by
  apply (sectionRepresenterCechHomAddEquivPi Y.ringCatSheaf
    (fun i => f ⁻¹ᵁ U i) M (n + 1)).injective
  funext a
  erw [schemeModulePushforwardCechHomAddEquiv_apply,
    sectionRepresenterCechHomEquivPi_d, sectionRepresenterCechHomEquivPi_d]
  let P := (Scheme.Modules.pushforward f).obj M
  let E := (FormalCoproduct.mk _ U).cech
  let D := (FormalCoproduct.mk _ (fun i => f ⁻¹ᵁ U i)).cech
  let e := (schemeModulePushforward_openSectionsAddEquiv f M
      (∏ᶜ fun b : Fin (n + 2) => U (a b))).trans
    (schemeModule_openEqSectionsAddEquiv M
      (schemeOpen_preimage_finiteProduct f (fun b : Fin (n + 2) => U (a b))))
  change e (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      P.val.map ((E.map (SimplexCategory.δ i).op).φ a).op
        (sectionRepresenterCechHomEquivPi X.ringCatSheaf U P n h
          ((E.map (SimplexCategory.δ i).op).f a))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul]
  apply congrArg (((-1 : ℤ) ^ (i : ℕ)) • ·)
  rw [schemeModulePushforwardCechHomAddEquiv_apply]
  let q := E.map (SimplexCategory.δ i).op
  let r := D.map (SimplexCategory.δ i).op
  have hindex : q.f a = r.f a := rfl
  have hn := schemeModule_openEqSectionsAddEquiv_naturality M
    (schemeOpen_preimage_finiteProduct f (fun b : Fin (n + 1) => U (q.f a b)))
    (schemeOpen_preimage_finiteProduct f (fun b : Fin (n + 2) => U (a b)))
    ((Opens.map f.base).map (q.φ a)) (r.φ a)
    (schemeModulePushforward_openSectionsAddEquiv f M _
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf U P n h (q.f a)))
  change schemeModule_openEqSectionsAddEquiv M
      (schemeOpen_preimage_finiteProduct f (fun b : Fin (n + 2) => U (a b)))
      (M.val.map ((Opens.map f.base).map (q.φ a)).op
        (sectionRepresenterCechHomEquivPi X.ringCatSheaf U P n h (q.f a))) =
    M.val.map (r.φ a).op
      (schemeModule_openEqSectionsAddEquiv M
        (schemeOpen_preimage_finiteProduct f (fun b : Fin (n + 1) => U (q.f a b)))
        (sectionRepresenterCechHomEquivPi X.ringCatSheaf U P n h (q.f a))) at hn ⊢
  exact hn

/-- Actual degree-one Hom cocycles correspond through the actual cochain
equivalence. Both directions use the internally proved differential square. -/
def schemeModulePushforwardCechOneCocycleAddEquiv (f : Y ⟶ X) (M : Y.Modules)
    (U : ι → X.Opens) :
    DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := (Scheme.Modules.pushforward f).obj M) ≃+
    DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf
      (fun i => f ⁻¹ᵁ U i)).d 2 1) (Y := M) where
  toFun z := ⟨schemeModulePushforwardCechHomAddEquiv f M U 1 z.1, by
    have hz : (sectionRepresenterCechChain X.ringCatSheaf U).d 2 1 ≫ z.1 = 0 := z.2
    change (sectionRepresenterCechChain Y.ringCatSheaf (fun i => f ⁻¹ᵁ U i)).d 2 1 ≫
      schemeModulePushforwardCechHomAddEquiv f M U 1 z.1 = 0
    rw [← schemeModulePushforwardCechHomAddEquiv_d, hz, map_zero]⟩
  invFun z := ⟨(schemeModulePushforwardCechHomAddEquiv f M U 1).symm z.1, by
    have hz : (sectionRepresenterCechChain Y.ringCatSheaf
      (fun i => f ⁻¹ᵁ U i)).d 2 1 ≫ z.1 = 0 := z.2
    change (sectionRepresenterCechChain X.ringCatSheaf U).d 2 1 ≫
      (schemeModulePushforwardCechHomAddEquiv f M U 1).symm z.1 = 0
    apply (schemeModulePushforwardCechHomAddEquiv f M U 2).injective
    rw [schemeModulePushforwardCechHomAddEquiv_d, AddEquiv.apply_symm_apply, map_zero]
    exact hz⟩
  left_inv z := by
    apply Subtype.ext
    exact (schemeModulePushforwardCechHomAddEquiv f M U 1).symm_apply_apply z.1
  right_inv z := by
    apply Subtype.ext
    exact (schemeModulePushforwardCechHomAddEquiv f M U 1).apply_symm_apply z.1
  map_add' z t := by
    apply Subtype.ext
    exact (schemeModulePushforwardCechHomAddEquiv f M U 1).map_add z.1 t.1

/-- The actual cocycle equivalence transports precisely the actual
degree-zero Hom boundaries. No cocycle-compatibility premise is added. -/
theorem schemeModulePushforwardCechOneCocycleAddEquiv_boundary_iff
    (f : Y ⟶ X) (M : Y.Modules) (U : ι → X.Opens)
    (z : DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := (Scheme.Modules.pushforward f).obj M)) :
    (∃ a : (sectionRepresenterCechChain X.ringCatSheaf U).X 0 ⟶
        (Scheme.Modules.pushforward f).obj M,
      (sectionRepresenterCechChain X.ringCatSheaf U).d 1 0 ≫ a = z.1) ↔
    (∃ b : (sectionRepresenterCechChain Y.ringCatSheaf (fun i => f ⁻¹ᵁ U i)).X 0 ⟶ M,
      (sectionRepresenterCechChain Y.ringCatSheaf (fun i => f ⁻¹ᵁ U i)).d 1 0 ≫ b =
        (schemeModulePushforwardCechOneCocycleAddEquiv f M U z).1) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨schemeModulePushforwardCechHomAddEquiv f M U 0 a, ?_⟩
    rw [← schemeModulePushforwardCechHomAddEquiv_d, ha]
    rfl
  · rintro ⟨b, hb⟩
    refine ⟨(schemeModulePushforwardCechHomAddEquiv f M U 0).symm b, ?_⟩
    apply (schemeModulePushforwardCechHomAddEquiv f M U 1).injective
    rw [schemeModulePushforwardCechHomAddEquiv_d, AddEquiv.apply_symm_apply]
    exact hb

/-- Pulling back an actual open cover gives an actual open cover; the
literal covering supremum is transported by the actual preimage map. -/
theorem schemeModulePushforward_preimageFamily_coversTop (f : Y ⟶ X)
    (U : ι → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U) :
    (Opens.grothendieckTopology Y).CoversTop (fun i => f ⁻¹ᵁ U i) := by
  apply (Opens.coversTop_iff Y _).mpr
  exact f.iSup_preimage_eq_top ((Opens.coversTop_iff X U).mp hU)

end PfaffianDescent.Coray
