import PfaffianDescent.CorayPushforwardCechHomTransport
import PfaffianDescent.SectionRepresenterCechCoefficientNaturality

/-! Actual coefficient naturality of the original preimage Cech transport.
This supplies literal transported lift equations for the canonical Ext
comparison. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {X Y : Scheme.{u}} {ι : Type u}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem openEqSections_postcomp (M N : Y.Modules)
    {V W : Y.Opens} (h : V = W) (g : M ⟶ N) (s : M.val.obj (op V)) :
    schemeModule_openEqSectionsAddEquiv N h (g.val.app (op V) s) =
      g.val.app (op W) (schemeModule_openEqSectionsAddEquiv M h s) := by
  subst W
  rfl

private theorem nativeCechCoordinate_postcomp
    (A B : X.Modules) (U : ι → X.Opens) (n : ℕ)
    (k : (sectionRepresenterCechChain X.ringCatSheaf U).X n ⟶ A)
    (g : A ⟶ B) (a : Fin (n + 1) → ι) :
    sectionRepresenterCechHomEquivPi X.ringCatSheaf U B n (k ≫ g) a =
      g.val.app (op (∏ᶜ fun b : Fin (n + 1) => U (a b)))
        (sectionRepresenterCechHomEquivPi X.ringCatSheaf U A n k a) := by
  exact sectionRepresenterCechHomEquivPi_postcomp X.ringCatSheaf U n k g a

private theorem nativePushforwardSection_postcomp
    (f : Y ⟶ X) (M N : Y.Modules) (V : X.Opens) (g : M ⟶ N)
    (s : ((Scheme.Modules.pushforward f).obj M).val.obj (op V)) :
    schemeModulePushforward_openSectionsAddEquiv f N V
      (((Scheme.Modules.pushforward f).map g).val.app (op V) s) =
      g.val.app (op (f ⁻¹ᵁ V))
        (schemeModulePushforward_openSectionsAddEquiv f M V s) := by
  rfl

private theorem nativeCechInverseCocycle_value
    (f : Y ⟶ X) (M : Y.Modules) (U : ι → X.Opens)
    (z : DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf
      (fun a => f ⁻¹ᵁ U a)).d 2 1) (Y := M)) :
    ((schemeModulePushforwardCechOneCocycleAddEquiv f M U).symm z).1 =
      (schemeModulePushforwardCechHomAddEquiv f M U 1).symm z.1 := by
  rfl

/-- Original preimage cochain transport commutes with the original
coefficient morphism, by its actual intersection section formulas. -/
theorem schemeModulePushforwardCechHomAddEquiv_postcomp
    (f : Y ⟶ X) (M N : Y.Modules) (U : ι → X.Opens) (n : ℕ)
    (h : (sectionRepresenterCechChain X.ringCatSheaf U).X n ⟶
      (Scheme.Modules.pushforward f).obj M) (g : M ⟶ N) :
    schemeModulePushforwardCechHomAddEquiv f N U n
      (h ≫ (Scheme.Modules.pushforward f).map g) =
      schemeModulePushforwardCechHomAddEquiv f M U n h ≫ g := by
  apply (sectionRepresenterCechHomAddEquivPi Y.ringCatSheaf
    (fun a => f ⁻¹ᵁ U a) N n).injective
  funext a
  let V : X.Opens := ∏ᶜ fun b : Fin (n + 1) => U (a b)
  let T : Y.Opens := ∏ᶜ fun b : Fin (n + 1) => f ⁻¹ᵁ U (a b)
  let e : f ⁻¹ᵁ V = T :=
    schemeOpen_preimage_finiteProduct f (fun b : Fin (n + 1) => U (a b))
  let P := (Scheme.Modules.pushforward f).obj M
  let Q := (Scheme.Modules.pushforward f).obj N
  let s : P.val.obj (op V) := sectionRepresenterCechHomEquivPi X.ringCatSheaf U P n h a
  have hcoord := nativeCechCoordinate_postcomp P Q U n h
    ((Scheme.Modules.pushforward f).map g) a
  have hsection := nativePushforwardSection_postcomp f M N V g s
  have hsource := schemeModulePushforwardCechHomAddEquiv_apply f M U n h a
  have htarget := schemeModulePushforwardCechHomAddEquiv_apply f N U n
    (h ≫ (Scheme.Modules.pushforward f).map g) a
  have hfinal := nativeCechCoordinate_postcomp M N (fun b => f ⁻¹ᵁ U b) n
    (schemeModulePushforwardCechHomAddEquiv f M U n h) g a
  calc
    sectionRepresenterCechHomEquivPi Y.ringCatSheaf (fun b => f ⁻¹ᵁ U b) N n
        (schemeModulePushforwardCechHomAddEquiv f N U n
          (h ≫ (Scheme.Modules.pushforward f).map g)) a =
      schemeModule_openEqSectionsAddEquiv N e
        (schemeModulePushforward_openSectionsAddEquiv f N V
          (sectionRepresenterCechHomEquivPi X.ringCatSheaf U Q n
            (h ≫ (Scheme.Modules.pushforward f).map g) a)) := htarget
    _ = schemeModule_openEqSectionsAddEquiv N e
        (schemeModulePushforward_openSectionsAddEquiv f N V
          (((Scheme.Modules.pushforward f).map g).val.app (op V) s)) :=
      congrArg (fun t : Q.val.obj (op V) =>
        schemeModule_openEqSectionsAddEquiv N e
          (schemeModulePushforward_openSectionsAddEquiv f N V t)) hcoord
    _ = schemeModule_openEqSectionsAddEquiv N e
        (g.val.app (op (f ⁻¹ᵁ V))
          (schemeModulePushforward_openSectionsAddEquiv f M V s)) :=
      congrArg (fun t : N.val.obj (op (f ⁻¹ᵁ V)) =>
        schemeModule_openEqSectionsAddEquiv N e t) hsection
    _ = g.val.app (op T) (schemeModule_openEqSectionsAddEquiv M e
        (schemeModulePushforward_openSectionsAddEquiv f M V s)) :=
      openEqSections_postcomp M N e g
        (schemeModulePushforward_openSectionsAddEquiv f M V s)
    _ = g.val.app (op T)
        (sectionRepresenterCechHomEquivPi Y.ringCatSheaf
          (fun b => f ⁻¹ᵁ U b) M n
          (schemeModulePushforwardCechHomAddEquiv f M U n h) a) :=
      congrArg (fun t : M.val.obj (op T) => g.val.app (op T) t) hsource.symm
    _ = sectionRepresenterCechHomEquivPi Y.ringCatSheaf
        (fun b => f ⁻¹ᵁ U b) N n
        (schemeModulePushforwardCechHomAddEquiv f M U n h ≫ g) a := hfinal.symm

/-- The inverse of the SAME cochain transport commutes with original
coefficient maps; this is the literal map needed for transported lifts. -/
theorem schemeModulePushforwardCechHomAddEquiv_symm_postcomp
    (f : Y ⟶ X) (M N : Y.Modules) (U : ι → X.Opens) (n : ℕ)
    (h : (sectionRepresenterCechChain Y.ringCatSheaf
      (fun a => f ⁻¹ᵁ U a)).X n ⟶ M) (g : M ⟶ N) :
    (schemeModulePushforwardCechHomAddEquiv f N U n).symm (h ≫ g) =
      (schemeModulePushforwardCechHomAddEquiv f M U n).symm h ≫
        (Scheme.Modules.pushforward f).map g := by
  apply (schemeModulePushforwardCechHomAddEquiv f N U n).injective
  rw [AddEquiv.apply_symm_apply, schemeModulePushforwardCechHomAddEquiv_postcomp,
    AddEquiv.apply_symm_apply]

/-- Actual cocycle-lift equations transport by actual pushforward maps and
the original differential square, without any desired Ext-map equality. -/
theorem schemeModulePushforwardCech_degreeOneLiftEquation
    (f : Y ⟶ X) (M N : Y.Modules) (g : M ⟶ N) (U : ι → X.Opens)
    (p : (sectionRepresenterCechChain Y.ringCatSheaf
      (fun a => f ⁻¹ᵁ U a)).X 0 ⟶ N)
    (z : DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf
      (fun a => f ⁻¹ᵁ U a)).d 2 1) (Y := M))
    (hz : (sectionRepresenterCechChain Y.ringCatSheaf
      (fun a => f ⁻¹ᵁ U a)).d 1 0 ≫ p = z.1 ≫ g) :
    (sectionRepresenterCechChain X.ringCatSheaf U).d 1 0 ≫
        (schemeModulePushforwardCechHomAddEquiv f N U 0).symm p =
      ((schemeModulePushforwardCechOneCocycleAddEquiv f M U).symm z).1 ≫
        (Scheme.Modules.pushforward f).map g := by
  let E₀ := schemeModulePushforwardCechHomAddEquiv f N U 0
  let E₁ := schemeModulePushforwardCechHomAddEquiv f N U 1
  let EM := schemeModulePushforwardCechHomAddEquiv f M U 1
  let C := sectionRepresenterCechChain Y.ringCatSheaf (fun a => f ⁻¹ᵁ U a)
  let zX := ((schemeModulePushforwardCechOneCocycleAddEquiv f M U).symm z).1
  have hvalue : EM zX = z.1 :=
    (congrArg (fun k => EM k) (nativeCechInverseCocycle_value f M U z)).trans
      (EM.apply_symm_apply z.1)
  have hleft : E₁ ((sectionRepresenterCechChain X.ringCatSheaf U).d 1 0 ≫ E₀.symm p) =
      C.d 1 0 ≫ p :=
    (schemeModulePushforwardCechHomAddEquiv_d f N U 0 (E₀.symm p)).trans
      (congrArg (fun k : C.X 0 ⟶ N => C.d 1 0 ≫ k) (E₀.apply_symm_apply p))
  have hright : E₁ (zX ≫ (Scheme.Modules.pushforward f).map g) = z.1 ≫ g :=
    (schemeModulePushforwardCechHomAddEquiv_postcomp f M N U 1 zX g).trans
      (congrArg (fun k : C.X 1 ⟶ M => k ≫ g) hvalue)
  apply E₁.injective
  exact hleft.trans (hz.trans hright.symm)

end PfaffianDescent.Coray
end
