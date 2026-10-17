import PfaffianDescent.CubicClosedPointSerreLocalKoszulAugmentation
import PfaffianDescent.CubicClosedPointSerreLocalKoszulPair

/-! # The actual affine Koszul sequence of a closed field point

The last map is constructed by the universal property of the actual ideal
kernel. Both free terms use the canonical section-one unit coordinate.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped nonZeroDivisors
universe u
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

theorem cubicClosedPointSerreLocalKoszul_exists_untwistedSequence
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hx : i default ∈ U) (q f : Γ(X, U))
    (hqreg : X.presheaf.germ U (i default) hx q ∈ (X.presheaf.stalk (i default))⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U (i default) hx q})
      (X.presheaf.germ U (i default) hx f) ∈
      ((X.presheaf.stalk (i default)) ⧸ Ideal.span {X.presheaf.germ U (i default) hx q})⁰)
    (hmax : Ideal.span ({X.presheaf.germ U (i default) hx q,
      X.presheaf.germ U (i default) hx f} : Set _) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i default)))
    (haway : ∀ (y : X) (hy : y ∈ U), y ≠ i default →
      Ideal.span ({X.presheaf.germ U y hy q, X.presheaf.germ U y hy f} : Set _) = ⊤) :
    ∃ (j : (SheafOfModules.unit (U : Scheme).ringCatSheaf ⊞
      SheafOfModules.unit (U : Scheme).ringCatSheaf) ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj (IdealSheafDataModule.closedImmersionModule i))
      (hz : cubicClosedPointSerreLocalKoszulFirst U q f ≫ j = 0),
      (ShortComplex.mk (cubicClosedPointSerreLocalKoszulFirst U q f) j hz).ShortExact ∧
      j ≫ (Scheme.Modules.restrictFunctor U.ι).map
          (IdealSheafDataModule.closedImmersionModuleToUnit i) =
        (cubicClosedPointSerreLocalKoszulPairUnitIso U).inv ≫
          (Scheme.Modules.restrictFunctor U.ι).map
            (sectionRepresenterKoszulLast X.ringCatSheaf U q f) ≫
          (Scheme.Modules.restrictFunctor U.ι).map
            (cubicClosedPointSerreLocalKoszulRepresenterUnitMap U) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  letI : F.Additive := { map_add := by intro A B f g; ext V m; rfl }
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  letI : PreservesFiniteLimits F := restrictFunctor_preservesFiniteLimits U.ι
  letI : PreservesFiniteColimits F := by dsimp [F]; infer_instance
  let B₀ := cubicClosedPointSerreLocalKoszulUnitSequence i
  let B := B₀.map F
  have hB : B.ShortExact := ShortComplex.shortExact_map_restrictFunctor U.ι B₀
    (cubicClosedPointSerreLocalKoszulUnitSequence_shortExact i)
  let a := cubicClosedPointSerreLocalKoszulRepresenterUnitMap U
  letI : IsIso (F.map a) := cubicClosedPointSerreLocalKoszulRepresenterUnitMap_restrict_isIso U
  let e₀ : F.obj (show X.Modules from sectionRepresenter X.ringCatSheaf U) ≅ B.X₂ :=
    asIso (F.map a)
  let d₁ := F.map (sectionRepresenterKoszulLast X.ringCatSheaf U q f)
  let d₂ := F.map (sectionRepresenterKoszulFirst X.ringCatSheaf U q f)
  letI := schemeModuleStalkModule (show X.Modules from
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (i default)
  let hk := (closedFieldPoint_pushforwardStalkFromRingLinearMap_ker_eq_maximalIdeal
    i default).trans hmax.symm
  let qM := closedImmersionUnitTwistStalkQuotientIso i (i default)
    (X.presheaf.germ U (i default) hx q) (X.presheaf.germ U (i default) hx f) hk
  let A₀ := sectionRepresenterKoszulAugmentedShortComplex X.ringCatSheaf U q f
    (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃
    (fieldPointSectionRepresenterKoszulSection i (SheafOfModules.unit X.ringCatSheaf)
      V hV eV U hx q f qM)
    (sectionRepresenterPointKoszulTransportedSection_q_smul X U (i default) hx q f _
      (fieldPointPushforwardTwist_skyscraperIso_of_coversTop_iso_unit i
        (SheafOfModules.unit X.ringCatSheaf) V hV eV) qM)
    (sectionRepresenterPointKoszulTransportedSection_f_smul X U (i default) hx q f _
      (fieldPointPushforwardTwist_skyscraperIso_of_coversTop_iso_unit i
        (SheafOfModules.unit X.ringCatSheaf) V hV eV) qM)
  have hA₀ : A₀.Exact := fieldPointSectionRepresenterKoszul_augmented_exact
    i (SheafOfModules.unit X.ringCatSheaf) V hV eV U hx q f qM haway
  have haug : a ≫ B₀.g = A₀.g :=
    cubicClosedPointSerreLocalKoszulAugmentation_eq i V hV eV U hx q f hmax
  have h₁₀ : (d₁ ≫ e₀.hom) ≫ B.g = 0 := by
    change (F.map (sectionRepresenterKoszulLast X.ringCatSheaf U q f) ≫ F.map a) ≫
      F.map B₀.g = 0
    rw [Category.assoc, ← F.map_comp, haug, ← F.map_comp]
    change F.map (A₀.f ≫ A₀.g) = 0
    rw [A₀.zero, F.map_zero]
  have he₀ : (ShortComplex.mk (d₁ ≫ e₀.hom) B.g h₁₀).Exact := by
    let b : A₀.map F ≅ ShortComplex.mk (d₁ ≫ e₀.hom) B.g h₁₀ :=
      ShortComplex.isoMk (Iso.refl _) e₀ (Iso.refl _) (by
        change 𝟙 _ ≫ (d₁ ≫ e₀.hom) = d₁ ≫ e₀.hom
        simp) (by
        change F.map a ≫ F.map B₀.g = F.map A₀.g ≫ 𝟙 _
        rw [← F.map_comp, haug, Category.comp_id])
    exact ShortComplex.exact_of_iso b (hA₀.map F)
  have h₂₁ : d₂ ≫ d₁ = 0 := by
    rw [← F.map_comp, sectionRepresenterKoszul_comp_zero X.ringCatSheaf U q f
      (Commute.all q f), F.map_zero]
  have he₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact :=
    (sectionRepresenterKoszul_exact_of_regularPairAtPoint X U q f (i default) hx
      hqreg hfreg haway).map F
  letI : Mono (sectionRepresenterKoszulFirst X.ringCatSheaf U q f) :=
    sectionRepresenterKoszulFirst_mono_of_regularPairAtPoint X U q f (i default) hx
      hqreg hfreg haway
  letI : Mono d₂ := Functor.map_mono F _
  let S := cubicClosedPointSerreLocalKoszulKernelComplex B hB e₀ d₁ d₂ h₁₀ h₂₁
  have hS : S.ShortExact := cubicClosedPointSerreLocalKoszulKernelComplex_shortExact
    B hB e₀ d₁ d₂ h₁₀ h₂₁ he₀ he₁
  let eP := cubicClosedPointSerreLocalKoszulRepresenterUnitIso U
  let eQ := cubicClosedPointSerreLocalKoszulPairUnitIso U
  let j := eQ.inv ≫ S.g
  have hz : cubicClosedPointSerreLocalKoszulFirst U q f ≫ j = 0 := by
    change (eP.inv ≫ S.f ≫ eQ.hom) ≫ (eQ.inv ≫ S.g) = 0
    simp only [Category.assoc, eQ.hom_inv_id_assoc]
    exact (congrArg (fun k => eP.inv ≫ k) S.zero).trans comp_zero
  let A := ShortComplex.mk (cubicClosedPointSerreLocalKoszulFirst U q f) j hz
  let b : S ≅ A := ShortComplex.isoMk eP eQ (Iso.refl _) (by
    change eP.hom ≫ (eP.inv ≫ S.f ≫ eQ.hom) = S.f ≫ eQ.hom
    simp) (by
    change eQ.hom ≫ (eQ.inv ≫ S.g) = S.g ≫ 𝟙 _
    simp)
  refine ⟨j, hz, ShortComplex.shortExact_of_iso b hS, ?_⟩
  change (eQ.inv ≫ S.g) ≫ B.f = eQ.inv ≫ d₁ ≫ F.map a
  rw [Category.assoc]
  change eQ.inv ≫ cubicClosedPointSerreLocalKoszulToKernel B hB e₀ d₁ h₁₀ ≫ B.f = _
  rw [cubicClosedPointSerreLocalKoszulToKernel_f]
  rfl

end PfaffianDescent
