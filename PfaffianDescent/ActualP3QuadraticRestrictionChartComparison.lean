import PfaffianDescent.ActualP3AugmentationChartKernel
import PfaffianDescent.ActualP3IdealHomogeneousRestrictionKernel
import PfaffianDescent.ActualP3QuadraticChartMembership

/- SOURCE ONLY / UNVERIFIED. Universal actual closed-Z quadratic dictionary.
Every comparison is derived internally from actual chart trivializations,
tensor naturality, the actual original i.app and the actual standard cover.
No comparison certificate, finiteness, reducedness, perfectness or global
support-avoiding linear form is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

lemma p3ActualHomogeneousGlobalSectionLinearMap_apply
    {K : Type u} [Field K] (m : ℕ)
    (p : homogeneousSubmodule (Fin 4) K m) :
    p3HomogeneousGlobalSectionLinearMap K m p =
      (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) m).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (homogeneousSubmodule (Fin 4) K) m p) := by
  let T := positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) m
  change T.unitHomEquiv.symm
    ((schemeModuleSectionsEquivTop T).symm
      (schemeModuleSectionsEquivTop T
        (positiveGlobalSectionOfHomogeneous (homogeneousSubmodule (Fin 4) K) m p))) = _
  rw [(schemeModuleSectionsEquivTop T).symm_apply_apply]

/-- Actual restriction on ONE standard chart is zero exactly when the SAME
original i.app kills the literal normalized homogeneous fraction. -/
theorem p3ActualHomogeneousRestriction_standard_chart_zero_iff
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i]
    (m : ℕ) (hm : 0 < m) (p : homogeneousSubmodule (Fin 4) K m) (j : Fin 4) :
    (Scheme.Modules.restrictFunctor (p3StandardOpen (K := K) j).ι).map
      (p3ClosedImmersionHomogeneousRestrictionLinearMap i m p) = 0 ↔
      i.app (p3StandardOpen (K := K) j)
        ((Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)).hom
          (ambientChartEvaluation j (p : MvPolynomial (Fin 4) K))) = 0 := by
  let U := p3StandardOpen (K := K) j
  let T := positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) m
  let R := Scheme.Modules.restrictFunctor U.ι
  let s : schemeModuleUnit (Proj (homogeneousSubmodule (Fin 4) K)) ⟶ T :=
    p3HomogeneousGlobalSectionLinearMap K m p
  let canonical := p3PositiveTwistStandardOpenIsoUnit K j m hm
  let eT := overFunctorIsoUnit_of_restrictIsoUnit U canonical
  let u := Scheme.Modules.restrictUnitIso U.ι
  let aug := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let c := u.inv ≫ R.map s ≫ canonical.hom
  have hlocal := actualPositiveRestriction_local_zero_iff_canonical_coordinate
    i U T eT canonical s
  change R.map (s ≫ actualPositiveClosedImmersionRestriction i T) = 0 ↔ _
  rw [hlocal]
  have hpre : ((R.map s ≫ canonical.hom ≫ u.inv) ≫ R.map aug = 0) ↔
      (c ≫ u.inv) ≫ R.map aug = 0 := by
    constructor
    · intro h
      have hh := congrArg (fun f => u.inv ≫ f) h
      simpa only [c, Category.assoc, comp_zero] using hh
    · intro h
      apply (cancel_epi u.inv).mp
      simpa only [c, Category.assoc, comp_zero] using h
  rw [hpre, p3ActualRestrictedAugmentation_zero_iff_value i U c]
  have hc := p3ActualHomogeneousUnitEndomorphismCoefficient K j m hm p
  rw [← p3ActualHomogeneousGlobalSectionLinearMap_apply m p] at hc
  change BundleSectionZeroLocus.unitEndomorphismValue c = _ at hc
  rw [hc, Iso.inv_hom_id_apply]

/-- The exact previously missing universal FOUR-chart restriction theorem.
It applies to every actual closed immersion into P3, including nonreduced Z. -/
theorem p3ActualQuadraticRestriction_zero_iff_four_chart_restrictions
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i]
    (p : homogeneousSubmodule (Fin 4) K 2) :
    p3ClosedImmersionHomogeneousRestrictionLinearMap i 2 p = 0 ↔
      ∀ j : Fin 4,
        i.app (intrinsicQuadraticAmbientOpen (K := K) j).1
          ((Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)).hom
            (ambientChartEvaluation j (p : MvPolynomial (Fin 4) K))) = 0 := by
  rw [p3ActualUnitSourceMorphism_zero_iff_standard_restrictions]
  exact forall_congr' fun j =>
    p3ActualHomogeneousRestriction_standard_chart_zero_iff i 2 (by decide) p j

/-- The actual polynomial restriction kernel, now internally identified with
the actual original embedding's intrinsic FULL quadratic system. -/
def p3ActualQuadraticRestrictionKernelIntrinsicEquiv
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i] :
    (p3ClosedImmersionHomogeneousRestrictionLinearMap i 2).ker ≃ₗ[K]
      intrinsicFullQuadraticSystem i := by
  let f : (p3ClosedImmersionHomogeneousRestrictionLinearMap i 2).ker →ₗ[K]
      intrinsicFullQuadraticSystem i :=
    { toFun p := ⟨p.val.val,
        (mem_intrinsicFullQuadraticSystem_iff_chart_restrictions_zero i p.val.val).mpr
          ⟨p.val.property,
            (p3ActualQuadraticRestriction_zero_iff_four_chart_restrictions i p.val).mp
              p.property⟩⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : intrinsicFullQuadraticSystem i => z.val) hpq
  · intro p
    let q : homogeneousSubmodule (Fin 4) K 2 := ⟨p.val, p.property.1⟩
    have hz : p3ClosedImmersionHomogeneousRestrictionLinearMap i 2 q = 0 :=
      (p3ActualQuadraticRestriction_zero_iff_four_chart_restrictions i q).mpr
        ((mem_intrinsicFullQuadraticSystem_iff_chart_restrictions_zero i p.val).mp
          p.property).2
    exact ⟨⟨q, hz⟩, Subtype.ext rfl⟩

/-- Literal H0(I_Z(2)) equals the intrinsic FULL quadratic submodule for the
SAME arbitrary original closed Z and embedding. Both directions and actual
ambient global sections are proved; no external dictionary is a premise. -/
def p3ActualIdealQuadraticIntrinsicLinearEquiv
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i] :
    SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2)) ≃ₗ[K]
      intrinsicFullQuadraticSystem i :=
  (p3ClosedImmersionIdealHomogeneousKernelEquiv i 2 (by decide)).trans
    (p3ActualQuadraticRestrictionKernelIntrinsicEquiv i)

/-- Actual sheaf-global-section dimension agrees with the exact intrinsic
quadratic dimension, without a finite/reduced/coefficient-chart hypothesis. -/
theorem p3ActualIdealQuadratic_finrank_eq_intrinsic
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i] :
    Module.finrank K (SchemeModuleGlobalSectionsOver
      (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) =
      Module.finrank K (intrinsicFullQuadraticSystem i) :=
  (p3ActualIdealQuadraticIntrinsicLinearEquiv i).finrank_eq

end PfaffianDescent
