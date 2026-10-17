import PfaffianDescent.CorayTwoAffineCurveCover
import PfaffianDescent.AffineMorphismUnitQuasicoherent
import PfaffianDescent.CorayProjectiveIntersectionCohomologyOneBound
import PfaffianDescent.ClosedImmersionCohomologyOneLinearEquiv
import PfaffianDescent.CorayGenericNormalizationLowDegreeLinearExact

/-! Source-only: actual unit restriction to a SAME closed projective
component is H1-surjective, and intrinsic original-K H1 is bounded by G_n.
The literal p/q curve may be reducible and nonreduced. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
universe u v w
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nativeExtOne_postcomp_surjective_of_extTwo_subsingleton
    {A : Type v} [Category.{w} A] [Abelian A]
    (originalExt : HasExt.{u} A) (O : A) (S : ShortComplex A) (hS : S.ShortExact) :
    letI : HasExt.{u} A := originalExt
    Subsingleton (Ext.{u} O S.X₁ 2) →
      Function.Surjective ((Ext.mk₀ S.g).postcomp O (add_zero 1)) := by
  letI : HasExt.{u} A := originalExt
  change Subsingleton (Ext.{u} O S.X₁ 2) →
    Function.Surjective ((Ext.mk₀ S.g).postcomp O (add_zero 1))
  intro hvan
  letI : Subsingleton (Ext.{u} O S.X₁ 2) := hvan
  intro z
  have hz : z.comp hS.extClass (show 1 + 1 = 2 by rfl) = 0 := Subsingleton.elim _ _
  obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₃ O hS z (show 1 + 1 = 2 by rfl) hz
  exact ⟨t, ht⟩

/-- Actual component structure restriction is H1-surjective: the OWN native
kernel is QC and its H2 vanishes on the derived two-affine cover of (p,q).
No integral/GI, reducedness, kernel-QC, cover or vanishing input occurs. -/
theorem projectiveIntersection_closedComponent_unit_cohomologyOneMap_surjective
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    [HasExt.{u} (scheme (projectiveIntersectionIdeal p q hp hq)).Modules] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let i := schemeQuotientMap I C hIC
    Function.Surjective (schemeModuleCohomologyMap X
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) 1) := by
  rename_i originalExt
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : HasExt.{u} X.Modules := originalExt
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := originalExt
  let i := schemeQuotientMap I C hIC
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion I C hIC
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let a := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let S := ShortComplex.kernelSequence a
  have hS : S.ShortExact :=
    IdealSheafDataModule.closedImmersionKernelExactSequence_shortExact i
  letI : (kernel a).IsQuasicoherent :=
    (closedImmersionUnitQuotient_and_kernel_isQuasicoherent i).2
  have hvan : Subsingleton (schemeModuleCohomology X (kernel a) 2) :=
    projectiveIntersection_quasicoherent_cohomology_subsingleton_ge_two
      p q hp hp0 n hq hnot (kernel a) 2 (by decide)
  have hvanNative : Subsingleton (Ext.{u} (C := X.Modules) O S.X₁ 2) := by
    change Subsingleton (schemeModuleCohomology X (kernel a) 2)
    exact hvan
  change Function.Surjective (schemeModuleCohomologyMap X a 1)
  change Function.Surjective ((Ext.mk₀ S.g).postcomp O (add_zero 1))
  exact nativeExtOne_postcomp_surjective_of_extTwo_subsingleton originalExt O S hS hvanNative

/-- Intrinsic original-K cohomology of ANY actual homogeneous closed
subscheme of the selected p/q curve is finite and has rank at most G_n.
In particular this is an actual genus estimate for each SAME integral
minimal component through P, without assuming geometric integrality. -/
theorem projectiveIntersection_closedComponent_unit_cohomology_one_finite_finrank_le
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal) :
    letI : EnoughInjectives (scheme C).Modules := sheafOfModules_enoughInjectives (scheme C).ringCatSheaf
    letI : HasExt.{u} (scheme C).Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (scheme C).Modules
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
    Module.Finite K (schemeModuleCohomology (scheme C)
      (SheafOfModules.unit (scheme C).ringCatSheaf) 1) ∧
      Module.finrank K (schemeModuleCohomology (scheme C)
        (SheafOfModules.unit (scheme C).ringCatSheaf) 1) ≤ 1 + 3 * n * (n - 1) / 2 := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let Y := scheme C
  let pi := toBase I
  let i := schemeQuotientMap I C hIC
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion I C hIC
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives Y.Modules := sheafOfModules_enoughInjectives Y.ringCatSheaf
  letI : HasExt.{u} Y.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} Y.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let M : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let P := (Scheme.Modules.pushforward i).obj M
  let a := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let T := schemeModuleCohomologyLinearMapOver pi a 1
  have hT : Function.Surjective T :=
    projectiveIntersection_closedComponent_unit_cohomologyOneMap_surjective
      p q hp hp0 n hq hnot C hIC
  letI : Module.Finite K (schemeModuleCohomology X O 1) :=
    projectiveIntersection_unit_cohomology_one_finite_native p q hp hp0 n hq hnot
  letI : Module.Finite K (schemeModuleCohomology X P 1) := Module.Finite.of_surjective T hT
  have hP : Module.finrank K (schemeModuleCohomology X P 1) ≤
      1 + 3 * n * (n - 1) / 2 :=
    (LinearMap.finrank_le_finrank_of_surjective hT).trans
      (projectiveIntersection_unit_cohomology_one_finrank_le_native p q hp hp0 n hn hq hnot)
  let result : (Y ⟶ Spec (CommRingCat.of K)) → Prop := fun rho =>
    letI : Linear K Y.Modules := schemeModulesLinearOver rho
    Module.Finite K (schemeModuleCohomology Y M 1) ∧
      Module.finrank K (schemeModuleCohomology Y M 1) ≤ 1 + 3 * n * (n - 1) / 2
  have hresult : result (i ≫ pi) := by
    letI : Linear K Y.Modules := schemeModulesLinearOver (i ≫ pi)
    let E := closedImmersion_cohomologyOneLinearEquiv pi i M
    refine ⟨Module.Finite.of_injective E.toLinearMap E.injective, ?_⟩
    rw [E.finrank_eq]
    exact hP
  change result (toBase C)
  exact Eq.mp (congrArg result (schemeQuotientMap_toBase I C hIC)) hresult

end PfaffianDescent.Coray
