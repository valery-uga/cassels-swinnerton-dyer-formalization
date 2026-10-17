import PfaffianDescent.CorayGenericNormalizationQuotientAffineSections
import PfaffianDescent.CorayFractionFieldFiniteDefect
import PfaffianDescent.CorayProjectiveIntersectionChartDimension
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-! Actual original-ground global section finiteness on the integral curve branch.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The project's original open-section ground action is exactly the action
of the ACTUAL structure morphism on the ORIGINAL open. -/
theorem schemeOpenBaseRingHom_eq_appLE
    {K : Type u} [Field K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) :
    schemeOpenBaseRingHom pi U =
      (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := by
  ext c
  rfl

/-- Actual module sections over an actual empty open are zero, proved from
the actual sheaf condition using the empty cover. -/
theorem schemeModuleOpenSections_subsingleton_of_not_nonempty
    {K : Type u} [Field K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (U : X.Opens)
    (hU : ¬ Nonempty U) : Subsingleton (SchemeModuleOpenSectionsOver pi M U) := by
  have hbot : U = ⊥ := by
    apply Opens.ext
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hU ⟨⟨x, hx⟩⟩
  refine ⟨fun x y => ?_⟩
  apply schemeModuleSections_ext M U (fun _ : Empty => ⊥)
    (fun i => nomatch i) (by rw [hbot]; simp) x y
  intro i
  exact nomatch i

/-- Actual affine quotient-SHEAF sections are finite over the ORIGINAL K.
Actual finite normalization, fraction-field transport and denominator torsion
are constructed internally; dimension ≤1 is the ordinary affine-curve bound. -/
theorem genericNormalizationQuotientSheaf_affineSections_finite_over_ground
    {K : Type u} [Field K] [CharZero K]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [Ring.DimensionLEOne Γ(X, U)] :
    Module.Finite K
      (SchemeModuleOpenSectionsOver pi (genericNormalizationQuotientSheaf X) U) := by
  let A := Γ(X, U)
  let F := X.functionField
  let beta : K →+* A :=
    (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  letI : Algebra K A := beta.toAlgebra
  have hbeta : beta.FiniteType := RingHom.FiniteType.comp
    (pi.finiteType_appLE (isAffineOpen_top _) hU (by simp))
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  letI : Algebra.FiniteType K A := hbeta
  letI : IsFractionRing A F := functionField_isFractionRing_of_isAffineOpen X U hU
  letI : Module.Finite A (integralClosure A (FractionRing A)) :=
    finiteNormalization_of_finiteType_charZero K A
  letI : Module.Finite A (integralClosure A F) :=
    Module.Finite.equiv (FractionRing.algEquiv (A := A) F).mapIntegralClosure.toLinearEquiv
  letI : Module.Finite A (localNormalizationDefect A F) := inferInstance
  let D := (ModuleCat.restrictScalars beta).obj (ModuleCat.of A (localNormalizationDefect A F))
  letI : Module.Finite A D :=
    (inferInstance : Module.Finite A (localNormalizationDefect A F))
  letI : IsScalarTower K A D := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : Module.Finite K D := finiteTorsion_finite_over_ground K A D
    (localNormalizationDefect_isTorsion A F)
  let e := genericNormalizationQuotientSheaf_groundAffineSectionsIso K X pi U hU
  have hfinite : Module.Finite K
      ((ModuleCat.restrictScalars beta).obj
        ((schemeOpenModuleFunctor X U).obj (genericNormalizationQuotientSheaf X))) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  exact hfinite

/-- Actual original-ground global sections inject into actual sections on a
finite cover. This ordinary sheaf lemma is used below with chart finiteness
DERIVED from the actual normalization quotient, not supplied to that endpoint. -/
theorem schemeModule_globalSections_finite_of_finite_open_cover
    {K : Type u} [Field K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    {ι : Type u} [Finite ι] (V : ι → X.Opens) (hcover : ⊤ ≤ ⨆ i, V i)
    (hfinite : ∀ i, Module.Finite K (SchemeModuleOpenSectionsOver pi M (V i))) :
    Module.Finite K (SchemeModuleGlobalSectionsOver pi M) := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI (i : ι) : Module.Finite K (SchemeModuleOpenSectionsOver pi M (V i)) := hfinite i
  let e := schemeModuleOpenSectionsLinearEquivCoverEqLocus M ⊤ V
    (fun _ => le_top) hcover pi
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi M ⊤) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  let eTop := schemeModuleGlobalSectionsLinearEquivOpenTop pi M
  exact FiniteDimensional.of_injective eTop.toLinearMap eTop.injective

/-- ACTUAL canonical GLOBAL normalization quotient SHEAF has finite ORIGINAL
K-dimensional global sections on the explicit integral selected projective
curve branch. The finite coordinate cover, every chart's dimension and every
chart's quotient-section finiteness are DERIVED from literal curve equations. -/
theorem projectiveIntersection_genericNormalizationQuotient_globalSections_finite
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    Module.Finite K
      (SchemeModuleGlobalSectionsOver (toBase (projectiveIntersectionIdeal p q hp hq))
        (genericNormalizationQuotientSheaf (scheme (projectiveIntersectionIdeal p q hp hq)))) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  let Q := genericNormalizationQuotientSheaf X
  let V : Fin 4 → X.Opens := fun j => (chartι I j).opensRange
  have hcover : ⊤ ≤ ⨆ j, V j := by
    intro x hx
    obtain ⟨j, y, hy⟩ := exists_coordinate_chart I x
    apply Opens.mem_iSup.mpr
    exact ⟨j, y, hy⟩
  have hcoverUp : ⊤ ≤ ⨆ j : ULift.{u} (Fin 4), V j.down := by
    intro x hx
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hcover hx)
    exact Opens.mem_iSup.mpr ⟨⟨j⟩, hj⟩
  apply schemeModule_globalSections_finite_of_finite_open_cover pi Q
    (fun j : ULift.{u} (Fin 4) => V j.down) hcoverUp
  intro jUp
  let j := jUp.down
  by_cases hnonempty : Nonempty (V j)
  · letI : Nonempty (V j) := hnonempty
    have hV : IsAffineOpen (V j) := isAffineOpen_opensRange (chartι I j)
    let e : Γ(X, V j) ≃+* ChartRing I j :=
      ((IsOpenImmersion.ΓIsoTop (chartι I j)).symm ≪≫
        Scheme.ΓSpecIso (CommRingCat.of (ChartRing I j))).commRingCatIsoToRingEquiv
    have hdim : ringKrullDim Γ(X, V j) ≤ 1 := by
      rw [ringKrullDim_eq_of_ringEquiv e]
      exact projectiveIntersection_chart_ringKrullDim_le_one p q hp hp0 n hq hnot j
    letI : Ring.KrullDimLE 1 Γ(X, V j) := Ring.krullDimLE_iff.mpr hdim
    letI : Ring.DimensionLEOne Γ(X, V j) :=
      ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
    exact genericNormalizationQuotientSheaf_affineSections_finite_over_ground X pi (V j) hV
  · letI := schemeModuleOpenSections_subsingleton_of_not_nonempty pi Q (V j) hnonempty
    infer_instance

end PfaffianDescent.Coray
