import PfaffianDescent.CorayClosedSupportRawCechExact
import PfaffianDescent.CorayGlobalSectionsChosenAffineDefect

/-! SOURCE ONLY / UNVERIFIED. The primitive Coray curve supplies the actual
GLOBAL normalization quotient, its closed support, and an affine open
containing that support. The degree-one exactness conclusion concerns the
existing actual categorical section-representer Čech Hom complex.
Neither support nor a comparison/acyclicity certificate is an extra premise.
This does not assert Ext-H¹ vanishing, genus subtraction, or Riemann--Roch.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveIntersection_genericNormalizationQuotient_exists_affineOpen_augmentedCechHom_exact_one
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let Q := genericNormalizationQuotientSheaf X
    ∃ U : X.affineOpens, Nonempty U.1 ∧ schemeModuleStalkSupport Q ⊆ U.1 ∧ x ∈ U.1 ∧
      ∀ (ι : Type u) [Finite ι] (V : ι → X.affineOpens),
        (⊤ ≤ ⨆ i, (V i).1) →
        (⊤ ≤ ⨆ a, supportAugmentedOpenFamily U.1 (fun i => (V i).1) a) ∧
        Function.Exact
          (fun h : (sectionRepresenterCechChain X.ringCatSheaf
              (supportAugmentedOpenFamily U.1 (fun i => (V i).1))).X 0 ⟶ Q =>
            (sectionRepresenterCechChain X.ringCatSheaf
              (supportAugmentedOpenFamily U.1 (fun i => (V i).1))).d 1 0 ≫ h)
          (fun h : (sectionRepresenterCechChain X.ringCatSheaf
              (supportAugmentedOpenFamily U.1 (fun i => (V i).1))).X 1 ⟶ Q =>
            (sectionRepresenterCechChain X.ringCatSheaf
              (supportAugmentedOpenFamily U.1 (fun i => (V i).1))).d 2 1 ≫ h) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let Q := genericNormalizationQuotientSheaf X
  obtain ⟨U, hnonempty, hsU, hxU⟩ :=
    projectiveIntersection_genericNormalizationQuotient_exists_affineOpen
      p q hp hp0 n hq hnot x
  have hclosed : IsClosed (schemeModuleStalkSupport Q) :=
    projectiveIntersection_genericNormalizationQuotient_stalkSupport_isClosed
      p q hp hp0 n hq hnot
  refine ⟨U, hnonempty, hsU, hxU, ?_⟩
  intro ι _ V hV
  exact ⟨supportAugmentedOpenFamily_covers U.1 (fun i => (V i).1) hV,
    schemeModule_augmentedCechHom_exact_one_of_closedSupport_subset (toBase I) Q U.1
      (fun i => (V i).1) (schemeModuleStalkSupport Q) hclosed (Set.Subset.rfl) hsU⟩

/-- The same internally chosen support-containing affine open yields
degree-one exactness of the existing additive categorical Čech complex of
the canonical normalization quotient, with no comparison certificate. -/
theorem projectiveIntersection_genericNormalizationQuotient_exists_affineOpen_augmentedRawCech_exact_one
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let Q := genericNormalizationQuotientSheaf X
    ∃ U : X.affineOpens, Nonempty U.1 ∧ schemeModuleStalkSupport Q ⊆ U.1 ∧ x ∈ U.1 ∧
      ∀ (ι : Type u) [Finite ι] (V : ι → X.affineOpens),
        (⊤ ≤ ⨆ i, (V i).1) →
        (⊤ ≤ ⨆ a, supportAugmentedOpenFamily U.1 (fun i => (V i).1) a) ∧
        Function.Exact
          ((schemeModuleCategoricalCechComplex Q
            (supportAugmentedOpenFamily U.1 (fun i => (V i).1))).d 0 1)
          ((schemeModuleCategoricalCechComplex Q
            (supportAugmentedOpenFamily U.1 (fun i => (V i).1))).d 1 2) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let Q := genericNormalizationQuotientSheaf X
  obtain ⟨U, hnonempty, hsU, hxU, hHom⟩ :=
    projectiveIntersection_genericNormalizationQuotient_exists_affineOpen_augmentedCechHom_exact_one
      p q hp hp0 n hq hnot x
  have hclosed : IsClosed (schemeModuleStalkSupport Q) :=
    projectiveIntersection_genericNormalizationQuotient_stalkSupport_isClosed
      p q hp hp0 n hq hnot
  refine ⟨U, hnonempty, hsU, hxU, ?_⟩
  intro ι _ V hV
  exact ⟨(hHom ι V hV).1,
    schemeModule_augmentedRawCech_exact_one_of_closedSupport_subset (toBase I) Q U.1
      (fun i => (V i).1) (schemeModuleStalkSupport Q) hclosed (Set.Subset.rfl) hsU⟩

end PfaffianDescent.Coray
