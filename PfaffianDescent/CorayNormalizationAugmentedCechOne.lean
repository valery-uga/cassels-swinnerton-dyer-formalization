import PfaffianDescent.CorayClosedSupportAugmentedCechOne
import PfaffianDescent.CorayGlobalSectionsChosenAffineDefect

/-! SOURCE ONLY / UNVERIFIED. Primitive Coray caller for actual degree-one
Čech exactness of the canonical GLOBAL normalization quotient. Finite and
closed actual support and the distinguished affine U are derived internally.
This does not assert Ext-H¹ vanishing, genus subtraction, or Riemann--Roch.
-/

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveIntersection_genericNormalizationQuotient_exists_affineOpen_augmentedCech_exact_one
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let pi := toBase I
    let Q := genericNormalizationQuotientSheaf X
    ∃ U : X.affineOpens, Nonempty U.1 ∧ schemeModuleStalkSupport Q ⊆ U.1 ∧ x ∈ U.1 ∧
      ∀ (ι : Type u) [Finite ι] (V : ι → X.affineOpens),
        (⊤ ≤ ⨆ i, (V i).1) →
        (⊤ ≤ ⨆ a, supportAugmentedOpenFamily U.1 (fun i => (V i).1) a) ∧
        Function.Exact
          (schemeModuleCechZeroDifferential pi Q
            (supportAugmentedOpenFamily U.1 (fun i => (V i).1)))
          (schemeModuleCechOneDifferential pi Q
            (supportAugmentedOpenFamily U.1 (fun i => (V i).1))) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
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
    schemeModule_augmentedCech_exact_one_of_closedSupport_subset pi Q U.1
      (fun i => (V i).1) (schemeModuleStalkSupport Q) hclosed (Set.Subset.rfl) hsU⟩

end PfaffianDescent.Coray
