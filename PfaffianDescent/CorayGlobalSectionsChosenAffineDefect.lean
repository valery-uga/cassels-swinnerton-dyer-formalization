import PfaffianDescent.CorayGlobalNormalizationSupportClosed
import PfaffianDescent.CorayProjectiveGlobalNormalizationSupport
import PfaffianDescent.CorayClosedSupportSectionExtension
import AllCharacteristics.ProjectiveCommonAffineNeighborhood

/-! A genuine chosen affine model for ACTUAL global normalization-quotient
sections, preserving the ORIGINAL ground field and chosen projective point.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine finite-support module sheaf on an actual projective polynomial
quotient admits one actual affine open containing its support AND a chosen
actual point. The installed proved positive-degree homogeneous prime
avoidance constructs the affine neighborhood; it is not supplied. -/
theorem projectiveModule_exists_affineOpen_containing_support_and_point
    {K : Type u} [CommRing K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (M : (scheme I).Modules) (hs : (schemeModuleStalkSupport M).Finite)
    (x : scheme I) :
    ∃ U : (scheme I).affineOpens,
      Nonempty U.1 ∧ schemeModuleStalkSupport M ⊆ U.1 ∧ x ∈ U.1 := by
  classical
  let S : Set (scheme I) := insert x (schemeModuleStalkSupport M)
  have hS : S.Finite := hs.insert x
  obtain ⟨U, hU⟩ := AllCharacteristics.exists_affineOpen_containing_projective_finset
    (grading I) hS.toFinset
  have hx : x ∈ U.1 := hU x (hS.mem_toFinset.mpr (Set.mem_insert x _))
  refine ⟨U, ⟨⟨x, hx⟩⟩, ?_, hx⟩
  intro y hy
  exact hU y (hS.mem_toFinset.mpr (Set.mem_insert_of_mem x hy))

/-- For the literal integral selected projective intersection, the ACTUAL
normalization quotient's finite support and a chosen point lie in one ACTUAL
nonempty affine open. Finite support is proved internally from the literal
curve equations and actual normalization, with no support certificate. -/
theorem projectiveIntersection_genericNormalizationQuotient_exists_affineOpen
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :
    ∃ U : (scheme (projectiveIntersectionIdeal p q hp hq)).affineOpens,
      Nonempty U.1 ∧
      schemeModuleStalkSupport
        (genericNormalizationQuotientSheaf (scheme (projectiveIntersectionIdeal p q hp hq)))
          ⊆ U.1 ∧ x ∈ U.1 := by
  exact projectiveModule_exists_affineOpen_containing_support_and_point
    (projectiveIntersectionIdeal p q hp hq)
    (genericNormalizationQuotientSheaf (scheme (projectiveIntersectionIdeal p q hp hq)))
    (projectiveIntersection_genericNormalizationQuotient_stalkSupport_finite
      p q hp hp0 n hq hnot) x

/-- ACTUAL ORIGINAL-K global sections of the canonical normalization quotient
identify with the LITERAL normalization defect on one ACTUAL affine open
containing the chosen point and ALL actual support. Finite/closed support,
affine choice, extension by zero, sheaf-cokernel section comparison and scalar
compatibility are all derived. This is not a genus/RR certificate. -/
theorem projectiveIntersection_genericNormalizationQuotient_exists_globalSectionsEquiv_affineDefect
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :
    ∃ (U : (scheme (projectiveIntersectionIdeal p q hp hq)).affineOpens)
      (hU : Nonempty U.1),
      letI : Nonempty U.1 := hU
      x ∈ U.1 ∧ Nonempty
        (SchemeModuleGlobalSectionsOver (toBase (projectiveIntersectionIdeal p q hp hq))
          (genericNormalizationQuotientSheaf (scheme (projectiveIntersectionIdeal p q hp hq)))
          ≃ₗ[K]
          (ModuleCat.restrictScalars
            (((toBase (projectiveIntersectionIdeal p q hp hq)).appLE ⊤ U.1 (by simp)).hom.comp
              (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).obj
            (ModuleCat.of Γ(scheme (projectiveIntersectionIdeal p q hp hq), U.1)
              (localNormalizationDefect Γ(scheme (projectiveIntersectionIdeal p q hp hq), U.1)
                (scheme (projectiveIntersectionIdeal p q hp hq)).functionField))) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  let Q := genericNormalizationQuotientSheaf X
  obtain ⟨U, hnonempty, hsU, hxU⟩ :=
    projectiveIntersection_genericNormalizationQuotient_exists_affineOpen
      p q hp hp0 n hq hnot x
  letI : Nonempty U.1 := hnonempty
  have hclosed : IsClosed (schemeModuleStalkSupport Q) :=
    projectiveIntersection_genericNormalizationQuotient_stalkSupport_isClosed
      p q hp hp0 n hq hnot
  let eGlobal : SchemeModuleGlobalSectionsOver pi Q ≃ₗ[K]
      SchemeModuleOpenSectionsOver pi Q U.1 :=
    schemeModule_groundGlobalSectionsEquiv_of_closedSupport_subset
      pi Q U.1 (schemeModuleStalkSupport Q) hclosed (Set.Subset.rfl) hsU
  let beta : K →+* Γ(X, U.1) :=
    (pi.appLE ⊤ U.1 (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let D := (ModuleCat.restrictScalars beta).obj
    (ModuleCat.of Γ(X, U.1) (localNormalizationDefect Γ(X, U.1) X.functionField))
  let eAffine : SchemeModuleOpenSectionsOver pi Q U.1 ≃ₗ[K] D :=
    (genericNormalizationQuotientSheaf_groundAffineSectionsIso K X pi U.1 U.2).toLinearEquiv
  exact ⟨U, hnonempty, hxU, ⟨eGlobal.trans eAffine⟩⟩

end PfaffianDescent.Coray
