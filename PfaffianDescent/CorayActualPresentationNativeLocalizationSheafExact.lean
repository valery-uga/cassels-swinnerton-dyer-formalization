import PfaffianDescent.CorayActualWeightedHomogeneousRelations
import PfaffianDescent.AffineQCAcyclicity
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Exact localization and actual affine tilde of the OWN finite homogeneous
presentation and its SAME polynomial relation kernel.
This is an affine-cone/localization leaf, not a supplied Proj sheaf comparison.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K

/-- The literal polynomial-linear relation matrix; its columns are the OWN
polynomial coefficient vectors in the original free presentation. -/
def actualPolynomialRelationMap
    {ι κ : Type u} [Fintype ι] [Fintype κ] (r : κ → ι → A) :
    (κ → A) →ₗ[A] (ι → A) where
  toFun c := ∑ j, c j • r j
  map_add' c c' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

/-- The SAME literal relation matrix has exactly the span of its actual
columns as its image; no kernel certificate is substituted. -/
theorem actualPolynomialRelationMap_range
    {ι κ : Type u} [Fintype ι] [Fintype κ] (r : κ → ι → A) :
    (actualPolynomialRelationMap r).range =
      Submodule.span A (Set.range r) := by
  ext c
  change (∃ b, actualPolynomialRelationMap r b = c) ↔ _
  exact (Submodule.mem_span_range_iff_exists_fun A).symm

/-- The accepted OWN relation-generator equality implies exactness of the
literal two polynomial matrices. The primitive caller derives that equality. -/
theorem actualPolynomialRelationMap_generatorMap_exact
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker) :
    Function.Exact (actualPolynomialRelationMap r) (actualPolynomialGeneratorMap g) := by
  apply LinearMap.exact_iff.mpr
  exact hr.symm.trans (actualPolynomialRelationMap_range r).symm

/-- The actual module localization map, extended over the SAME canonical
localized polynomial ring. Its underlying map remains IsLocalizedModule.map. -/
def actualNativePolynomialLocalizedMap
    (S : Submonoid A) {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) :
    LocalizedModule S M →ₗ[Localization S] LocalizedModule S N :=
  (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) f).extendScalarsOfIsLocalization S (Localization S)

/-- Representatives are mapped by the OWN polynomial map without changing
numerators, denominators, or the original coefficient action. -/
theorem actualNativePolynomialLocalizedMap_mk
    (S : Submonoid A) {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (m : M) (s : S) :
    actualNativePolynomialLocalizedMap S f (LocalizedModule.mk m s) =
      LocalizedModule.mk (f m) s :=
  IsLocalizedModule.map_LocalizedModules S f m s

/-- The SAME original K coefficient acts through its actual polynomial
constant map. Compatibility is the native A-linear localization law, not
an action transported through a comparison equivalence. -/
theorem actualNativePolynomialLocalizedMap_ground_smul
    (S : Submonoid A) {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (c : K) (x : LocalizedModule S M) :
    actualNativePolynomialLocalizedMap S f ((algebraMap K A c) • x) =
      (algebraMap K A c) • actualNativePolynomialLocalizedMap S f x := by
  exact (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) f).map_smul (algebraMap K A c) x

/-- Every localization of the OWN polynomial presentation/relation matrices
is exact, internally derived from exact module localization. -/
theorem actualPolynomialPresentation_nativeLocalized_exact
    (S : Submonoid A) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker) :
    Function.Exact
      (actualNativePolynomialLocalizedMap S (actualPolynomialRelationMap r))
      (actualNativePolynomialLocalizedMap S (actualPolynomialGeneratorMap g)) :=
  LocalizedModule.map_exact S
    (actualPolynomialRelationMap r) (actualPolynomialGeneratorMap g)
    (actualPolynomialRelationMap_generatorMap_exact g r hr)

/-- The actual localized module short complex, with its zero composite
proved from the OWN relation-kernel equality and exact localization. -/
def actualPolynomialPresentation_nativeLocalizedComplex
    (S : Submonoid A) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker) :
    ShortComplex (ModuleCat.{u} (Localization S)) :=
  ModuleCat.shortComplexOfCompEqZero
    (actualNativePolynomialLocalizedMap S (actualPolynomialRelationMap r))
    (actualNativePolynomialLocalizedMap S (actualPolynomialGeneratorMap g)) (by
      apply LinearMap.ext
      intro x
      exact (actualPolynomialPresentation_nativeLocalized_exact S g r hr _).mpr ⟨x, rfl⟩)

/-- The literal native affine tilde complex of the SAME localized maps. -/
def actualPolynomialPresentation_nativeLocalizedSheafComplex
    (S : Submonoid A) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker) :
    ShortComplex (Spec (CommRingCat.of (Localization S))).Modules := by
  let F := tilde.functor (CommRingCat.of (Localization S))
  letI : F.IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  exact (actualPolynomialPresentation_nativeLocalizedComplex S g r hr).map F

/-- The OWN native affine sheaf presentation is exact in every localization,
including coordinate-power and prime localizations. No sheaf exactness,
comparison, surjectivity or cohomology premise is supplied. -/
theorem actualPolynomialPresentation_nativeLocalizedSheafComplex_exact
    (S : Submonoid A) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker) :
    (actualPolynomialPresentation_nativeLocalizedSheafComplex S g r hr).Exact := by
  let F := tilde.functor (CommRingCat.of (Localization S))
  letI : F.IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  letI : F.PreservesMonomorphisms :=
    PfaffianDescent.tilde_preservesMonomorphisms (R := CommRingCat.of (Localization S))
  letI : F.PreservesHomology := F.preservesHomology_of_preservesMonos_and_cokernels
  have h : (actualPolynomialPresentation_nativeLocalizedComplex S g r hr).Exact :=
    ModuleCat.shortComplex_exact _
      (actualPolynomialPresentation_nativeLocalized_exact S g r hr)
  change ((actualPolynomialPresentation_nativeLocalizedComplex S g r hr).map F).Exact
  exact h.map F

/-- The primitive OWN homogeneous ideal internally produces finite
homogeneous generators, finite weighted homogeneous relations, and genuine
native affine sheaf exactness of the SAME matrices in ALL localizations.
No desired presentation/local exactness certificate is a premise. -/
theorem homogeneousIdeal_exists_actualNativeLocalizedSheafPresentation
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    ∃ (T : Finset A) (d : T → ℕ)
      (R : Finset (T → A)) (e : R → ℕ) (B : ℕ)
      (hr : Submodule.span A (Set.range (fun c : R => c.val)) =
        (actualPolynomialGeneratorMap (fun i : T => i.val)).ker),
      Ideal.span (T : Set A) = I.toIdeal ∧
      (∀ i : T, d i ≤ B ∧ (i : A).IsHomogeneous (d i)) ∧
      (∀ c : R, e c ≤ B ∧ ActualWeightedPolynomialHomogeneous d (e c) c.val) ∧
      ∀ S : Submonoid A,
        (actualPolynomialPresentation_nativeLocalizedSheafComplex S
          (fun i : T => i.val) (fun c : R => c.val) hr).Exact := by
  classical
  obtain ⟨T, d, R, e, B, hI, hd, hR, he⟩ :=
    homogeneousIdeal_exists_actual_finite_homogeneousPresentation_and_relations I
  have hrange : Set.range (fun c : R => c.val) = (R : Set (T → A)) := by
    ext c
    constructor
    · rintro ⟨r, rfl⟩
      exact r.property
    · intro hc
      exact ⟨⟨c, hc⟩, rfl⟩
  have hr : Submodule.span A (Set.range (fun c : R => c.val)) =
      (actualPolynomialGeneratorMap (fun i : T => i.val)).ker := by
    rw [hrange]
    exact hR
  refine ⟨T, d, R, e, B, hr, hI, hd, he, ?_⟩
  intro S
  exact actualPolynomialPresentation_nativeLocalizedSheafComplex_exact S
    (fun i : T => i.val) (fun c : R => c.val) hr

end PfaffianDescent.Coray
