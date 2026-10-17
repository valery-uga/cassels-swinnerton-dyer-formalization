import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import PfaffianDescent.BundleSectionZeroLocus
import PfaffianDescent.ExtMapFixedSource
import PfaffianDescent.SheafModulePushforwardExact

/-!
# Cohomology of a scheme module

For an `O_X`-module sheaf `M`, global sections are represented by the unit
module `O_X`.  We therefore use `Ext^n_{O_X}(O_X,M)` as the derived-global-
sections model of sheaf cohomology.  The degree-zero comparison below checks
that this definition recovers the literal global sections of `M`.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Abelian

universe u v

/-- Cohomology of an `O_X`-module sheaf, modeled as the derived functors of
global sections through the representing object `O_X`. -/
abbrev schemeModuleCohomology (X : Scheme.{u})
    [HasExt.{u} X.Modules] (M : X.Modules) (n : ℕ) : Type u :=
  Ext.{u}
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) M n

/-- The map on scheme-module cohomology induced by a module morphism. -/
noncomputable def schemeModuleCohomologyMap (X : Scheme.{u})
    [HasExt.{u} X.Modules] {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    schemeModuleCohomology X M n →+ schemeModuleCohomology X N n :=
  (Ext.mk₀ f).postcomp
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (add_zero n)

/-- If the two adjacent cohomology groups of the middle term vanish, the
connecting map of a short exact sequence is bijective. -/
theorem extBoundary_bijective_of_middle_subsingleton
    {C : Type v} [Category C] [Abelian C] [HasExt.{u} C]
    (X : C) (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext X S.X₂ n)]
    [Subsingleton (Ext X S.X₂ (n + 1))] :
    Function.Bijective
      (hS.extClass.postcomp X (show n + 1 = n + 1 by rfl)) := by
  constructor
  · intro x y hxy
    have hzero : (x - y).comp hS.extClass
        (show n + 1 = n + 1 by rfl) = 0 := by
      change (hS.extClass.postcomp X (show n + 1 = n + 1 by rfl))
        (x - y) = 0
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃
      X hS (x - y) (show n + 1 = n + 1 by rfl) hzero
    rw [show z = 0 by exact Subsingleton.elim _ _, Ext.zero_comp] at hz
    exact sub_eq_zero.mp hz.symm
  · intro z
    have hzero : z.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 :=
      Subsingleton.elim _ _
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₁
      X hS z hzero (show n + 1 = n + 1 by rfl)
    exact ⟨x, hx⟩

/-- Additive equivalence supplied by the connecting map when the middle
term has vanishing cohomology in the two adjacent degrees. -/
noncomputable def extBoundaryAddEquivOfMiddleSubsingleton
    {C : Type v} [Category C] [Abelian C] [HasExt.{u} C]
    (X : C) (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext X S.X₂ n)]
    [Subsingleton (Ext X S.X₂ (n + 1))] :
    Ext X S.X₃ n ≃+ Ext X S.X₁ (n + 1) :=
  AddEquiv.ofBijective
    (hS.extClass.postcomp X (show n + 1 = n + 1 by rfl))
    (extBoundary_bijective_of_middle_subsingleton X S hS n)

/-- Degree-zero scheme-module cohomology is the type of global sections. -/
noncomputable def schemeModuleCohomologyZeroEquivSections
    (X : Scheme.{u}) [HasExt.{u} X.Modules] (M : X.Modules) :
    schemeModuleCohomology X M 0 ≃ M.sections :=
  Ext.homEquiv₀.trans M.unitHomEquiv

/-- Vanishing in degree zero is equivalent to uniqueness of global
sections. -/
theorem schemeModuleCohomology_zero_subsingleton_iff_sections
    (X : Scheme.{u}) [HasExt.{u} X.Modules] (M : X.Modules) :
    Subsingleton (schemeModuleCohomology X M 0) ↔
      Subsingleton M.sections := by
  exact Equiv.subsingleton_congr
    (schemeModuleCohomologyZeroEquivSections X M)

/-- A supplied vanishing theorem for scheme-module cohomology is exactly the
Ext vanishing required by the inverse-twist argument. -/
theorem ext_unit_subsingleton_of_schemeModuleCohomology
    (X : Scheme.{u}) [HasExt.{u} X.Modules] (M : X.Modules) (n : ℕ)
    [Subsingleton (schemeModuleCohomology X M n)] :
    Subsingleton (Ext.{u}
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) M n) := by
  infer_instance

/-- Scheme-module cohomology vanishing transports covariantly across an
isomorphism of coefficient modules. -/
theorem schemeModuleCohomology_subsingleton_of_iso
    (X : Scheme.{u}) [HasExt.{u} X.Modules]
    {M N : X.Modules} (e : M ≅ N) (n : ℕ)
    [Subsingleton (schemeModuleCohomology X M n)] :
    Subsingleton (schemeModuleCohomology X N n) :=
  ext_subsingleton_of_iso_right e n

/-- The useful four-term consequence of the covariant long exact cohomology
sequence.  For a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, surjectivity of
`Hⁿ(B) ⟶ Hⁿ(C)` and vanishing of `Hⁿ⁺¹(B)` imply vanishing of `Hⁿ⁺¹(A)`.

For `n = 0`, this is the standard reduction used to prove an `H¹` vanishing
from surjectivity on global sections and an ambient `H¹` vanishing. -/
theorem schemeModuleCohomology_succ_subsingleton_of_map_surjective
    (X : Scheme.{u}) [HasExt.{u} X.Modules]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ)
    (hsurj : Function.Surjective (schemeModuleCohomologyMap X S.g n))
    [Subsingleton (schemeModuleCohomology X S.X₂ (n + 1))] :
    Subsingleton (schemeModuleCohomology X S.X₁ (n + 1)) := by
  constructor
  intro x y
  suffices hzero : ∀ z : schemeModuleCohomology X S.X₁ (n + 1), z = 0 by
    exact (hzero x).trans (hzero y).symm
  intro z
  have hz : z.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨z₀, hz₀⟩ := Ext.covariant_sequence_exact₁
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) hS z hz
    (show n + 1 = n + 1 by rfl)
  obtain ⟨z₂, hz₂⟩ := hsurj z₀
  rw [← hz₀, ← hz₂]
  change (z₂.comp (Ext.mk₀ S.g) (add_zero n)).comp hS.extClass
    (show n + 1 = n + 1 by rfl) = 0
  rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- Degree-one specialization of
`schemeModuleCohomology_succ_subsingleton_of_map_surjective`. -/
theorem schemeModuleCohomology_one_subsingleton_of_zero_map_surjective
    (X : Scheme.{u}) [HasExt.{u} X.Modules]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hsurj : Function.Surjective (schemeModuleCohomologyMap X S.g 0))
    [Subsingleton (schemeModuleCohomology X S.X₂ 1)] :
    Subsingleton (schemeModuleCohomology X S.X₁ 1) := by
  exact schemeModuleCohomology_succ_subsingleton_of_map_surjective
    X S hS 0 hsurj

/-- The preceding degree-one vanishing criterion has the exact converse
needed for restriction sequences: if `H¹(A)` vanishes in
`0 → A → B → C → 0`, then global sections of `B` restrict surjectively to
global sections of `C`. -/
theorem schemeModuleCohomology_zero_map_surjective_of_one_subsingleton
    (X : Scheme.{u}) [HasExt.{u} X.Modules]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Subsingleton (schemeModuleCohomology X S.X₁ 1)] :
    Function.Surjective (schemeModuleCohomologyMap X S.g 0) := by
  intro z
  have hz : z.comp hS.extClass (show 1 = 1 by rfl) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨z₂, hz₂⟩ := Ext.covariant_sequence_exact₃
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) hS z
    (show 1 = 1 by rfl) hz
  refine ⟨z₂, ?_⟩
  change z₂.comp (Ext.mk₀ S.g) (add_zero 0) = z
  exact hz₂

/-- Failure of surjectivity on global sections of the quotient in a short
exact sequence produces nonvanishing first cohomology of the kernel.  This
is the formal long-exact-sequence step used after Voisin's dimension count
for `H¹(I_Z(l))`. -/
theorem not_schemeModuleCohomology_one_subsingleton_of_zero_map_not_surjective
    (X : Scheme.{u}) [HasExt.{u} X.Modules]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hnot : ¬ Function.Surjective (schemeModuleCohomologyMap X S.g 0)) :
    ¬ Subsingleton (schemeModuleCohomology X S.X₁ 1) := by
  intro hvan
  letI : Subsingleton (schemeModuleCohomology X S.X₁ 1) := hvan
  exact hnot
    (schemeModuleCohomology_zero_map_surjective_of_one_subsingleton X S hS)

/-- The other standard three-term consequence of the covariant long exact
cohomology sequence.  For a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0`, vanishing of `Hⁿ(B)` and `Hⁿ⁺¹(A)` implies vanishing
of `Hⁿ(C)`.

Applied to the restriction sequence of a hypersurface, this reduces
cohomology of the hypersurface twist to the two adjacent ambient
projective-space cohomology groups. -/
theorem schemeModuleCohomology_subsingleton_of_middle_and_next_left
    (X : Scheme.{u}) [HasExt.{u} X.Modules]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (schemeModuleCohomology X S.X₂ n)]
    [Subsingleton (schemeModuleCohomology X S.X₁ (n + 1))] :
    Subsingleton (schemeModuleCohomology X S.X₃ n) := by
  constructor
  intro x y
  suffices hzero : ∀ z : schemeModuleCohomology X S.X₃ n, z = 0 by
    exact (hzero x).trans (hzero y).symm
  intro z
  have hz : z.comp hS.extClass (show n + 1 = n + 1 by rfl) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨z₂, hz₂⟩ := Ext.covariant_sequence_exact₃
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) hS z
    (show n + 1 = n + 1 by rfl) hz
  rw [← hz₂, show z₂ = 0 by exact Subsingleton.elim _ _]
  exact Ext.zero_comp
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) n
    (Ext.mk₀ S.g) n (add_zero n)

/-- Degree-one hypersurface-restriction specialization: if `H¹(B)` and
`H²(A)` vanish in a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, then
`H¹(C)` vanishes. -/
theorem schemeModuleCohomology_one_subsingleton_of_middle_one_and_left_two
    (X : Scheme.{u}) [HasExt.{u} X.Modules]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Subsingleton (schemeModuleCohomology X S.X₂ 1)]
    [Subsingleton (schemeModuleCohomology X S.X₁ 2)] :
    Subsingleton (schemeModuleCohomology X S.X₃ 1) := by
  exact schemeModuleCohomology_subsingleton_of_middle_and_next_left
    X S hS 1

/-- Hypersurface-restriction form with the three terms identified only up to
isomorphism.  This is the convenient interface for a constructed twist
sequence: ambient vanishings for `A` and `B` imply the desired vanishing for
the restricted twist `C`. -/
theorem schemeModuleCohomology_subsingleton_of_restriction_sequence_isos
    (X : Scheme.{u}) [HasExt.{u} X.Modules]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ)
    {A B C : X.Modules} (eA : A ≅ S.X₁) (eB : B ≅ S.X₂)
    (eC : S.X₃ ≅ C)
    [Subsingleton (schemeModuleCohomology X B n)]
    [Subsingleton (schemeModuleCohomology X A (n + 1))] :
    Subsingleton (schemeModuleCohomology X C n) := by
  letI : Subsingleton (schemeModuleCohomology X S.X₁ (n + 1)) :=
    schemeModuleCohomology_subsingleton_of_iso X eA (n + 1)
  letI : Subsingleton (schemeModuleCohomology X S.X₂ n) :=
    schemeModuleCohomology_subsingleton_of_iso X eB n
  letI : Subsingleton (schemeModuleCohomology X S.X₃ n) :=
    schemeModuleCohomology_subsingleton_of_middle_and_next_left X S hS n
  exact schemeModuleCohomology_subsingleton_of_iso X eC n

/-- Degree-one cohomology on a scheme vanishes when degree-one cohomology of
its pushforward vanishes and that pushforward is exact.  This is the
closed-immersion comparison needed to pass from a hypersurface restriction
sequence on the ambient projective space to cohomology on the hypersurface.

Only exactness of pushforward is assumed.  Pullback need not be exact, and
pushforward need not preserve injective objects. -/
theorem schemeModuleCohomology_one_subsingleton_of_pushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasExt.{u} Y.Modules] [HasExt.{u} X.Modules]
    [EnoughInjectives X.Modules]
    [PreservesFiniteColimits (Scheme.Modules.pushforward f)]
    (M : X.Modules)
    [Subsingleton (schemeModuleCohomology Y
      ((Scheme.Modules.pushforward f).obj M) 1)] :
    Subsingleton (schemeModuleCohomology X M 1) := by
  let _ : PreservesFiniteLimits (Scheme.Modules.pushforward f) := by
    change PreservesFiniteLimits
      (SheafOfModules.pushforward f.toRingCatSheafHom)
    exact SheafOfModules.pushforward_preservesFiniteLimits _
  let _ : IsIso (BundleSectionZeroLocus.pullbackUnitComparison f) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  let h : Subsingleton
      (Ext ((Scheme.Modules.pullback f).obj
        (SheafOfModules.unit Y.ringCatSheaf)) M 1) :=
    ext_one_subsingleton_of_exact_right_adjoint
      (Scheme.Modules.pullback f) (Scheme.Modules.pushforward f)
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (SheafOfModules.unit Y.ringCatSheaf) M
  exact ext_subsingleton_of_iso_left
    (asIso (BundleSectionZeroLocus.pullbackUnitComparison f)) 1

end PfaffianDescent
