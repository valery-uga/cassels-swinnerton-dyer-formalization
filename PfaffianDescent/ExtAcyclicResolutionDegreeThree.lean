import PfaffianDescent.ExtAcyclicResolutionLowDegree

/-!
# Degree-three dimension shifting for an acyclic source resolution

Three consecutive short exact sequences give a composite connecting map
from `Hom(K₂, Y)` to `Ext³(P, Y)`. Under the standard acyclicity assumptions
it is onto, and its kernel consists exactly of the maps which extend across
`K₂ ⟶ C₂`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace PfaffianDescent

universe u v w

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- Three composable short exact sequences, written with shared kernel
objects so that dimension shifting involves no transport across equalities. -/
structure ThreeStepResolution (A : Type u) [Category.{v} A] [Abelian A] where
  P : A
  C₀ : A
  C₁ : A
  C₂ : A
  K₀ : A
  K₁ : A
  K₂ : A
  i₀ : K₀ ⟶ C₀
  p₀ : C₀ ⟶ P
  zero₀ : i₀ ≫ p₀ = 0
  i₁ : K₁ ⟶ C₁
  p₁ : C₁ ⟶ K₀
  zero₁ : i₁ ≫ p₁ = 0
  i₂ : K₂ ⟶ C₂
  p₂ : C₂ ⟶ K₁
  zero₂ : i₂ ≫ p₂ = 0
  exact₀ : (ShortComplex.mk i₀ p₀ zero₀).ShortExact
  exact₁ : (ShortComplex.mk i₁ p₁ zero₁).ShortExact
  exact₂ : (ShortComplex.mk i₂ p₂ zero₂).ShortExact

namespace ThreeStepResolution

variable (R : ThreeStepResolution A)

abbrev S₀ : ShortComplex A := ShortComplex.mk R.i₀ R.p₀ R.zero₀
abbrev S₁ : ShortComplex A := ShortComplex.mk R.i₁ R.p₁ R.zero₁
abbrev S₂ : ShortComplex A := ShortComplex.mk R.i₂ R.p₂ R.zero₂

/-- The composite of the three contravariant connecting morphisms. -/
def connecting (Y : A) (x : R.K₂ ⟶ Y) : Ext R.P Y 3 :=
  R.exact₀.extClass.comp
    (R.exact₁.extClass.comp
      (R.exact₂.extClass.comp (Ext.mk₀ x) (show 1 + 0 = 1 by rfl))
      (show 1 + 1 = 2 by rfl))
    (show 1 + 2 = 3 by rfl)

@[simp]
theorem connecting_zero (Y : A) :
    R.connecting Y (0 : R.K₂ ⟶ Y) = 0 := by
  simp [connecting]

theorem connecting_add (Y : A) (x y : R.K₂ ⟶ Y) :
    R.connecting Y (x + y) = R.connecting Y x + R.connecting Y y := by
  simp only [connecting, Ext.mk₀_add, Ext.comp_add]

end ThreeStepResolution

/-- A connecting morphism is injective if the preceding Ext group of the
middle object vanishes. -/
theorem extClass_comp_injective_of_middle_subsingleton
    (Y : A) (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext S.X₂ Y n)] :
    Function.Injective (fun x : Ext S.X₁ Y n =>
      hS.extClass.comp x (show 1 + n = n + 1 by omega)) := by
  intro x y hxy
  have hz : hS.extClass.comp (x - y) (show 1 + n = n + 1 by omega) = 0 := by
    rw [sub_eq_add_neg, Ext.comp_add, Ext.comp_neg]
    simpa only [sub_eq_add_neg] using sub_eq_zero.mpr hxy
  obtain ⟨z, hz'⟩ := Ext.contravariant_sequence_exact₁
    hS Y (x - y) (show 1 + n = n + 1 by omega) hz
  have hzero : z = 0 := Subsingleton.elim _ _
  rw [hzero, Ext.comp_zero] at hz'
  exact sub_eq_zero.mp hz'.symm

/-- Under acyclicity of the three middle terms in the indicated degrees,
the degree-three connecting map is surjective. -/
theorem ThreeStepResolution.connecting_surjective
    (R : ThreeStepResolution A) (Y : A)
    [Subsingleton (Ext R.C₀ Y 3)]
    [Subsingleton (Ext R.C₁ Y 2)]
    [Subsingleton (Ext R.C₂ Y 1)] :
    Function.Surjective (R.connecting Y) := by
  intro z
  have hz : (Ext.mk₀ R.p₀).comp z (zero_add 3) = 0 := Subsingleton.elim _ _
  obtain ⟨x₀, hx₀⟩ := Ext.contravariant_sequence_exact₃
    R.exact₀ Y z hz (show 1 + 2 = 3 by rfl)
  have hx₀z : (Ext.mk₀ R.p₁).comp x₀ (zero_add 2) = 0 := Subsingleton.elim _ _
  obtain ⟨x₁, hx₁⟩ := Ext.contravariant_sequence_exact₃
    R.exact₁ Y x₀ hx₀z (show 1 + 1 = 2 by rfl)
  have hx₁z : (Ext.mk₀ R.p₂).comp x₁ (zero_add 1) = 0 := Subsingleton.elim _ _
  obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₃
    R.exact₂ Y x₁ hx₁z (show 1 + 0 = 1 by rfl)
  refine ⟨Ext.addEquiv₀ x₂, ?_⟩
  simp only [ThreeStepResolution.connecting, Ext.mk₀_addEquiv₀_apply, hx₂, hx₁, hx₀]

/-- The kernel of the degree-three connecting map is exactly the image of
restriction along `K₂ ⟶ C₂`. -/
theorem ThreeStepResolution.connecting_eq_zero_iff
    (R : ThreeStepResolution A) (Y : A)
    [Subsingleton (Ext R.C₀ Y 2)]
    [Subsingleton (Ext R.C₁ Y 1)]
    (x : R.K₂ ⟶ Y) :
    R.connecting Y x = 0 ↔ ∃ q : R.C₂ ⟶ Y, R.i₂ ≫ q = x := by
  let δ₀ := fun a : Ext R.K₂ Y 0 =>
    R.exact₂.extClass.comp a (show 1 + 0 = 1 by rfl)
  let δ₁ := fun a : Ext R.K₁ Y 1 =>
    R.exact₁.extClass.comp a (show 1 + 1 = 2 by rfl)
  let δ₂ := fun a : Ext R.K₀ Y 2 =>
    R.exact₀.extClass.comp a (show 1 + 2 = 3 by rfl)
  have hδ₂ : Function.Injective δ₂ :=
    extClass_comp_injective_of_middle_subsingleton Y R.S₀ R.exact₀ 2
  have hδ₁ : Function.Injective δ₁ :=
    extClass_comp_injective_of_middle_subsingleton Y R.S₁ R.exact₁ 1
  constructor
  · intro hx
    have h₂ : δ₁ (δ₀ (Ext.mk₀ x)) = 0 := by
      apply hδ₂
      simpa only [δ₂, δ₁, δ₀, ThreeStepResolution.connecting, Ext.comp_zero] using hx
    have h₁ : δ₀ (Ext.mk₀ x) = 0 := by
      apply hδ₁
      simpa only [δ₁, δ₀, Ext.comp_zero] using h₂
    obtain ⟨q₀, hq₀⟩ := Ext.contravariant_sequence_exact₁
      R.exact₂ Y (Ext.mk₀ x) (show 1 + 0 = 1 by rfl) h₁
    refine ⟨Ext.addEquiv₀ q₀, ?_⟩
    apply (Ext.mk₀_bijective _ _).injective
    rw [← Ext.mk₀_addEquiv₀_apply q₀] at hq₀
    simpa only [Ext.mk₀_comp_mk₀] using hq₀
  · rintro ⟨q, rfl⟩
    simp only [ThreeStepResolution.connecting, ← Ext.mk₀_comp_mk₀,
      R.exact₂.extClass_comp_assoc, Ext.comp_zero]

end PfaffianDescent
