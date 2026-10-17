import PfaffianDescent.ExtAcyclicResolutionDegreeThree

/-!
# Degree-two dimension shifting for an acyclic source resolution

Two consecutive short exact sequences give a composite connecting map from
`Hom(K₁,Y)` to `Ext²(P,Y)`. Under the standard acyclicity assumptions it is
surjective, and its kernel consists exactly of maps extending across
`K₁ ⟶ C₁`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace PfaffianDescent

universe u v w

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/- Two composable short exact sequences, with their shared kernel object
made explicit. -/
structure TwoStepResolution (A : Type u) [Category.{v} A] [Abelian A] where
  P : A
  C₀ : A
  C₁ : A
  K₀ : A
  K₁ : A
  i₀ : K₀ ⟶ C₀
  p₀ : C₀ ⟶ P
  zero₀ : i₀ ≫ p₀ = 0
  i₁ : K₁ ⟶ C₁
  p₁ : C₁ ⟶ K₀
  zero₁ : i₁ ≫ p₁ = 0
  exact₀ : (ShortComplex.mk i₀ p₀ zero₀).ShortExact
  exact₁ : (ShortComplex.mk i₁ p₁ zero₁).ShortExact

namespace TwoStepResolution

variable (R : TwoStepResolution A)

abbrev S₀ : ShortComplex A := ShortComplex.mk R.i₀ R.p₀ R.zero₀
abbrev S₁ : ShortComplex A := ShortComplex.mk R.i₁ R.p₁ R.zero₁

/- The composite of the two contravariant connecting morphisms. -/
def connecting (Y : A) (x : R.K₁ ⟶ Y) : Ext R.P Y 2 :=
  R.exact₀.extClass.comp
    (R.exact₁.extClass.comp (Ext.mk₀ x) (show 1 + 0 = 1 by rfl))
    (show 1 + 1 = 2 by rfl)

@[simp]
theorem connecting_zero (Y : A) :
    R.connecting Y (0 : R.K₁ ⟶ Y) = 0 := by
  simp [connecting]

theorem connecting_add (Y : A) (x y : R.K₁ ⟶ Y) :
    R.connecting Y (x + y) = R.connecting Y x + R.connecting Y y := by
  simp only [connecting, Ext.mk₀_add, Ext.comp_add]

end TwoStepResolution

/- Under acyclicity of the two middle terms in the indicated degrees, the
degree-two connecting map is surjective. -/
theorem TwoStepResolution.connecting_surjective
    (R : TwoStepResolution A) (Y : A)
    [Subsingleton (Ext R.C₀ Y 2)]
    [Subsingleton (Ext R.C₁ Y 1)] :
    Function.Surjective (R.connecting Y) := by
  intro z
  have hz : (Ext.mk₀ R.p₀).comp z (zero_add 2) = 0 := Subsingleton.elim _ _
  obtain ⟨x₀, hx₀⟩ := Ext.contravariant_sequence_exact₃
    R.exact₀ Y z hz (show 1 + 1 = 2 by rfl)
  have hx₀z : (Ext.mk₀ R.p₁).comp x₀ (zero_add 1) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨x₁, hx₁⟩ := Ext.contravariant_sequence_exact₃
    R.exact₁ Y x₀ hx₀z (show 1 + 0 = 1 by rfl)
  refine ⟨Ext.addEquiv₀ x₁, ?_⟩
  simp only [TwoStepResolution.connecting, Ext.mk₀_addEquiv₀_apply, hx₁, hx₀]

/- The kernel of the degree-two connecting map is exactly the image of
restriction along `K₁ ⟶ C₁`. -/
theorem TwoStepResolution.connecting_eq_zero_iff
    (R : TwoStepResolution A) (Y : A)
    [Subsingleton (Ext R.C₀ Y 1)]
    (x : R.K₁ ⟶ Y) :
    R.connecting Y x = 0 ↔ ∃ q : R.C₁ ⟶ Y, R.i₁ ≫ q = x := by
  let delta₀ := fun a : Ext R.K₁ Y 0 =>
    R.exact₁.extClass.comp a (show 1 + 0 = 1 by rfl)
  let delta₁ := fun a : Ext R.K₀ Y 1 =>
    R.exact₀.extClass.comp a (show 1 + 1 = 2 by rfl)
  have hdelta₁ : Function.Injective delta₁ :=
    extClass_comp_injective_of_middle_subsingleton Y R.S₀ R.exact₀ 1
  constructor
  · intro hx
    have h₀ : delta₀ (Ext.mk₀ x) = 0 := by
      apply hdelta₁
      simpa only [delta₁, delta₀, TwoStepResolution.connecting,
        Ext.comp_zero] using hx
    obtain ⟨q₀, hq₀⟩ := Ext.contravariant_sequence_exact₁
      R.exact₁ Y (Ext.mk₀ x) (show 1 + 0 = 1 by rfl) h₀
    refine ⟨Ext.addEquiv₀ q₀, ?_⟩
    apply (Ext.mk₀_bijective _ _).injective
    rw [← Ext.mk₀_addEquiv₀_apply q₀] at hq₀
    simpa only [Ext.mk₀_comp_mk₀] using hq₀
  · rintro ⟨q, rfl⟩
    simp only [TwoStepResolution.connecting, ← Ext.mk₀_comp_mk₀,
      R.exact₁.extClass_comp_assoc, Ext.comp_zero]

end PfaffianDescent
