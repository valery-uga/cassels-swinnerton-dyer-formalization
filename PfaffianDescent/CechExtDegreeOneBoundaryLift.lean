import PfaffianDescent.SchemeCoverCechExtDegreeOne
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! Literal lifted cocycles represent the actual connecting class of the
actual coefficient short exact sequence. Ordinary diagram equations are
used only at this generic categorical boundary, not supplied compatibility
of the desired Ext comparisons. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- A genuine degree-zero lift and its literal differential represent the
connecting class of the original coefficient sequence. -/
theorem augmentedChainDegreeOneToExt_eq_boundary_of_lift
    {P C₀ C₁ C₂ : A} (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact) [Epi epsilon]
    (S : ShortComplex A) (hS : S.ShortExact)
    (q : P ⟶ S.X₃) (p : C₀ ⟶ S.X₂)
    (z : DegreeOneCocycle d₂ (Y := S.X₁))
    (hp : p ≫ S.g = epsilon ≫ q) (hz : d₁ ≫ p = z.1 ≫ S.f) :
    augmentedChainDegreeOneToExtHom S.X₁ epsilon d₁ d₂
      h₁₀ h₂₁ hexact₀ hexact₁ z =
      (Ext.mk₀ q).comp hS.extClass (zero_add 1) := by
  let T := augmentedChainDegreeOneShortComplex epsilon d₁ h₁₀
  let hT := augmentedChainDegreeOneShortComplex_shortExact epsilon d₁ h₁₀ hexact₀
  let a := degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ z
  have ha : Abelian.image.ι d₁ ≫ p = a ≫ S.f := by
    apply (cancel_epi (Abelian.factorThruImage d₁)).1
    calc
      Abelian.factorThruImage d₁ ≫ (Abelian.image.ι d₁ ≫ p) = d₁ ≫ p := by
        rw [← Category.assoc, Abelian.image.fac]
      _ = z.1 ≫ S.f := hz
      _ = Abelian.factorThruImage d₁ ≫ (a ≫ S.f) := by
        rw [← Category.assoc]
        exact congrArg (fun k : C₁ ⟶ S.X₁ => k ≫ S.f)
          (factorThruImage_comp_degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ z).symm
  let t : T ⟶ S := ShortComplex.homMk a p q ha.symm hp
  exact ShortComplex.ShortExact.extClass_naturality hT hS t

end PfaffianDescent
end
