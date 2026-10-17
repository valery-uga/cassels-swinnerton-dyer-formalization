import PfaffianDescent.ExtAcyclicResolutionDegreeThree

/-! # Actual ambient degree-three pullback from a point resolution

This formalizes the categorical part of the ambient rational-point route.
For a three-step resolution, acyclicity of its two negative middle terms
and last kernel makes pullback along the actual augmentation an equivalence.
The projective Koszul resolution and its twist-Ext vanishings still have to
be constructed geometrically; these are explicit hypotheses here.
-/

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace PfaffianDescent

universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- Vanishing on the kernel in the two adjacent degrees makes actual
contravariant pullback an isomorphism. -/
theorem pointGlobalTrace_precomp_bijective_of_kernel_vanishing
    (Y : A) (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext S.X₁ Y n)] [Subsingleton (Ext S.X₁ Y (n + 1))] :
    Function.Bijective ((Ext.mk₀ S.g).precomp Y (zero_add (n + 1))) := by
  constructor
  · intro x y hxy
    change (Ext.mk₀ S.g).comp x (zero_add (n + 1)) =
      (Ext.mk₀ S.g).comp y (zero_add (n + 1)) at hxy
    have hz : (Ext.mk₀ S.g).comp (x - y) (zero_add (n + 1)) = 0 := by
      rw [sub_eq_add_neg, Ext.comp_add, Ext.comp_neg]
      simpa only [sub_eq_add_neg] using sub_eq_zero.mpr hxy
    obtain ⟨z, hz'⟩ := Ext.contravariant_sequence_exact₃
      hS Y (x - y) hz (show 1 + n = n + 1 by omega)
    rw [show z = 0 from Subsingleton.elim _ _, Ext.comp_zero] at hz'
    exact sub_eq_zero.mp hz'.symm
  · intro z
    have hz : (Ext.mk₀ S.f).comp z (zero_add (n + 1)) = 0 :=
      Subsingleton.elim _ _
    exact Ext.contravariant_sequence_exact₂ hS Y z hz

/-- A three-step resolution whose negative terms have the six indicated
vanishings makes pullback along its augmentation an actual Ext equivalence.
For the projective point Koszul resolution, the three negative terms are
`O(-1)^3`, `O(-2)^3`, and `O(-3)`. -/
def pointGlobalTraceAmbientResolutionPullbackEquiv
    (R : ThreeStepResolution A) (Y : A)
    [Subsingleton (Ext R.C₁ Y 2)] [Subsingleton (Ext R.C₁ Y 3)]
    [Subsingleton (Ext R.C₂ Y 1)] [Subsingleton (Ext R.C₂ Y 2)]
    [Subsingleton (Ext R.K₂ Y 0)] [Subsingleton (Ext R.K₂ Y 1)] :
    Ext R.P Y 3 ≃+ Ext R.C₀ Y 3 := by
  letI : Subsingleton (Ext R.K₁ Y 1) :=
    ext_succ_subsingleton_X3_of_left_and_middle Y R.S₂ R.exact₂ 0
  letI : Subsingleton (Ext R.K₁ Y 2) :=
    ext_succ_subsingleton_X3_of_left_and_middle Y R.S₂ R.exact₂ 1
  letI : Subsingleton (Ext R.K₀ Y 2) :=
    ext_succ_subsingleton_X3_of_left_and_middle Y R.S₁ R.exact₁ 1
  letI : Subsingleton (Ext R.K₀ Y 3) :=
    ext_succ_subsingleton_X3_of_left_and_middle Y R.S₁ R.exact₁ 2
  exact AddEquiv.ofBijective ((Ext.mk₀ R.p₀).precomp Y (zero_add 3))
    (pointGlobalTrace_precomp_bijective_of_kernel_vanishing Y R.S₀ R.exact₀ 2)

/-- The equivalence uses the actual augmentation, rather than an arbitrary
coordinate on the two Ext groups. -/
theorem pointGlobalTraceAmbientResolutionPullbackEquiv_apply
    (R : ThreeStepResolution A) (Y : A)
    [Subsingleton (Ext R.C₁ Y 2)] [Subsingleton (Ext R.C₁ Y 3)]
    [Subsingleton (Ext R.C₂ Y 1)] [Subsingleton (Ext R.C₂ Y 2)]
    [Subsingleton (Ext R.K₂ Y 0)] [Subsingleton (Ext R.K₂ Y 1)]
    (z : Ext R.P Y 3) :
    pointGlobalTraceAmbientResolutionPullbackEquiv R Y z =
      (Ext.mk₀ R.p₀).comp z (zero_add 3) := rfl

end PfaffianDescent
