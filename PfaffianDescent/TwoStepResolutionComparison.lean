import PfaffianDescent.CechExtDegreeTwo

/-!
# Source comparison of two-step resolution classes

The source map of a chain comparison gives contravariant pullback of the
Yoneda class. The two kernel maps are constructed from the first two terms
by the universal property of the kernels.
-/

noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A]
namespace TwoStepResolution
/-- A comparison of two exact two-step resolutions. -/
structure Hom (R S : TwoStepResolution A) where
  onP : R.P ⟶ S.P
  onC₀ : R.C₀ ⟶ S.C₀
  onC₁ : R.C₁ ⟶ S.C₁
  onK₀ : R.K₀ ⟶ S.K₀
  onK₁ : R.K₁ ⟶ S.K₁
  comm_i₀ : R.i₀ ≫ onC₀ = onK₀ ≫ S.i₀
  comm_p₀ : R.p₀ ≫ onP = onC₀ ≫ S.p₀
  comm_i₁ : R.i₁ ≫ onC₁ = onK₁ ≫ S.i₁
  comm_p₁ : R.p₁ ≫ onK₀ = onC₁ ≫ S.p₁

def Hom.mapS₀ {R S : TwoStepResolution A} (φ : Hom R S) : R.S₀ ⟶ S.S₀ where
  τ₁ := φ.onK₀
  τ₂ := φ.onC₀
  τ₃ := φ.onP
  comm₁₂ := φ.comm_i₀.symm
  comm₂₃ := φ.comm_p₀.symm

def Hom.mapS₁ {R S : TwoStepResolution A} (φ : Hom R S) : R.S₁ ⟶ S.S₁ where
  τ₁ := φ.onK₁
  τ₂ := φ.onC₁
  τ₃ := φ.onK₀
  comm₁₂ := φ.comm_i₁.symm
  comm₂₃ := φ.comm_p₁.symm

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation and first differential squares determine the kernel maps. -/
noncomputable def Hom.ofFirstTerms
    {R S : TwoStepResolution A}
    (aP : R.P ⟶ S.P) (a₀ : R.C₀ ⟶ S.C₀) (a₁ : R.C₁ ⟶ S.C₁)
    (h₀ : R.p₀ ≫ aP = a₀ ≫ S.p₀)
    (h₁ : (R.p₁ ≫ R.i₀) ≫ a₀ = a₁ ≫ (S.p₁ ≫ S.i₀)) : Hom R S := by
  letI : Mono S.i₀ := S.exact₀.mono_f
  have hz₀ : (R.i₀ ≫ a₀) ≫ S.p₀ = 0 := by
    rw [Category.assoc, ← h₀, ← Category.assoc, R.zero₀, zero_comp]
  let k₀ : R.K₀ ⟶ S.K₀ :=
    S.exact₀.fIsKernel.lift (KernelFork.ofι (R.i₀ ≫ a₀) hz₀)
  have hk₀ : k₀ ≫ S.i₀ = R.i₀ ≫ a₀ :=
    S.exact₀.fIsKernel.fac (KernelFork.ofι (R.i₀ ≫ a₀) hz₀) WalkingParallelPair.zero
  have hp₁ : R.p₁ ≫ k₀ = a₁ ≫ S.p₁ := by
    apply (cancel_mono S.i₀).1
    rw [Category.assoc, hk₀, ← Category.assoc, h₁, Category.assoc]
  have hz₁ : (R.i₁ ≫ a₁) ≫ S.p₁ = 0 := by
    rw [Category.assoc, ← hp₁, ← Category.assoc, R.zero₁, zero_comp]
  let k₁ : R.K₁ ⟶ S.K₁ :=
    S.exact₁.fIsKernel.lift (KernelFork.ofι (R.i₁ ≫ a₁) hz₁)
  have hk₁ : k₁ ≫ S.i₁ = R.i₁ ≫ a₁ :=
    S.exact₁.fIsKernel.fac (KernelFork.ofι (R.i₁ ≫ a₁) hz₁) WalkingParallelPair.zero
  exact ⟨aP, a₀, a₁, k₀, k₁, hk₀.symm, h₀, hk₁.symm, hp₁⟩

set_option backward.isDefEq.respectTransparency false in
/-- The induced second-kernel map respects an explicit presentation. -/
theorem Hom.onK₁_of_presentation
    {R S : TwoStepResolution A} (φ : Hom R S)
    {C D : A} (πR : C ⟶ R.K₁) (πS : D ⟶ S.K₁) (a : C ⟶ D)
    (h : (πR ≫ R.i₁) ≫ φ.onC₁ = a ≫ (πS ≫ S.i₁)) :
    πR ≫ φ.onK₁ = a ≫ πS := by
  letI : Mono S.i₁ := S.exact₁.mono_f
  apply (cancel_mono S.i₁).1
  rw [Category.assoc, ← φ.comm_i₁, ← Category.assoc, h, Category.assoc]

variable [HasExt.{w} A]
/-- Source comparison gives the pullback of the Yoneda class. -/
theorem connecting_naturality {R S : TwoStepResolution A} (φ : Hom R S)
    (Y : A) (x : S.K₁ ⟶ Y) :
    R.connecting Y (φ.onK₁ ≫ x) =
      (Ext.mk₀ φ.onP).comp (S.connecting Y x) (zero_add 2) := by
  have h₀ := R.exact₀.extClass_naturality S.exact₀ φ.mapS₀
  have h₁ := R.exact₁.extClass_naturality S.exact₁ φ.mapS₁
  change R.exact₀.extClass.comp (Ext.mk₀ φ.onK₀) (add_zero 1) =
    (Ext.mk₀ φ.onP).comp S.exact₀.extClass (zero_add 1) at h₀
  change R.exact₁.extClass.comp (Ext.mk₀ φ.onK₁) (add_zero 1) =
    (Ext.mk₀ φ.onK₀).comp S.exact₁.extClass (zero_add 1) at h₁
  have hinner : R.exact₁.extClass.comp (Ext.mk₀ (φ.onK₁ ≫ x)) (by rfl) =
      (Ext.mk₀ φ.onK₀).comp
        (S.exact₁.extClass.comp (Ext.mk₀ x) (by rfl)) (zero_add 1) := by
    rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc, h₁, Ext.comp_assoc] <;> rfl
  unfold connecting
  rw [hinner, ← Ext.comp_assoc, h₀, Ext.comp_assoc] <;> rfl

/-- Matching coefficients on an epimorphic presentation suffice for class compatibility. -/
theorem connecting_naturality_of_coefficients
    {R S : TwoStepResolution A} (φ : Hom R S)
    {C D Y : A} (πR : C ⟶ R.K₁) [Epi πR]
    (πS : D ⟶ S.K₁) (a : C ⟶ D)
    (h : (πR ≫ R.i₁) ≫ φ.onC₁ = a ≫ (πS ≫ S.i₁))
    (r : R.K₁ ⟶ Y) (s : S.K₁ ⟶ Y)
    (hcoeff : πR ≫ r = a ≫ (πS ≫ s)) :
    R.connecting Y r = (Ext.mk₀ φ.onP).comp (S.connecting Y s) (zero_add 2) := by
  have hr : r = φ.onK₁ ≫ s := by
    apply (cancel_epi πR).1
    rw [← Category.assoc, φ.onK₁_of_presentation πR πS a h, Category.assoc]
    exact hcoeff
  rw [hr]
  exact connecting_naturality φ Y s
end TwoStepResolution
end PfaffianDescent
