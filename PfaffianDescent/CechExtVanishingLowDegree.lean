import PfaffianDescent.ExtAcyclicResolutionLowDegree

/-!
# A low-degree acyclic-cover criterion for Ext

This file isolates the categorical step in the low-degree Čech argument.  An
augmented chain which is exact in its first two spots gives two short exact
sequences after passing to images.  Exactness of the induced `Hom(-, Y)`
cochain in degrees one and two supplies the two lifting conditions needed for
dimension shifting.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace PfaffianDescent

universe u v w

variable {A : Type u} [Category.{v} A] [Abelian A]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Exactness of a short complex can be tested after applying
`Hom(-, I)` for every injective target.  Enough injectives are used only to
embed the cokernel of the first differential into an injective object. -/
theorem shortComplex_exact_of_forall_injective_hom_exact
    [EnoughInjectives A] (S : ShortComplex A)
    (h : ∀ (I : A) [Injective I], Function.Exact
      (fun f : S.X₃ ⟶ I => S.g ≫ f)
      (fun f : S.X₂ ⟶ I => S.f ≫ f)) :
    S.Exact := by
  rw [S.exact_iff_kernel_ι_comp_cokernel_π_zero]
  let I := Injective.under (cokernel S.f)
  let j : cokernel S.f ⟶ I := Injective.ι (cokernel S.f)
  have hf : S.f ≫ (cokernel.π S.f ≫ j) = 0 := by
    rw [← Category.assoc, cokernel.condition, zero_comp]
  obtain ⟨q, hq⟩ := (h I (cokernel.π S.f ≫ j)).mp hf
  apply (cancel_mono j).1
  rw [zero_comp]
  calc
    (kernel.ι S.g ≫ cokernel.π S.f) ≫ j =
        kernel.ι S.g ≫ (cokernel.π S.f ≫ j) := Category.assoc _ _ _
    _ = kernel.ι S.g ≫ (S.g ≫ q) := by rw [← hq]
    _ = (kernel.ι S.g ≫ S.g) ≫ q := (Category.assoc _ _ _).symm
    _ = 0 := by rw [kernel.condition, zero_comp]

/-- A finite coproduct is Ext-acyclic in a fixed degree when all its
summands are.  In an abelian category the finite coproduct is the finite
biproduct, and `Ext` turns the latter into a product in its first variable. -/
theorem ext_finite_coproduct_subsingleton
    [HasExt.{w} A]
    {J : Type*} [Fintype J] (X : J → A) (Y : A) (n : ℕ)
    [∀ j, Subsingleton (Ext (X j) Y n)] :
    Subsingleton (Ext (∐ X) Y n) := by
  have hB : Subsingleton (Ext (⨁ X) Y n) :=
    (Equiv.subsingleton_congr
      (Ext.biproductAddEquiv (biproduct.isBilimit X) Y n).toEquiv).mpr
        inferInstance
  let _ : Subsingleton (Ext (⨁ X) Y n) := hB
  exact ext_subsingleton_of_iso_left (biproduct.isoCoproduct X) n

/-- Low-degree acyclic-cover criterion, expressed entirely in the source
abelian category.  The first two exact spots of an augmented chain, local
Ext-acyclicity, and exactness of the induced Hom cochain in degrees one and
two imply global Ext vanishing in those degrees. -/
theorem ext_one_and_two_subsingleton_of_augmented_acyclic_chain
    [HasExt.{w} A]
    (Y P C₀ C₁ C₂ C₃ : A)
    (ε : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂)
    (h₁₀ : d₁ ≫ ε = 0) (h₂₁ : d₂ ≫ d₁ = 0) (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₀ : (ShortComplex.mk d₁ ε h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    [Epi ε]
    [Subsingleton (Ext C₀ Y 1)]
    [Subsingleton (Ext C₀ Y 2)]
    [Subsingleton (Ext C₁ Y 1)]
    (hHom₁ : Function.Exact
      (fun f : C₀ ⟶ Y => d₁ ≫ f)
      (fun f : C₁ ⟶ Y => d₂ ≫ f))
    (hHom₂ : Function.Exact
      (fun f : C₁ ⟶ Y => d₂ ≫ f)
      (fun f : C₂ ⟶ Y => d₃ ≫ f)) :
    Subsingleton (Ext P Y 1) ∧ Subsingleton (Ext P Y 2) := by
  let S₀ : ShortComplex A :=
    ShortComplex.mk (Abelian.image.ι d₁) ε
      (Abelian.image_ι_comp_eq_zero h₁₀)
  have hS₀Exact : S₀.Exact := by
    exact ((ShortComplex.mk d₁ ε h₁₀).exact_iff_exact_image_ι).mp hexact₀
  have hS₀Mono : Mono S₀.f := by
    dsimp [S₀]
    infer_instance
  have hS₀Epi : Epi S₀.g := by
    dsimp [S₀]
    infer_instance
  have hS₀ : S₀.ShortExact :=
    ShortComplex.ShortExact.mk' hS₀Exact hS₀Mono hS₀Epi

  let T₁ : ShortComplex A :=
    ShortComplex.mk (Abelian.factorThruCoimage d₂) d₁ (by
      apply (cancel_epi (Abelian.coimage.π d₂)).1
      simpa only [← Category.assoc, Abelian.coimage.fac, comp_zero] using h₂₁)
  have hT₁Exact : T₁.Exact := by
    let T : ShortComplex A := ShortComplex.mk d₂ d₁ h₂₁
    let φ : T ⟶ T₁ :=
      { τ₁ := Abelian.coimage.π d₂
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hexact₁

  let S₁ : ShortComplex A :=
    ShortComplex.mk (Abelian.factorThruCoimage d₂)
      (Abelian.factorThruImage d₁) (by
        apply (cancel_mono (Abelian.image.ι d₁)).1
        simpa only [Category.assoc, Abelian.image.fac, zero_comp] using T₁.zero)
  have hS₁Exact : S₁.Exact := by
    let φ : S₁ ⟶ T₁ :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := Abelian.image.ι d₁ }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hT₁Exact
  have hS₁Mono : Mono S₁.f := by
    dsimp [S₁]
    infer_instance
  have hS₁Epi : Epi S₁.g := by
    dsimp [S₁]
    infer_instance
  have hS₁ : S₁.ShortExact :=
    ShortComplex.ShortExact.mk' hS₁Exact hS₁Mono hS₁Epi

  have hsurj₀ : Function.Surjective
      (fun f : S₀.X₂ ⟶ Y => S₀.f ≫ f) := by
    have hz : d₂ ≫ Abelian.factorThruImage d₁ = 0 := by
      apply (cancel_mono (Abelian.image.ι d₁)).1
      simpa only [Category.assoc, Abelian.image.fac, zero_comp] using h₂₁
    apply hom_precomp_surjective_of_exact_and_epi Y
      (Abelian.image.ι d₁) (Abelian.factorThruImage d₁) d₂ hz
    simpa only [Abelian.image.fac] using hHom₁
  have hsurj₁ : Function.Surjective
      (fun f : S₁.X₂ ⟶ Y => S₁.f ≫ f) := by
    apply hom_precomp_surjective_of_exact_and_epi Y
      (Abelian.factorThruCoimage d₂) (Abelian.coimage.π d₂) d₃
      (Abelian.comp_coimage_π_eq_zero h₃₂)
    simpa only [Abelian.coimage.fac] using hHom₂

  exact ext_one_and_two_subsingleton_of_two_step_acyclic_resolution
    Y S₀ S₁ hS₀ hS₁ rfl hsurj₀ hsurj₁

end PfaffianDescent
