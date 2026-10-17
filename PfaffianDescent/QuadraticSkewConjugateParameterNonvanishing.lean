import PfaffianDescent.QuadraticSkewMixedSecantNonvanishing
/-! SOURCE ONLY / UNVERIFIED. The two independent split parameters
are an invertible linear change of the actual ground affine-plane variables;
nonzero A/B stay nonzero under this substitution in every characteristic. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.MixedNonvanishing
open MvPolynomial Module
open ActualSecant MixedNormalForm
universe u v
variable {E : Type u} [Field E]

abbrev planeT : MvPolynomial SecantPlaneIndex.{v} E := X (ULift.up 0)
abbrev planeU : MvPolynomial SecantPlaneIndex.{v} E := X (ULift.up 1)

def conjugateParameterSubstitution (α β : E) :
    MvPolynomial SecantPlaneIndex.{v} E →ₐ[E] MvPolynomial SecantPlaneIndex.{v} E :=
  MvPolynomial.aeval (fun i => ![planeT.{u, v} + C α * planeU.{u, v}, planeT.{u, v} + C β * planeU.{u, v}] i.down)

def conjugateParameterInverseSubstitution (α β : E) :
    MvPolynomial SecantPlaneIndex.{v} E →ₐ[E] MvPolynomial SecantPlaneIndex.{v} E :=
  MvPolynomial.aeval (fun i =>
    ![C (α - β)⁻¹ * (C α * planeU.{u, v} - C β * planeT.{u, v}),
      C (α - β)⁻¹ * (planeT.{u, v} - planeU.{u, v})] i.down)

set_option backward.isDefEq.respectTransparency false in
theorem conjugateParameterInverseSubstitution_comp
    (α β : E) (hαβ : α ≠ β) :
    (conjugateParameterInverseSubstitution.{u, v} α β).comp
      (conjugateParameterSubstitution.{u, v} α β) = AlgHom.id E _ := by
  let t : MvPolynomial (ULift.{v} (Fin 2)) E := X (ULift.up 0)
  let z : MvPolynomial (ULift.{v} (Fin 2)) E := X (ULift.up 1)
  let f : MvPolynomial (ULift.{v} (Fin 2)) E →ₐ[E]
      MvPolynomial (ULift.{v} (Fin 2)) E :=
    MvPolynomial.aeval (fun i : ULift.{v} (Fin 2) =>
      ![t + C α * z, t + C β * z] i.down)
  let g : MvPolynomial (ULift.{v} (Fin 2)) E →ₐ[E]
      MvPolynomial (ULift.{v} (Fin 2)) E :=
    MvPolynomial.aeval (fun i : ULift.{v} (Fin 2) =>
      ![C (α - β)⁻¹ * (C α * z - C β * t),
        C (α - β)⁻¹ * (t - z)] i.down)
  have hδ : (C (α - β)⁻¹ : MvPolynomial (ULift.{v} (Fin 2)) E) *
      (C α - C β) = 1 := by
    rw [← map_sub, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hαβ), map_one]
  change g.comp f = AlgHom.id E _
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with ⟨i⟩
  fin_cases i
  · change g (f t) = t
    simp [f, g, t, z, MvPolynomial.algebraMap_eq]
    linear_combination (X (ULift.up (0 : Fin 2)) :
      MvPolynomial (ULift.{v} (Fin 2)) E) * hδ
  · change g (f z) = z
    simp [f, g, t, z, MvPolynomial.algebraMap_eq]
    linear_combination (X (ULift.up (1 : Fin 2)) :
      MvPolynomial (ULift.{v} (Fin 2)) E) * hδ

theorem conjugateParameterSubstitution_injective (α β : E) (hαβ : α ≠ β) :
    Function.Injective (conjugateParameterSubstitution.{u, v} α β) := by
  intro p q h
  have h' := congrArg (conjugateParameterInverseSubstitution.{u, v} α β) h
  have hleft (r : MvPolynomial SecantPlaneIndex.{v} E) :
      conjugateParameterInverseSubstitution.{u, v} α β (conjugateParameterSubstitution.{u, v} α β r) = r := by
    exact DFunLike.congr_fun (conjugateParameterInverseSubstitution_comp.{u, v} α β hαβ) r
  rwa [hleft p, hleft q] at h'

def swappedConjugateParameterSubstitution (α β : E) :
    MvPolynomial SecantPlaneIndex.{v} E →ₐ[E] MvPolynomial SecantPlaneIndex.{v} E :=
  MvPolynomial.aeval (fun i => ![planeT.{u, v} + C β * planeU.{u, v}, planeT.{u, v} + C α * planeU.{u, v}] i.down)

theorem swappedConjugateParameterSubstitution_injective (α β : E) (hαβ : α ≠ β) :
    Function.Injective (swappedConjugateParameterSubstitution.{u, v} α β) := by
  exact conjugateParameterSubstitution_injective.{u, v} β α hαβ.symm

def actualSecantA (α β : E) (G : MvPolynomial (Fin 4) E) :
    MvPolynomial SecantPlaneIndex.{v} E :=
  conjugateParameterSubstitution.{u, v} α β (leftSecantPolynomial.{u, v} G)

def actualSecantB (α β : E) (G : MvPolynomial (Fin 4) E) :
    MvPolynomial SecantPlaneIndex.{v} E :=
  swappedConjugateParameterSubstitution.{u, v} α β (rightSecantPolynomial.{u, v} G)

set_option backward.isDefEq.respectTransparency false in
theorem actualSecantA_eq_leftMixedValue (α β : E) (G : MvPolynomial (Fin 4) E) :
    actualSecantA.{u, v} α β G = leftMixedValue (mappedMixedCoefficients C G)
      1 (planeT.{u, v} + C α * planeU.{u, v}) 1 (planeT.{u, v} + C β * planeU.{u, v}) := by
  let t : MvPolynomial (ULift.{v} (Fin 2)) E := X (ULift.up 0)
  let z : MvPolynomial (ULift.{v} (Fin 2)) E := X (ULift.up 1)
  let ta : MvPolynomial (ULift.{v} (Fin 2)) E := t + C α * z
  let tb : MvPolynomial (ULift.{v} (Fin 2)) E := t + C β * z
  let f : MvPolynomial (ULift.{v} (Fin 2)) E →ₐ[E]
      MvPolynomial (ULift.{v} (Fin 2)) E :=
    MvPolynomial.aeval (fun i : ULift.{v} (Fin 2) => ![ta, tb] i.down)
  change f (leftSecantPolynomial.{u, v} G) =
    leftMixedValue (mappedMixedCoefficients
      (C : E →+* MvPolynomial (ULift.{v} (Fin 2)) E) G) 1 ta 1 tb
  rw [leftSecantPolynomial_eq_secant_left.{u, v}]
  change f (leftMixedValue (mappedMixedCoefficients
      (C : E →+* MvPolynomial (ULift.{v} (Fin 2)) E) G) 1 t 1 z) =
    leftMixedValue (mappedMixedCoefficients
      (C : E →+* MvPolynomial (ULift.{v} (Fin 2)) E) G) 1 ta 1 tb
  simp [f, leftMixedValue, mappedMixedCoefficients, ta, tb, t, z,
    MvPolynomial.algebraMap_eq]

set_option backward.isDefEq.respectTransparency false in
theorem actualSecantB_eq_rightMixedValue (α β : E) (G : MvPolynomial (Fin 4) E) :
    actualSecantB.{u, v} α β G = rightMixedValue (mappedMixedCoefficients C G)
      1 (planeT.{u, v} + C α * planeU.{u, v}) 1 (planeT.{u, v} + C β * planeU.{u, v}) := by
  let t : MvPolynomial (ULift.{v} (Fin 2)) E := X (ULift.up 0)
  let z : MvPolynomial (ULift.{v} (Fin 2)) E := X (ULift.up 1)
  let ta : MvPolynomial (ULift.{v} (Fin 2)) E := t + C α * z
  let tb : MvPolynomial (ULift.{v} (Fin 2)) E := t + C β * z
  let f : MvPolynomial (ULift.{v} (Fin 2)) E →ₐ[E]
      MvPolynomial (ULift.{v} (Fin 2)) E :=
    MvPolynomial.aeval (fun i : ULift.{v} (Fin 2) => ![tb, ta] i.down)
  change f (rightSecantPolynomial.{u, v} G) =
    rightMixedValue (mappedMixedCoefficients
      (C : E →+* MvPolynomial (ULift.{v} (Fin 2)) E) G) 1 ta 1 tb
  rw [rightSecantPolynomial_eq_secant_right.{u, v}]
  change f (rightMixedValue (mappedMixedCoefficients
      (C : E →+* MvPolynomial (ULift.{v} (Fin 2)) E) G) 1 z 1 t) =
    rightMixedValue (mappedMixedCoefficients
      (C : E →+* MvPolynomial (ULift.{v} (Fin 2)) E) G) 1 ta 1 tb
  simp [f, rightMixedValue, mappedMixedCoefficients, ta, tb, t, z,
    MvPolynomial.algebraMap_eq]

set_option backward.isDefEq.respectTransparency false in
theorem actualSecantA_ne_zero (α β : E) (hαβ : α ≠ β)
    (G : MvPolynomial (Fin 4) E) (hA : leftSecantPolynomial.{u, v} G ≠ 0) :
    actualSecantA.{u, v} α β G ≠ 0 := by
  intro hzero
  change conjugateParameterSubstitution.{u, v} α β (leftSecantPolynomial.{u, v} G) = 0 at hzero
  apply hA
  apply conjugateParameterSubstitution_injective.{u, v} α β hαβ
  simpa only [map_zero] using hzero

set_option backward.isDefEq.respectTransparency false in
theorem actualSecantB_ne_zero (α β : E) (hαβ : α ≠ β)
    (G : MvPolynomial (Fin 4) E) (hB : rightSecantPolynomial.{u, v} G ≠ 0) :
    actualSecantB.{u, v} α β G ≠ 0 := by
  intro hzero
  change swappedConjugateParameterSubstitution.{u, v} α β (rightSecantPolynomial.{u, v} G) = 0 at hzero
  apply hB
  apply swappedConjugateParameterSubstitution_injective.{u, v} α β hαβ
  simpa only [map_zero] using hzero

theorem actualSecantProduct_ne_zero (α β : E) (hαβ : α ≠ β)
    (G : MvPolynomial (Fin 4) E)
    (hA : leftSecantPolynomial.{u, v} G ≠ 0) (hB : rightSecantPolynomial.{u, v} G ≠ 0) :
    actualSecantA.{u, v} α β G * actualSecantB.{u, v} α β G ≠ 0 :=
  mul_ne_zero (actualSecantA_ne_zero.{u, v} α β hαβ G hA)
    (actualSecantB_ne_zero.{u, v} α β hαβ G hB)

end PfaffianDescent.QuadraticSkewRationality.MixedNonvanishing
