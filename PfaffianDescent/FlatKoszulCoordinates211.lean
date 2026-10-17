import PfaffianDescent.PointKoszulFlatBaseChangeTensor
import PfaffianDescent.FlatIdealBaseChange
import PfaffianDescent.LocalSerreExtensionPresentation

/-! Source candidate: canonical flat transport of both actual Koszul short
complexes. No comparison of extension classes is an input. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TensorProduct
open scoped ChangeOfRings nonZeroDivisors
namespace PfaffianDescent
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def flatKoszulIdealIso211 (φ : R →+* S) (hφ : φ.Flat) (f g : R) :
    (ModuleCat.extendScalars φ).obj
      (ModuleCat.of R (Ideal.span ({f, g} : Set R))) ≅
        ModuleCat.of S (Ideal.span ({φ f, φ g} : Set S)) := by
  letI : Algebra R S := φ.toAlgebra
  exact ((idealFlatBaseChangeLinearEquiv φ hφ _).trans
    (LinearEquiv.ofEq _ _ (by rw [Ideal.map_span, Set.image_pair]))).toModuleIso

theorem flatKoszulIdealIso211_tmul
    (φ : R →+* S) (hφ : φ.Flat) (f g : R) (s : S)
    (x : Ideal.span ({f, g} : Set R)) :
    ((flatKoszulIdealIso211 φ hφ f g).hom (s ⊗ₜ[R,φ] x) : S) =
      s * φ x.1 := by
  letI : Algebra R S := φ.toAlgebra
  change ((idealFlatBaseChangeLinearEquiv φ hφ _) (s ⊗ₜ[R] x) : S) = _
  exact idealFlatBaseChangeLinearEquiv_tmul φ hφ _ s x

set_option backward.isDefEq.respectTransparency false in
theorem flatKoszulRelation_square211 (φ : R →+* S) (f g : R) :
    (ModuleCat.extendScalars φ).map (ModuleCat.ofHom (localKoszulRelationMap f g)) ≫
        (pointKoszulFlatBaseChangePairIso φ).hom =
      (pointKoszulFlatBaseChangeFreeIso φ).hom ≫
        ModuleCat.ofHom (localKoszulRelationMap (φ f) (φ g)) := by
  letI : Algebra R S := φ.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact (LinearMap.map_zero _).trans (LinearMap.map_zero _).symm
  | add x y hx hy =>
      exact (LinearMap.map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (LinearMap.map_add _ _ _).symm)
  | tmul s r =>
      change S at s
      change R at r
      change (pointKoszulFlatBaseChangePairIso φ).hom
          ((ModuleCat.extendScalars φ).map (ModuleCat.ofHom (localKoszulRelationMap f g))
            (s ⊗ₜ[R,φ] r)) =
        localKoszulRelationMap (φ f) (φ g)
          ((pointKoszulFlatBaseChangeFreeIso φ).hom (s ⊗ₜ[R,φ] r))
      erw [ModuleCat.ExtendScalars.map_tmul, pointKoszulFlatBaseChangePairIso_tmul,
        pointKoszulFlatBaseChangeFreeIso_tmul]
      ext <;> simp [localKoszulRelationMap, smul_eq_mul, map_mul, map_neg] <;> ring

set_option backward.isDefEq.respectTransparency false in
theorem flatKoszulGenerators_square211
    (φ : R →+* S) (hφ : φ.Flat) (f g : R) :
    (ModuleCat.extendScalars φ).map (ModuleCat.ofHom (localKoszulToIdeal f g)) ≫
        (flatKoszulIdealIso211 φ hφ f g).hom =
      (pointKoszulFlatBaseChangePairIso φ).hom ≫
        ModuleCat.ofHom (localKoszulToIdeal (φ f) (φ g)) := by
  letI : Algebra R S := φ.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact (LinearMap.map_zero _).trans (LinearMap.map_zero _).symm
  | add x y hx hy =>
      exact (LinearMap.map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (LinearMap.map_add _ _ _).symm)
  | tmul s v =>
      change S at s
      change R × R at v
      apply Subtype.ext
      change ((flatKoszulIdealIso211 φ hφ f g).hom
          ((ModuleCat.extendScalars φ).map (ModuleCat.ofHom (localKoszulToIdeal f g))
            (s ⊗ₜ[R,φ] v)) : S) =
        (localKoszulToIdeal (φ f) (φ g)
          ((pointKoszulFlatBaseChangePairIso φ).hom (s ⊗ₜ[R,φ] v)) : S)
      erw [ModuleCat.ExtendScalars.map_tmul, flatKoszulIdealIso211_tmul,
        pointKoszulFlatBaseChangePairIso_tmul]
      change s * φ (v.1 * f + v.2 * g) = (s * φ v.1) * φ f + (s * φ v.2) * φ g
      simp only [map_add, map_mul]
      ring

set_option backward.isDefEq.respectTransparency false in
theorem flatKoszulInclusion_square211
    (φ : R →+* S) (hφ : φ.Flat) (f g : R) :
    (ModuleCat.extendScalars φ).map
        (ModuleCat.ofHom (Ideal.span ({f, g} : Set R)).subtype) ≫
        (pointKoszulFlatBaseChangeFreeIso φ).hom =
      (flatKoszulIdealIso211 φ hφ f g).hom ≫
        ModuleCat.ofHom (Ideal.span ({φ f, φ g} : Set S)).subtype := by
  letI : Algebra R S := φ.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact (LinearMap.map_zero _).trans (LinearMap.map_zero _).symm
  | add x y hx hy =>
      exact (LinearMap.map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (LinearMap.map_add _ _ _).symm)
  | tmul s v =>
      change S at s
      change Ideal.span ({f, g} : Set R) at v
      change (pointKoszulFlatBaseChangeFreeIso φ).hom (s ⊗ₜ[R,φ] v.1) =
        ((flatKoszulIdealIso211 φ hφ f g).hom (s ⊗ₜ[R,φ] v) : S)
      exact (pointKoszulFlatBaseChangeFreeIso_tmul φ s v.1).trans
        (flatKoszulIdealIso211_tmul φ hφ f g s v).symm

set_option backward.isDefEq.respectTransparency false in
theorem flatKoszulQuotient_square211 (φ : R →+* S) (f g : R) :
    (ModuleCat.extendScalars φ).map (localSerreIdealQuotientComplex f g).g ≫
        (pointKoszulFlatBaseChangePointIso φ f g).hom =
      (pointKoszulFlatBaseChangeFreeIso φ).hom ≫
        (localSerreIdealQuotientComplex (φ f) (φ g)).g := by
  letI : Algebra R S := φ.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact (LinearMap.map_zero _).trans (LinearMap.map_zero _).symm
  | add x y hx hy =>
      exact (LinearMap.map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (LinearMap.map_add _ _ _).symm)
  | tmul s r =>
      change S at s
      change R at r
      change (pointKoszulFlatBaseChangePointIso φ f g).hom
          ((ModuleCat.extendScalars φ).map (localSerreIdealQuotientComplex f g).g
            (s ⊗ₜ[R,φ] r)) =
        Ideal.Quotient.mk (Ideal.span ({φ f, φ g} : Set S))
          ((pointKoszulFlatBaseChangeFreeIso φ).hom (s ⊗ₜ[R,φ] r))
      erw [ModuleCat.ExtendScalars.map_tmul, pointKoszulFlatBaseChangeFreeIso_tmul]
      exact pointKoszulFlatBaseChangePointIso_tmul φ f g s r

set_option backward.isDefEq.respectTransparency false in
theorem flatKoszulCoefficient_square211 (φ : R →+* S) (c : R) :
    (ModuleCat.extendScalars φ).map (ModuleCat.ofHom (LinearMap.lsmul R R c)) ≫
        (pointKoszulFlatBaseChangeFreeIso φ).hom =
      (pointKoszulFlatBaseChangeFreeIso φ).hom ≫
        ModuleCat.ofHom (LinearMap.lsmul S S (φ c)) := by
  letI : Algebra R S := φ.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact (LinearMap.map_zero _).trans (LinearMap.map_zero _).symm
  | add x y hx hy =>
      exact (LinearMap.map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (LinearMap.map_add _ _ _).symm)
  | tmul s r =>
      change S at s
      change R at r
      change (pointKoszulFlatBaseChangeFreeIso φ).hom (s ⊗ₜ[R,φ] (c * r)) =
        (φ c) * ((pointKoszulFlatBaseChangeFreeIso φ).hom (s ⊗ₜ[R,φ] r))
      rw [pointKoszulFlatBaseChangeFreeIso_tmul φ s (c * r),
        pointKoszulFlatBaseChangeFreeIso_tmul φ s r]
      change s * φ (c * r) = φ c * (s * φ r)
      rw [map_mul]
      ring

def flatKoszulIdealComparison211 (φ : R →+* S) (hφ : φ.Flat) (f g : R) :
    (localKoszulIdealComplex f g).map (ModuleCat.extendScalars φ) ⟶
      localKoszulIdealComplex (φ f) (φ g) :=
  ShortComplex.homMk (pointKoszulFlatBaseChangeFreeIso φ).hom
    (pointKoszulFlatBaseChangePairIso φ).hom (flatKoszulIdealIso211 φ hφ f g).hom
    (flatKoszulRelation_square211 φ f g).symm
    (flatKoszulGenerators_square211 φ hφ f g).symm

def flatKoszulQuotientComparison211 (φ : R →+* S) (hφ : φ.Flat) (f g : R) :
    (localSerreIdealQuotientComplex f g).map (ModuleCat.extendScalars φ) ⟶
      localSerreIdealQuotientComplex (φ f) (φ g) :=
  ShortComplex.homMk (flatKoszulIdealIso211 φ hφ f g).hom
    (pointKoszulFlatBaseChangeFreeIso φ).hom (pointKoszulFlatBaseChangePointIso φ f g).hom
    (flatKoszulInclusion_square211 φ hφ f g).symm
    (flatKoszulQuotient_square211 φ f g).symm

end PfaffianDescent
