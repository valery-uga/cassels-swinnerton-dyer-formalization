import PfaffianDescent.PointCartierYonedaSurfaceKoszul
import PfaffianDescent.PointCartierYonedaUnitLift
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! The first Cartier boundary of a literal principal curve-point extension.
This is a ring-local calculation. It does not identify the original global
point-dual sequence with this principal sequence, or compute a global trace.
SOURCE ONLY; no compiler check has been run by the source worker. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors
universe u v w w'

/-- The degree-one version of the existing degree-two coefficient-lift
calculation. The inputs are ordinary maps and lift squares. -/
theorem TwoStepResolution.first_connecting_comp_coefficient_extension188
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    (T : TwoStepResolution C) (S : ShortComplex C) (hS : S.ShortExact)
    (phi : T.K₀ ⟶ S.X₃) (l : T.C₁ ⟶ S.X₂) (psi : T.K₁ ⟶ S.X₁)
    (hleft : T.i₁ ≫ l = psi ≫ S.f)
    (hright : T.p₁ ≫ phi = l ≫ S.g) :
    (T.exact₀.extClass.comp (Ext.mk₀ phi) (add_zero 1)).comp
      hS.extClass (show 1 + 1 = 2 by rfl) = T.connecting S.X₁ psi := by
  let a : T.S₁ ⟶ S :=
    { τ₁ := psi, τ₂ := l, τ₃ := phi,
      comm₁₂ := hleft.symm, comm₂₃ := hright.symm }
  have hn := T.exact₁.extClass_naturality hS a
  change T.exact₁.extClass.comp (Ext.mk₀ psi) (add_zero 1) =
    (Ext.mk₀ phi).comp hS.extClass (zero_add 1) at hn
  rw [Ext.comp_assoc_of_second_deg_zero, ← hn]
  rfl

/-- The literal parameter extension over R/(f), after restriction to R,
followed by the principal f-boundary is the regular two-parameter class
with coefficient one. The quotient augmentation and its projection square
are constructed internally from the two actual cokernel sequences. -/
theorem firstCartierPrincipalParameter_boundary188
    {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat R)]
    (f g : R) [HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {f}))]
    (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰) :
    ∃ kappa : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶
        (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
          (pointCartierYonedaCoefficientComplex
            (Ideal.Quotient.mk (Ideal.span {f}) g)).X₃,
      (localSerreIdealQuotientComplex f g).g ≫ kappa =
        (pointCartierYonedaCoefficientComplex f).g ≫
          (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).map
            (pointCartierYonedaCoefficientComplex
              (Ideal.Quotient.mk (Ideal.span {f}) g)).g ∧
      ((Ext.mk₀ kappa).comp
          (((pointCartierYonedaCoefficientComplex_shortExact
            (Ideal.Quotient.mk (Ideal.span {f}) g) hg).extClass).mapExactFunctor
              (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))))
          (zero_add 1)).comp
        (pointCartierYonedaCoefficientComplex_shortExact f hf).extClass
        (show 1 + 1 = 2 by rfl) = localSerreExtTwoClass f g 1 hf hg := by
  let T := pointCartierYonedaSurfaceResolution f g hf hg
  let S := pointCartierYonedaCoefficientComplex f
  let hS := pointCartierYonedaCoefficientComplex_shortExact f hf
  let q := Ideal.Quotient.mk (Ideal.span {f})
  have hqf : q f = 0 := Ideal.Quotient.mk_singleton_self f
  let F := ModuleCat.restrictScalars q
  let V := pointCartierYonedaCoefficientComplex (q g)
  let U := V.map F
  have hU : U.ShortExact :=
    (pointCartierYonedaCoefficientComplex_shortExact (q g) hg).map_of_exact F
  let l : T.C₁ ⟶ S.X₂ := ModuleCat.ofHom (LinearMap.snd R R R)
  have hz : T.i₁ ≫ (l ≫ S.g) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change R at x
    change q (x * f) = 0
    rw [map_mul, hqf, mul_zero]
  let phi : T.K₀ ⟶ S.X₃ :=
    T.exact₁.gIsCokernel.desc (CokernelCofork.ofπ (l ≫ S.g) hz)
  have hright : T.p₁ ≫ phi = l ≫ S.g :=
    T.exact₁.gIsCokernel.fac _ WalkingParallelPair.one
  have hleft : T.i₁ ≫ l = (𝟙 (ModuleCat.of R R)) ≫ S.f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change R at x
    change x * f = f * x
    exact mul_comm _ _
  have hpoint : T.i₀ ≫ S.g = phi ≫ U.f := by
    letI : Epi T.p₁ := T.exact₁.epi_g
    apply (cancel_epi T.p₁).1
    rw [← Category.assoc T.p₁ phi, hright]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change q (x.1 * f + x.2 * g) = q g * q x.2
    simp only [map_add, map_mul, hqf,
      mul_zero, zero_add]
    exact mul_comm _ _
  have hz0 : T.i₀ ≫ (S.g ≫ U.g) = 0 := by
    rw [← Category.assoc, hpoint, Category.assoc, U.zero, comp_zero]
  let kappa : T.P ⟶ U.X₃ :=
    T.exact₀.gIsCokernel.desc (CokernelCofork.ofπ (S.g ≫ U.g) hz0)
  have hk : T.p₀ ≫ kappa = S.g ≫ U.g :=
    T.exact₀.gIsCokernel.fac _ WalkingParallelPair.one
  let a : T.S₀ ⟶ U :=
    { τ₁ := phi, τ₂ := S.g, τ₃ := kappa,
      comm₁₂ := hpoint.symm, comm₂₃ := hk.symm }
  have hn := T.exact₀.extClass_naturality hU a
  change T.exact₀.extClass.comp (Ext.mk₀ phi) (add_zero 1) =
    (Ext.mk₀ kappa).comp hU.extClass (zero_add 1) at hn
  have hb := T.first_connecting_comp_coefficient_extension188
    S hS phi l (𝟙 (ModuleCat.of R R)) hleft hright
  have hi : (𝟙 (ModuleCat.of R R)) =
      ModuleCat.ofHom (LinearMap.lsmul R R (1 : R)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x = 1 * x
    exact (one_mul x).symm
  rw [hi] at hb
  change _ = (pointCartierYonedaSurfaceResolution f g hf hg).connecting
    (ModuleCat.of R R) (ModuleCat.ofHom (LinearMap.lsmul R R 1)) at hb
  rw [pointCartierYonedaSurfaceResolution_connecting] at hb
  refine ⟨kappa, hk, ?_⟩
  rw [Ext.mapExactFunctor_extClass]
  change ((Ext.mk₀ kappa).comp hU.extClass (zero_add 1)).comp
    hS.extClass (show 1 + 1 = 2 by rfl) = _
  rw [← hn]
  exact hb

end PfaffianDescent
