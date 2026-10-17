import PfaffianDescent.PointCartierYonedaUnitLift
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # Canonical principal normalization of an actual rank-one extension

The scalar is extracted from the actual first map in the chosen rank-one
coordinates. Exactness then constructs the quotient endpoint and all the
commuting squares. No sequence-identification hypothesis is required.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u w

variable {R : Type u} [CommRing R]

def pointCartierNativeStalkCoordinateMap (S : ShortComplex (ModuleCat R))
    (e₁ : S.X₁ ≅ ModuleCat.of R R) (e₂ : S.X₂ ≅ ModuleCat.of R R) :
    ModuleCat.of R R ⟶ ModuleCat.of R R := e₁.inv ≫ S.f ≫ e₂.hom

def pointCartierNativeStalkScalar (S : ShortComplex (ModuleCat R))
    (e₁ : S.X₁ ≅ ModuleCat.of R R) (e₂ : S.X₂ ≅ ModuleCat.of R R) : R :=
  (pointCartierNativeStalkCoordinateMap S e₁ e₂).hom 1

theorem pointCartierNativeStalkCoordinateMap_eq_lsmul
    (S : ShortComplex (ModuleCat R))
    (e₁ : S.X₁ ≅ ModuleCat.of R R) (e₂ : S.X₂ ≅ ModuleCat.of R R) :
    pointCartierNativeStalkCoordinateMap S e₁ e₂ =
      ModuleCat.ofHom (LinearMap.lsmul R R (pointCartierNativeStalkScalar S e₁ e₂)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (pointCartierNativeStalkCoordinateMap S e₁ e₂).hom x =
    pointCartierNativeStalkScalar S e₁ e₂ * x
  have hs := (pointCartierNativeStalkCoordinateMap S e₁ e₂).hom.map_smul x (1 : R)
  simpa only [smul_eq_mul, mul_one, pointCartierNativeStalkScalar,
    LinearMap.lsmul_apply, mul_comm] using hs

theorem pointCartierNativeStalkScalar_regular (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact)
    (e₁ : S.X₁ ≅ ModuleCat.of R R) (e₂ : S.X₂ ≅ ModuleCat.of R R) :
    pointCartierNativeStalkScalar S e₁ e₂ ∈ R⁰ := by
  have : Mono S.f := hS.mono_f
  have hm : Mono (pointCartierNativeStalkCoordinateMap S e₁ e₂) := by
    dsimp [pointCartierNativeStalkCoordinateMap]
    infer_instance
  rw [pointCartierNativeStalkCoordinateMap_eq_lsmul] at hm
  have hinj := (ModuleCat.mono_iff_injective _).mp hm
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  apply hinj
  change pointCartierNativeStalkScalar S e₁ e₂ * x =
    pointCartierNativeStalkScalar S e₁ e₂ * 0
  simpa only [mul_zero] using hx

theorem pointCartierNativeStalkPrincipal_square (S : ShortComplex (ModuleCat R))
    (e₁ : S.X₁ ≅ ModuleCat.of R R) (e₂ : S.X₂ ≅ ModuleCat.of R R) :
    S.f ≫ e₂.hom = e₁.hom ≫
      (pointCartierYonedaCoefficientComplex (pointCartierNativeStalkScalar S e₁ e₂)).f := by
  change S.f ≫ e₂.hom = e₁.hom ≫
    ModuleCat.ofHom (LinearMap.lsmul R R (pointCartierNativeStalkScalar S e₁ e₂))
  have hc := pointCartierNativeStalkCoordinateMap_eq_lsmul S e₁ e₂
  change e₁.inv ≫ S.f ≫ e₂.hom = _ at hc
  rw [← cancel_epi e₁.inv]
  simpa only [Category.assoc, e₁.inv_hom_id_assoc] using hc

def pointCartierNativeStalkCokernelIso (S T : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) (hT : T.ShortExact)
    (e₁ : S.X₁ ≅ T.X₁) (e₂ : S.X₂ ≅ T.X₂)
    (hc : S.f ≫ e₂.hom = e₁.hom ≫ T.f) : S.X₃ ≅ T.X₃ :=
  CokernelCofork.mapIsoOfIsColimit hS.gIsCokernel hT.gIsCokernel
    (Arrow.isoMk e₁ e₂ hc.symm)

theorem pointCartierNativeStalkCokernelIso_square (S T : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) (hT : T.ShortExact)
    (e₁ : S.X₁ ≅ T.X₁) (e₂ : S.X₂ ≅ T.X₂)
    (hc : S.f ≫ e₂.hom = e₁.hom ≫ T.f) :
    S.g ≫ (pointCartierNativeStalkCokernelIso S T hS hT e₁ e₂ hc).hom = e₂.hom ≫ T.g := by
  dsimp only [pointCartierNativeStalkCokernelIso, CokernelCofork.mapIsoOfIsColimit,
    CokernelCofork.mapOfIsColimit]
  exact hS.gIsCokernel.fac _ WalkingParallelPair.one

def pointCartierNativeStalkQuotientIso (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact)
    (e₁ : S.X₁ ≅ ModuleCat.of R R) (e₂ : S.X₂ ≅ ModuleCat.of R R) :
    S.X₃ ≅ (pointCartierYonedaCoefficientComplex (pointCartierNativeStalkScalar S e₁ e₂)).X₃ :=
  pointCartierNativeStalkCokernelIso S
    (pointCartierYonedaCoefficientComplex (pointCartierNativeStalkScalar S e₁ e₂)) hS
    (pointCartierYonedaCoefficientComplex_shortExact _
      (pointCartierNativeStalkScalar_regular S hS e₁ e₂)) e₁ e₂
    (pointCartierNativeStalkPrincipal_square S e₁ e₂)

theorem pointCartierNativeStalkQuotientIso_square (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact)
    (e₁ : S.X₁ ≅ ModuleCat.of R R) (e₂ : S.X₂ ≅ ModuleCat.of R R) :
    S.g ≫ (pointCartierNativeStalkQuotientIso S hS e₁ e₂).hom = e₂.hom ≫
      (pointCartierYonedaCoefficientComplex (pointCartierNativeStalkScalar S e₁ e₂)).g := by
  exact pointCartierNativeStalkCokernelIso_square S _ hS
    (pointCartierYonedaCoefficientComplex_shortExact _
      (pointCartierNativeStalkScalar_regular S hS e₁ e₂)) e₁ e₂
    (pointCartierNativeStalkPrincipal_square S e₁ e₂)

/-- The entire actual short exact sequence is canonically isomorphic to the
principal coefficient sequence in its first two rank-one coordinates. -/
def pointCartierNativeStalkPrincipalIso (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact)
    (e₁ : S.X₁ ≅ ModuleCat.of R R) (e₂ : S.X₂ ≅ ModuleCat.of R R) :
    S ≅ pointCartierYonedaCoefficientComplex (pointCartierNativeStalkScalar S e₁ e₂) :=
  ShortComplex.isoMk e₁ e₂ (pointCartierNativeStalkQuotientIso S hS e₁ e₂)
    (pointCartierNativeStalkPrincipal_square S e₁ e₂).symm
    (pointCartierNativeStalkQuotientIso_square S hS e₁ e₂).symm

end PfaffianDescent
