import PfaffianDescent.VoisinPositiveTwistTriviality
import AllCharacteristics.HomogeneousProjectiveAmbient
import PfaffianDescent.SchemeModuleGlobalSections
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentExactKernelLinearEquiv

/- SOURCE-ONLY, UNVERIFIED. These are actual morphism-valued global
sections, not a polynomial space renamed H0. The final P3 lemma derives its
short exact sequence internally from the four actual positive-twist charts.
No finite/reduced/single-chart hypothesis is used. The homogeneous
polynomial-to-restriction-kernel comparison is a separate remaining task. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Left exactness of actual global sections, as a linear kernel equivalence. -/
def shortExactActualGlobalSectionsKernelEquiv
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) :
    SchemeModuleGlobalSectionsOver base S.X₁ ≃ₗ[K]
      (schemeModuleGlobalSectionsMap base S.g).ker := by
  let a := schemeModuleGlobalSectionsMap base S.f
  let r := schemeModuleGlobalSectionsMap base S.g
  letI : Mono S.f := hS.mono_f
  have ha : Function.Injective a := by
    intro s t h
    exact (cancel_mono S.f).mp h
  have hz : ∀ s, r (a s) = 0 := by
    intro s
    change schemeModuleUnit X ⟶ S.X₁ at s
    change (s ≫ S.f) ≫ S.g = 0
    rw [Category.assoc, S.zero, comp_zero]
  have hlift : ∀ s, r s = 0 → ∃ t, a t = s := by
    intro s hs
    have hs' : s ≫ S.g = 0 := hs
    let fork := KernelFork.ofι s hs'
    refine ⟨hS.fIsKernel.lift fork, ?_⟩
    exact hS.fIsKernel.fac fork WalkingParallelPair.zero
  exact cubicClosedPointSerreSurfaceJetCotangent_exactKernelLinearEquiv a r ha hz hlift

/-- The actual restriction of a positive-twist section to the actual
closed-subscheme quotient. The tensor unit isomorphism fixes the source
as O(m), rather than O tensor O(m). -/
def p3ClosedImmersionPositiveRestriction
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [IsClosedImmersion i] (m : ℕ) :=
  let T := positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) m
  (schemeModuleTensorUnitLeftIso T).inv ≫ (closedImmersionIdealTwistSequence i T).g

/-- Actual ideal sheaf global sections identify with the kernel of the
actual restriction map on global O(m) sections, for every closed subscheme
of P3. In particular, this is a prerequisite for the literal H0(I_Z(2))
dictionary and it preserves arbitrary nonreduced Z. -/
def p3ClosedImmersionPositiveIdealGlobalKernelEquiv
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [IsClosedImmersion i] (m : ℕ) (hm : 0 < m) :
    SchemeModuleGlobalSectionsOver
      (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) m)) ≃ₗ[K]
      (schemeModuleGlobalSectionsMap
        (ambientToBase (R := K) (σ := Fin 4))
        (p3ClosedImmersionPositiveRestriction i m)).ker := by
  let PS := MvPolynomial.homogeneousSubmodule (Fin 4) K
  let T := positiveSheafOfModules PS m
  let S := closedImmersionIdealTwistSequence i T
  let base := ambientToBase (R := K) (σ := Fin 4)
  let u : S.X₂ ≅ T := schemeModuleTensorUnitLeftIso T
  letI : PreservesFiniteLimits (schemeModuleTensorRight T) :=
    p3PositiveTwist_tensorRight_preservesFiniteLimits K m hm
  letI : PreservesFiniteColimits (schemeModuleTensorRight T) :=
    p3PositiveTwist_tensorRight_preservesFiniteColimits K m hm
  have hS : S.ShortExact := closedImmersionIdealTwistSequence_shortExact i T
  letI : Mono S.f := hS.mono_f
  let a := schemeModuleGlobalSectionsMap base (S.f ≫ u.hom)
  let r := schemeModuleGlobalSectionsMap base (u.inv ≫ S.g)
  have ha : Function.Injective a := by
    intro s t h
    exact (cancel_mono (S.f ≫ u.hom)).mp h
  have hz : ∀ s, r (a s) = 0 := by
    intro s
    change schemeModuleUnit _ ⟶ S.X₁ at s
    change (s ≫ (S.f ≫ u.hom)) ≫ (u.inv ≫ S.g) = 0
    simp only [Category.assoc, Iso.hom_inv_id_assoc, S.zero, comp_zero]
  have hlift : ∀ s, r s = 0 → ∃ t, a t = s := by
    intro s hs
    change schemeModuleUnit (Proj PS) ⟶ T at s
    change s ≫ (u.inv ≫ S.g) = 0 at hs
    have hs' : (s ≫ u.inv) ≫ S.g = 0 := by
      simpa only [Category.assoc] using hs
    let fork := KernelFork.ofι (s ≫ u.inv) hs'
    let t : schemeModuleUnit (Proj PS) ⟶ S.X₁ := hS.fIsKernel.lift fork
    have ht : t ≫ S.f = s ≫ u.inv :=
      hS.fIsKernel.fac fork WalkingParallelPair.zero
    refine ⟨t, ?_⟩
    change t ≫ (S.f ≫ u.hom) = s
    rw [← Category.assoc, ht, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact cubicClosedPointSerreSurfaceJetCotangent_exactKernelLinearEquiv a r ha hz hlift

end PfaffianDescent
