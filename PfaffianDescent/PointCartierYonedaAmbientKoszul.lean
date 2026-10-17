import PfaffianDescent.PointCartierYonedaRegularKoszul
import PfaffianDescent.CechExtDegreeThree
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The bounded ambient point resolution

The ordinary three-parameter Koszul complex is packaged as an actual
three-step resolution in `ModuleCat`. Its only hypotheses are regularity
of the three parameters in their displayed order.
-/

noncomputable section

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u

variable {R : Type u} [CommRing R]

abbrev pointCartierYonedaAmbientPoint (f g h : R) : ModuleCat R :=
  ModuleCat.of R (R ⧸ Ideal.span ({f, g, h} : Set R))

def pointCartierYonedaAmbientAugmentation (f g h : R) :
    ModuleCat.of R R ⟶ pointCartierYonedaAmbientPoint f g h :=
  ModuleCat.ofHom (Ideal.Quotient.mkₐ R (Ideal.span ({f, g, h} : Set R))).toLinearMap

instance pointCartierYonedaAmbientAugmentation_epi (f g h : R) :
    Epi (pointCartierYonedaAmbientAugmentation f g h) :=
  (ModuleCat.epi_iff_surjective _).mpr (Ideal.Quotient.mkₐ_surjective R _)

theorem pointCartierYonedaAmbientAugmentation_zero (f g h : R) :
    ModuleCat.ofHom (threeGeneratorLast f g h) ≫
      pointCartierYonedaAmbientAugmentation f g h = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk (Ideal.span ({f, g, h} : Set R))
    (threeGeneratorLast f g h x) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← threeGeneratorLast_range]
  exact ⟨x, rfl⟩

theorem pointCartierYonedaAmbientAugmentation_exact (f g h : R) :
    (ShortComplex.mk (ModuleCat.ofHom (threeGeneratorLast f g h))
      (pointCartierYonedaAmbientAugmentation f g h)
        (pointCartierYonedaAmbientAugmentation_zero f g h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (threeGeneratorLast f g h) =
    LinearMap.ker (Ideal.Quotient.mkₐ R (Ideal.span ({f, g, h} : Set R))).toLinearMap
  rw [threeGeneratorLast_range]
  ext x
  exact Ideal.Quotient.eq_zero_iff_mem.symm

theorem pointCartierYonedaAmbientLast_zero (f g h : R) :
    ModuleCat.ofHom (threeGeneratorMiddle f g h) ≫
      ModuleCat.ofHom (threeGeneratorLast f g h) = 0 := by
  apply ModuleCat.hom_ext
  exact threeGenerator_last_comp_middle f g h

theorem pointCartierYonedaAmbientMiddle_zero (f g h : R) :
    ModuleCat.ofHom (threeGeneratorFirst f g h) ≫
      ModuleCat.ofHom (threeGeneratorMiddle f g h) = 0 := by
  apply ModuleCat.hom_ext
  exact threeGenerator_middle_comp_first f g h

theorem pointCartierYonedaAmbientLast_exact (f g h : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R)) :
    (ShortComplex.mk (ModuleCat.ofHom (threeGeneratorMiddle f g h))
      (ModuleCat.ofHom (threeGeneratorLast f g h))
        (pointCartierYonedaAmbientLast_zero f g h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact pointCartierYoneda_last_exact hf hg hh

theorem pointCartierYonedaAmbientMiddle_exact (f g h : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰) :
    (ShortComplex.mk (ModuleCat.ofHom (threeGeneratorFirst f g h))
      (ModuleCat.ofHom (threeGeneratorMiddle f g h))
        (pointCartierYonedaAmbientMiddle_zero f g h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact pointCartierYoneda_middle_exact hf hg

theorem pointCartierYonedaAmbientFirst_exact (f g h : R) (hf : f ∈ R⁰) :
    (ShortComplex.mk (0 : ModuleCat.of R PUnit ⟶ ModuleCat.of R R)
      (ModuleCat.ofHom (threeGeneratorFirst f g h)) (by simp)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (0 : PUnit →ₗ[R] R) = LinearMap.ker (threeGeneratorFirst f g h)
  rw [LinearMap.range_zero, LinearMap.ker_eq_bot.mpr (pointCartierYoneda_first_injective hf)]

def pointCartierYonedaAmbientResolution (f g h : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R)) : ThreeStepResolution (ModuleCat R) :=
  threeStepResolutionOfAugmentedChain
    (pointCartierYonedaAmbientPoint f g h) (ModuleCat.of R R)
    (ModuleCat.of R (R × R × R)) (ModuleCat.of R (R × R × R)) (ModuleCat.of R R)
    (pointCartierYonedaAmbientAugmentation f g h)
    (ModuleCat.ofHom (threeGeneratorLast f g h))
    (ModuleCat.ofHom (threeGeneratorMiddle f g h))
    (ModuleCat.ofHom (threeGeneratorFirst f g h))
    (pointCartierYonedaAmbientAugmentation_zero f g h)
    (pointCartierYonedaAmbientLast_zero f g h)
    (pointCartierYonedaAmbientMiddle_zero f g h)
    (pointCartierYonedaAmbientAugmentation_exact f g h)
    (pointCartierYonedaAmbientLast_exact f g h hf hg hh)
    (pointCartierYonedaAmbientMiddle_exact f g h hf hg)

end PfaffianDescent
