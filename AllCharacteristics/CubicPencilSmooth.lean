import AllCharacteristics.CubicPencil
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Smoothness of the generic member of a cubic pencil

If the right endpoint of a pencil of cubic surfaces is nonzero and smooth,
then its generic member over `k(t)` is nonzero and smooth.  The proof uses the
universal open smooth locus: the generic point of `Spec k[t]` generalizes the
point `t = 1`, so every open containing the latter contains the former.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
open UniversalHomogeneous HomogeneousProjective

universe u
attribute [local instance] PrimeSpectrum.isPrime
variable {k : Type u} [Field k]

/-- Every injective field-valued specialization of `k[t]` sends the pencil to
the universal nonzero smooth parameter open whenever its right endpoint is
nonzero and smooth.  Injectivity says that the specialization is a generic
point rather than a closed value of the pencil parameter. -/
theorem cubicPencil_map_parameter_mem
    {K : Type u} [Field K] (g : Polynomial k →+* K) (hg : Function.Injective g)
    {p q : MvPolynomial (Fin 4) k} (hq : q.IsHomogeneous 3) (hq0 : q ≠ 0)
    [Smooth (hypersurfaceToBase q hq)] :
    equationParameter
        (g.comp Polynomial.C) ((cubicPencil p q).map g)
        (IsLocalRing.closedPoint K) ∈
      nonzeroSmoothParameterOpen k (Fin 4) 3 := by
  let P : MvPolynomial (Fin 4) (Polynomial k) := cubicPencil p q
  let cA : Coefficients (Fin 4) 3 k →+* Polynomial k :=
    MvPolynomial.eval₂Hom Polynomial.C
      (fun m : Monomials (Fin 4) 3 ↦ P.coeff m.1)
  let e₁ : Polynomial k →+* k := Polynomial.evalRingHom 1
  let x₁ : PrimeSpectrum (Polynomial k) :=
    PrimeSpectrum.comap e₁ (IsLocalRing.closedPoint k)
  let η : PrimeSpectrum (Polynomial k) :=
    PrimeSpectrum.comap g (IsLocalRing.closedPoint K)

  have he₁C : e₁.comp Polynomial.C = RingHom.id k := by
    ext r
    simp [e₁]
  have he₁cA : e₁.comp cA = coefficientSpecialization (d := 3) (RingHom.id k) q := by
    have h := UniversalHomogeneous.coefficientEvaluation_comp
      (d := 3) Polynomial.C P e₁
    rw [he₁C, cubicPencil_map_eval_one] at h
    simpa [cA, P, coefficientSpecialization] using h
  have hx₁ : PrimeSpectrum.comap cA x₁ ∈
      nonzeroSmoothParameterOpen k (Fin 4) 3 := by
    have hqmem := (equationParameter_mem_nonzeroSmooth_iff
      (d := 3) (RingHom.id k) q hq).2 ⟨hq0, inferInstance⟩
    change PrimeSpectrum.comap cA
        (PrimeSpectrum.comap e₁ (IsLocalRing.closedPoint k)) ∈ _
    rw [← PrimeSpectrum.comap_comp_apply, he₁cA]
    exact hqmem

  have hηideal : η.asIdeal = ⊥ := by
    rw [show η.asIdeal = RingHom.ker g from fieldPoint_asIdeal_eq_ker g]
    exact (RingHom.injective_iff_ker_eq_bot g).mp hg
  have hηle : η ≤ x₁ := by
    rw [← PrimeSpectrum.asIdeal_le_asIdeal, hηideal]
    exact bot_le
  have hspec : Specializes η x₁ :=
    (PrimeSpectrum.le_iff_specializes η x₁).mp hηle
  have hgeneric : PrimeSpectrum.comap cA η ∈
      nonzeroSmoothParameterOpen k (Fin 4) 3 :=
    (hspec.map (PrimeSpectrum.continuous_comap cA)).mem_open
      (nonzeroSmoothParameterOpen k (Fin 4) 3).2 hx₁

  have hgcA : g.comp cA =
      coefficientSpecialization (d := 3) (g.comp Polynomial.C) (P.map g) := by
    simpa [cA, coefficientSpecialization] using
      (UniversalHomogeneous.coefficientEvaluation_comp
        (d := 3) Polynomial.C P g)
  change PrimeSpectrum.comap
      (coefficientSpecialization (d := 3) (g.comp Polynomial.C) (P.map g))
      (IsLocalRing.closedPoint K) ∈ _
  rw [← hgcA, PrimeSpectrum.comap_comp_apply]
  exact hgeneric

/-- The generic member over the canonical fraction field belongs to the
universal nonzero smooth parameter open. -/
theorem cubicPencil_generic_parameter_mem
    {p q : MvPolynomial (Fin 4) k}
    (hq : q.IsHomogeneous 3) (hq0 : q ≠ 0)
    [Smooth (hypersurfaceToBase q hq)] :
    equationParameter
        ((algebraMap (Polynomial k) (FractionRing (Polynomial k))).comp Polynomial.C)
        ((cubicPencil p q).map
          (algebraMap (Polynomial k) (FractionRing (Polynomial k))))
        (IsLocalRing.closedPoint (FractionRing (Polynomial k))) ∈
      nonzeroSmoothParameterOpen k (Fin 4) 3 :=
  cubicPencil_map_parameter_mem
    (algebraMap (Polynomial k) (FractionRing (Polynomial k)))
    (FaithfulSMul.algebraMap_injective (Polynomial k) (FractionRing (Polynomial k)))
    hq hq0

/-- Every injective field-valued specialization of the pencil parameter has
a nonzero smooth projective hypersurface. -/
theorem cubicPencil_map_smooth
    {K : Type u} [Field K] (g : Polynomial k →+* K) (hg : Function.Injective g)
    {p q : MvPolynomial (Fin 4) k}
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hq0 : q ≠ 0)
    [Smooth (hypersurfaceToBase q hq)] :
    Smooth (hypersurfaceToBase ((cubicPencil p q).map g)
      ((cubicPencil_isHomogeneous hp hq).map g)) := by
  exact ((equationParameter_mem_nonzeroSmooth_iff (d := 3)
    (g.comp Polynomial.C) ((cubicPencil p q).map g)
    ((cubicPencil_isHomogeneous hp hq).map g)).1
      (cubicPencil_map_parameter_mem g hg hq hq0)).2

/-- A pencil with a nonzero smooth right endpoint has a nonzero smooth
generic cubic surface over `k(t)`. -/
theorem cubicPencil_generic_smooth
    {p q : MvPolynomial (Fin 4) k}
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hq0 : q ≠ 0)
    [Smooth (hypersurfaceToBase q hq)] :
    Smooth (hypersurfaceToBase
      ((cubicPencil p q).map
        (algebraMap (Polynomial k) (FractionRing (Polynomial k))))
      ((cubicPencil_isHomogeneous hp hq).map
        (algebraMap (Polynomial k) (FractionRing (Polynomial k))))) := by
  exact cubicPencil_map_smooth
    (algebraMap (Polynomial k) (FractionRing (Polynomial k)))
    (FaithfulSMul.algebraMap_injective (Polynomial k) (FractionRing (Polynomial k)))
    hp hq hq0

end AllCharacteristics
