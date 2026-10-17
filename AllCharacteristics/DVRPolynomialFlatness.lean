import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Flat polynomial hypersurfaces over a discrete valuation ring

If a polynomial has nonzero reduction, its principal ideal is saturated with
respect to a uniformizer. The quotient has no coefficient-ring torsion and is
therefore flat over the DVR. This applies without a monic equation, a rational
point outside the hypersurface, or any restriction on the residue characteristic.
-/

open IsLocalRing MvPolynomial
namespace AllCharacteristics
universe u v

/-- Over a DVR, injectivity of a uniformizer on a module implies that the
module is torsion-free. -/
theorem isTorsionFree_of_uniformizer_regular
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (π : R) (hπ : Irreducible π) (hreg : IsSMulRegular M π) :
    Module.IsTorsionFree R M := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r m hm
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    obtain ⟨n, a, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hπ
    exact ((a.isSMulRegular M).mul (IsSMulRegular.pow n hreg)).right_eq_zero_of_smul hm

/-- A polynomial with nonzero residue equation generates an ideal saturated
with respect to a generator of the coefficient ring's maximal ideal. -/
theorem polynomial_equation_saturated_uniformizer
    {R : Type u} {σ : Type v} [CommRing R] [IsDomain R] [IsLocalRing R]
    (π : R) (hπ : π ≠ 0) (hm : maximalIdeal R = Ideal.span {π})
    (p : MvPolynomial σ R) (hp : p.map (residue R) ≠ 0)
    (g : MvPolynomial σ R) (hg : p ∣ C π * g) : p ∣ g := by
  have hres : ∀ r : R, residue R r = 0 ↔ π ∣ r := by
    intro r
    change Ideal.Quotient.mk (maximalIdeal R) r = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, hm, Ideal.mem_span_singleton]
  obtain ⟨a, ha⟩ := hg
  have ha0 : p.map (residue R) * a.map (residue R) = 0 := by
    rw [← map_mul, ← ha, map_mul, map_C, (hres π).mpr dvd_rfl, map_zero, zero_mul]
  have hadiv : C π ∣ a :=
    (C_dvd_iff_map_hom_eq_zero (residue R) π hres a).mpr
      ((mul_eq_zero.mp ha0).resolve_left hp)
  obtain ⟨a', ha'⟩ := hadiv
  refine ⟨a', ?_⟩
  apply mul_left_cancel₀ (show C π ≠ (0 : MvPolynomial σ R) by simpa using hπ)
  calc
    C π * g = p * a := ha
    _ = p * (C π * a') := congrArg (p * ·) ha'
    _ = C π * (p * a') := by ac_rfl

/-- The uniformizer acts injectively on the polynomial hypersurface quotient
when the residue equation is nonzero. -/
theorem polynomial_quotient_uniformizer_regular
    {R : Type u} {σ : Type v} [CommRing R] [IsDomain R] [IsLocalRing R]
    (π : R) (hπ : π ≠ 0) (hm : maximalIdeal R = Ideal.span {π})
    (p : MvPolynomial σ R) (hp : p.map (residue R) ≠ 0) :
    IsSMulRegular (MvPolynomial σ R ⧸ Ideal.span {p}) π := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro z hz
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  apply polynomial_equation_saturated_uniformizer π hπ hm p hp g
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [← smul_eq_C_mul]
  exact ((Ideal.Quotient.mkₐ R (Ideal.span {p})).toLinearMap.map_smul π g).trans hz

/-- The polynomial quotient of a nonzero residue equation is torsion-free
over the discrete valuation coefficient ring. -/
theorem polynomial_quotient_isTorsionFree_of_nonzero_reduction
    {R : Type u} {σ : Type v} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (p : MvPolynomial σ R) (hp : p.map (residue R) ≠ 0) :
    Module.IsTorsionFree R (MvPolynomial σ R ⧸ Ideal.span {p}) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact isTorsionFree_of_uniformizer_regular π hπ
    (polynomial_quotient_uniformizer_regular π hπ.ne_zero hπ.maximalIdeal_eq p hp)

/-- A polynomial hypersurface whose residue equation is nonzero is flat over
the discrete valuation coefficient ring. -/
theorem polynomial_quotient_flat_of_nonzero_reduction
    {R : Type u} {σ : Type v} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (p : MvPolynomial σ R) (hp : p.map (residue R) ≠ 0) :
    Module.Flat R (MvPolynomial σ R ⧸ Ideal.span {p}) := by
  have := polynomial_quotient_isTorsionFree_of_nonzero_reduction p hp
  infer_instance

end AllCharacteristics
