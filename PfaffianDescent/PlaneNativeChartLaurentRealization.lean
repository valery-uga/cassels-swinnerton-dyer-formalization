import PfaffianDescent.PlaneNativeChartFrames
import PfaffianDescent.PlaneTwistLaurent
/-! SOURCE ONLY / UNCHECKED: genuinely derived actual positive and negative
chart-section Laurent representatives, with injectivity and exact supported
range. The maps are defined on actual native sheaf sections. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open ProjectiveNegativeTwist PlaneLaurentLocalization PlaneTwistLaurent
open scoped AddMonoidAlgebra BigOperators
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K

abbrev p2CechBasicOpen (n : ℕ) (f : Fin (n + 1) → Fin 3) :
    Scheme.Opens (Proj PS) := Proj.basicOpen PS (p2CechDenominator (K := K) n f)

abbrev p2PositiveTwistChartAway (n : ℕ) (f : Fin (n + 1) → Fin 3)
    (m : ℕ) (i : Fin 3) (hi : MvPolynomial.X i ∣ p2CechDenominator (K := K) n f)
    (s : Γ(positiveSheafOfModules PS m, p2CechBasicOpen K n f)) :
    HomogeneousLocalization.Away PS (p2CechDenominator (K := K) n f) :=
  (p2PositiveTwistBasicOpenIsoAway K (p2CechDenominator (K := K) n f)
    (n + 1) (p2CechDenominator_mem (K := K) n f) (Nat.succ_pos n) i hi m).hom s

private def p2PositiveAwayToLaurent
    (m n : ℕ) (f : Fin (n + 1) → Fin 3) :
    HomogeneousLocalization.Away PS (p2CechDenominator (K := K) n f) →+
      PlaneLaurentLocalization.LaurentPolynomial K where
  toFun z := awayToLaurent (K := K) n f z *
    AddMonoidAlgebra.single (positiveTwistShift m (f 0)) 1
  map_zero' := by simp
  map_add' x y := by simp [add_mul]

private theorem p2PositiveAwayToLaurent_injective
    (m n : ℕ) (f : Fin (n + 1) → Fin 3) :
    Function.Injective (p2PositiveAwayToLaurent K m n f) := by
  intro x y h
  apply awayToLaurent_injective (K := K) n f
  exact (isUnit_single_one (K := K) (positiveTwistShift m (f 0))).mul_right_cancel h

private theorem p2PositiveAwayToLaurent_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 3)
    (z : HomogeneousLocalization.Away PS (p2CechDenominator (K := K) n f)) :
    ∀ a ∈ (p2PositiveAwayToLaurent K m n f z).coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ :=
    (mul_single_mem_support_iff (K := K)
      (awayToLaurent (K := K) n f z) (positiveTwistShift m (f 0)) a).mp ha
  have hbase := awayToLaurent_support_properties (K := K) n f z b hb
  constructor
  · rw [totalDegree_add, hbase.1, totalDegree_positiveTwistShift]
    simp
  · exact (negativeSupport_add_positiveTwistShift_subset m (f 0) b).trans hbase.2

private theorem exists_p2PositiveAwayToLaurent_eq_of_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 3)
    (g : PlaneLaurentLocalization.LaurentPolynomial K)
    (hg : ∀ a ∈ g.coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ Set.range f) :
    ∃ z : HomogeneousLocalization.Away PS (p2CechDenominator (K := K) n f),
      p2PositiveAwayToLaurent K m n f z = g := by
  let gneg := g * AddMonoidAlgebra.single (twistShift m (f 0)) 1
  have hgneg : ∀ a ∈ gneg.coeff.support,
      totalDegree a = 0 ∧ negativeSupport a ⊆ Set.range f := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ :=
      (mul_single_mem_support_iff (K := K) g (twistShift m (f 0)) a).mp ha
    have hbase := hg b hb
    constructor
    · rw [totalDegree_add, hbase.1, totalDegree_twistShift]
      simp
    · exact negativeSupport_add_twistShift_subset n m f b hbase.2
  obtain ⟨z, hz⟩ := exists_awayToLaurent_eq_of_support (K := K) n f gneg hgneg
  refine ⟨z, ?_⟩
  change awayToLaurent (K := K) n f z *
    AddMonoidAlgebra.single (positiveTwistShift m (f 0)) 1 = g
  rw [hz]
  change (g * AddMonoidAlgebra.single (twistShift m (f 0)) 1) *
    AddMonoidAlgebra.single (positiveTwistShift m (f 0)) 1 = g
  rw [mul_assoc, twistShift_mul_positiveTwistShift K m (f 0), mul_one]

/-- Restoring the actual chart frame gives a positive-degree Laurent
representative of the SAME native positive-twist section. -/
def p2PositiveNativeChartToLaurent
    (m n : ℕ) (f : Fin (n + 1) → Fin 3) :
    Γ(positiveSheafOfModules PS m, p2CechBasicOpen K n f) →+
      PlaneLaurentLocalization.LaurentPolynomial K where
  toFun s := p2PositiveAwayToLaurent K m n f
    (p2PositiveTwistChartAway K n f m (f 0)
      (p2Coordinate_zero_dvd_cechDenominator (K := K) n f) s)
  map_zero' := by simp [p2PositiveTwistChartAway]
  map_add' x y := by simp [p2PositiveTwistChartAway]

/-- The actual native positive-chart Laurent map is injective. -/
theorem p2PositiveNativeChartToLaurent_injective
    (m n : ℕ) (f : Fin (n + 1) → Fin 3) :
    Function.Injective (p2PositiveNativeChartToLaurent K m n f) := by
  intro x y h
  apply (ConcreteCategory.bijective_of_isIso
    (p2PositiveTwistBasicOpenIsoAway K (p2CechDenominator (K := K) n f)
      (n + 1) (p2CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
      (f 0) (p2Coordinate_zero_dvd_cechDenominator (K := K) n f) m).hom).1
  exact p2PositiveAwayToLaurent_injective K m n f h

/-- Native chart representatives have exactly the prescribed total degree
and can have negative exponents only at the actually inverted coordinates. -/
theorem p2PositiveNativeChartToLaurent_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 3)
    (s : Γ(positiveSheafOfModules PS m, p2CechBasicOpen K n f)) :
    ∀ a ∈ (p2PositiveNativeChartToLaurent K m n f s).coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
  exact p2PositiveAwayToLaurent_support K m n f
    (p2PositiveTwistChartAway K n f m (f 0)
      (p2Coordinate_zero_dvd_cechDenominator (K := K) n f) s)

/-- Every positive-degree Laurent representative with the actual coordinate
support comes from a section of the SAME native positive-twist sheaf. -/
theorem exists_p2PositiveNativeChartToLaurent_eq_of_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 3)
    (g : PlaneLaurentLocalization.LaurentPolynomial K)
    (hg : ∀ a ∈ g.coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ Set.range f) :
    ∃ s : Γ(positiveSheafOfModules PS m, p2CechBasicOpen K n f),
      p2PositiveNativeChartToLaurent K m n f s = g := by
  obtain ⟨z, hz⟩ := exists_p2PositiveAwayToLaurent_eq_of_support K m n f g hg
  let e := p2PositiveTwistBasicOpenIsoAway K (p2CechDenominator (K := K) n f)
    (n + 1) (p2CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
    (f 0) (p2Coordinate_zero_dvd_cechDenominator (K := K) n f) m
  refine ⟨e.inv z, ?_⟩
  change p2PositiveAwayToLaurent K m n f (e.hom (e.inv z)) = g
  rw [Iso.inv_hom_id_apply]
  exact hz


/-- The negative native chart map uses the actual multiplication frame
and the exact negative Laurent shift on the same original coordinate open. -/
def p2NegativeNativeChartToLaurent
    (m n : ℕ) (f : Fin (n + 1) → Fin 3) :
    Γ(sheafOfModules PS m, p2CechBasicOpen K n f) →+
      PlaneLaurentLocalization.LaurentPolynomial K where
  toFun s := twistAwayToLaurent (K := K) m n f
    ((p2NegativeTwistBasicOpenIsoAway K (p2CechDenominator (K := K) n f)
      (n + 1) (p2CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
      (f 0) (p2Coordinate_zero_dvd_cechDenominator (K := K) n f) m).hom s)
  map_zero' := by simp
  map_add' x y := by simp

theorem p2NegativeNativeChartToLaurent_injective
    (m n : ℕ) (f : Fin (n + 1) → Fin 3) :
    Function.Injective (p2NegativeNativeChartToLaurent K m n f) := by
  intro x y h
  apply (ConcreteCategory.bijective_of_isIso
    (p2NegativeTwistBasicOpenIsoAway K (p2CechDenominator (K := K) n f)
      (n + 1) (p2CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
      (f 0) (p2Coordinate_zero_dvd_cechDenominator (K := K) n f) m).hom).1
  exact twistAwayToLaurent_injective (K := K) m n f h

theorem p2NegativeNativeChartToLaurent_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 3)
    (s : Γ(sheafOfModules PS m, p2CechBasicOpen K n f)) :
    ∀ a ∈ (p2NegativeNativeChartToLaurent K m n f s).coeff.support,
      totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
  exact twistAwayToLaurent_support_properties (K := K) m n f _

theorem exists_p2NegativeNativeChartToLaurent_eq_of_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 3)
    (g : PlaneLaurentLocalization.LaurentPolynomial K)
    (hg : ∀ a ∈ g.coeff.support,
      totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f) :
    ∃ s : Γ(sheafOfModules PS m, p2CechBasicOpen K n f),
      p2NegativeNativeChartToLaurent K m n f s = g := by
  obtain ⟨z, hz⟩ := exists_twistAwayToLaurent_eq_of_support (K := K) m n f g hg
  let e := p2NegativeTwistBasicOpenIsoAway K (p2CechDenominator (K := K) n f)
    (n + 1) (p2CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
    (f 0) (p2Coordinate_zero_dvd_cechDenominator (K := K) n f) m
  refine ⟨e.inv z, ?_⟩
  change twistAwayToLaurent (K := K) m n f (e.hom (e.inv z)) = g
  rw [Iso.inv_hom_id_apply]
  exact hz

end PfaffianDescent.ProjectivePlaneNative
