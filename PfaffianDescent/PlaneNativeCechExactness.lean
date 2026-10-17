import PfaffianDescent.PlanePositiveNativeCechDifferential
import PfaffianDescent.PlaneNegativeNativeCechDifferential
import PfaffianDescent.PlaneLaurentCechExact
/-! SOURCE ONLY / UNCHECKED. Genuine native Fin3 Cech degree1/2 exactness.
The maps are the ACTUAL native positive/negative sheaf differentials and
actual derived chart Laurent maps. No exactness certificate is a premise.
Negative degree2 correctly requires m≤2; O(-3) is not contracted. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open CategoryTheory AlgebraicGeometry MvPolynomial
open ProjectiveNegativeTwist PlaneLaurentLocalization PlaneLaurentCechCore PlaneTwistLaurent
open scoped AddMonoidAlgebra BigOperators
universe u
variable (K : Type u) [Field K]
/-- Every native positive-twist Čech one-cocycle has a native boundary,
using the actual differential and actual chart representatives. -/
theorem p2PositiveNativeCech_exact_one (m : ℕ) :
    Function.Exact ((p2PositiveNativeCechComplex K m).d 0 1)
      ((p2PositiveNativeCechComplex K m).d 1 2) := by
  intro y
  constructor
  · intro hy
    have hdy : ∀ f, tupleD1 (p2PositiveNativeCechTermToLaurent K m 1 y) f = 0 := by
      intro f
      rw [← congrFun (p2PositiveNativeCechTermToLaurent_d_one K m y) f, hy]
      simp
    obtain ⟨xL, hxL, hdiff⟩ :=
      PlaneLaurentCechExact.laurent_tuple_exact_one_of_degree K (m : ℤ)
        (p2PositiveNativeCechTermToLaurent K m 1 y)
        (p2PositiveNativeCechTermToLaurent_support K m 1 y) hdy
    obtain ⟨x, hx⟩ := exists_p2PositiveNativeCechTermToLaurent_eq_of_support K m 0 xL hxL
    refine ⟨x, ?_⟩
    apply p2PositiveNativeCechTermToLaurent_injective K m 1
    rw [p2PositiveNativeCechTermToLaurent_d_zero, hx]
    funext f
    exact hdiff f
  · rintro ⟨x, rfl⟩
    exact ConcreteCategory.congr_hom ((p2PositiveNativeCechComplex K m).d_comp_d 0 1 2) x

/-- Every native positive-twist Čech two-cocycle has a native boundary,
using the actual differential and actual chart representatives. -/
theorem p2PositiveNativeCech_exact_two (m : ℕ) :
    Function.Exact ((p2PositiveNativeCechComplex K m).d 1 2)
      ((p2PositiveNativeCechComplex K m).d 2 3) := by
  intro z
  constructor
  · intro hz
    have hdz : ∀ f, tupleD2 (p2PositiveNativeCechTermToLaurent K m 2 z) f = 0 := by
      intro f
      rw [← congrFun (p2PositiveNativeCechTermToLaurent_d_two K m z) f, hz]
      simp
    obtain ⟨yL, hyL, hdiff⟩ :=
      PlaneLaurentCechExact.laurent_tuple_exact_two_of_degree K (m : ℤ) (by omega)
        (p2PositiveNativeCechTermToLaurent K m 2 z)
        (p2PositiveNativeCechTermToLaurent_support K m 2 z) hdz
    obtain ⟨y, hy⟩ := exists_p2PositiveNativeCechTermToLaurent_eq_of_support K m 1 yL hyL
    refine ⟨y, ?_⟩
    apply p2PositiveNativeCechTermToLaurent_injective K m 2
    rw [p2PositiveNativeCechTermToLaurent_d_one, hy]
    funext f
    exact hdiff f
  · rintro ⟨y, rfl⟩
    exact ConcreteCategory.congr_hom ((p2PositiveNativeCechComplex K m).d_comp_d 1 2 3) y


/-- Every native negative-twist Čech one-cocycle has a native boundary,
using the actual differential and actual chart representatives. -/
theorem p2NegativeNativeCech_exact_one (m : ℕ) :
    Function.Exact ((p2NegativeNativeCechComplex K m).d 0 1)
      ((p2NegativeNativeCechComplex K m).d 1 2) := by
  intro y
  constructor
  · intro hy
    have hdy : ∀ f, tupleD1 (p2NegativeNativeCechTermToLaurent K m 1 y) f = 0 := by
      intro f
      rw [← congrFun (p2NegativeNativeCechTermToLaurent_d_one K m y) f, hy]
      simp
    obtain ⟨xL, hxL, hdiff⟩ :=
      PlaneLaurentCechExact.laurent_tuple_exact_one_of_degree K (-(m : ℤ))
        (p2NegativeNativeCechTermToLaurent K m 1 y)
        (p2NegativeNativeCechTermToLaurent_support K m 1 y) hdy
    obtain ⟨x, hx⟩ := exists_p2NegativeNativeCechTermToLaurent_eq_of_support K m 0 xL hxL
    refine ⟨x, ?_⟩
    apply p2NegativeNativeCechTermToLaurent_injective K m 1
    rw [p2NegativeNativeCechTermToLaurent_d_zero, hx]
    funext f
    exact hdiff f
  · rintro ⟨x, rfl⟩
    exact ConcreteCategory.congr_hom ((p2NegativeNativeCechComplex K m).d_comp_d 0 1 2) x

/-- Every native negative-twist Čech two-cocycle has a native boundary,
using the actual differential and actual chart representatives. -/
theorem p2NegativeNativeCech_exact_two (m : ℕ) (hm : m ≤ 2) :
    Function.Exact ((p2NegativeNativeCechComplex K m).d 1 2)
      ((p2NegativeNativeCechComplex K m).d 2 3) := by
  intro z
  constructor
  · intro hz
    have hdz : ∀ f, tupleD2 (p2NegativeNativeCechTermToLaurent K m 2 z) f = 0 := by
      intro f
      rw [← congrFun (p2NegativeNativeCechTermToLaurent_d_two K m z) f, hz]
      simp
    obtain ⟨yL, hyL, hdiff⟩ :=
      PlaneLaurentCechExact.laurent_tuple_exact_two_of_degree K (-(m : ℤ)) (by omega)
        (p2NegativeNativeCechTermToLaurent K m 2 z)
        (p2NegativeNativeCechTermToLaurent_support K m 2 z) hdz
    obtain ⟨y, hy⟩ := exists_p2NegativeNativeCechTermToLaurent_eq_of_support K m 1 yL hyL
    refine ⟨y, ?_⟩
    apply p2NegativeNativeCechTermToLaurent_injective K m 2
    rw [p2NegativeNativeCechTermToLaurent_d_one, hy]
    funext f
    exact hdiff f
  · rintro ⟨y, rfl⟩
    exact ConcreteCategory.congr_hom ((p2NegativeNativeCechComplex K m).d_comp_d 1 2 3) y


end PfaffianDescent.ProjectivePlaneNative
