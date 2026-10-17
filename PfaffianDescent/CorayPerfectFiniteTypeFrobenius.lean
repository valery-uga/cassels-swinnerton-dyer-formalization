import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! SOURCE ONLY / UNVERIFIED. Genuine finite Frobenius for a finite-type
algebra over ORIGINAL perfect K. The literal endomorphism is integral by
an explicit monic polynomial. Its coefficient composite is finite-type
from perfectness of K and the ORIGINAL algebraMap; native integral plus
finite type derives finiteness. No finite Frobenius or separability premise. -/
noncomputable section
namespace PfaffianDescent.Coray
universe u v

/-- Every actual iterated Frobenius endomorphism is integral, with the
literal monic equation X^(p^n)-C(a). No domain/perfection/finiteness input. -/
theorem iterateFrobenius_isIntegral
    (A : Type u) [CommRing A] (p : ℕ) [ExpChar A p] (n : ℕ) :
    (iterateFrobenius A p n).IsIntegral := by
  intro a
  refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.C a,
    Polynomial.monic_X_pow_sub_C a (pow_ne_zero n (expChar_ne_zero A p)), ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, iterateFrobenius_def, sub_self]

/-- A finite-type algebra over the SAME original perfect field has finite
literal iterated Frobenius. The target module is restriction along that
actual power map; no transported coefficient action or separability
certificate is used. Characteristic of A is derived from its ORIGINAL
K-algebra map, not selected independently. -/
theorem perfectField_finiteType_iterateFrobenius_finite
    (K : Type u) [Field K] [PerfectField K]
    (A : Type v) [CommRing A] [Nontrivial A]
    [Algebra K A] [Algebra.FiniteType K A]
    (p : ℕ) [ExpChar K p] (n : ℕ) :
    letI : ExpChar A p :=
      expChar_of_injective_ringHom (algebraMap K A).injective p
    (iterateFrobenius A p n).Finite := by
  letI : ExpChar A p :=
    expChar_of_injective_ringHom (algebraMap K A).injective p
  have hbase : (algebraMap K A).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hpower : (iterateFrobenius K p n).FiniteType :=
    RingHom.FiniteType.of_surjective _
      (bijective_iterateFrobenius K p n).2
  have hcoeff : ((iterateFrobenius A p n).comp (algebraMap K A)).FiniteType := by
    rw [← (algebraMap K A).iterateFrobenius_comm p n]
    exact hbase.comp hpower
  have htype : (iterateFrobenius A p n).FiniteType :=
    RingHom.FiniteType.of_comp_finiteType hcoeff
  exact (iterateFrobenius_isIntegral A p n).to_finite htype

end PfaffianDescent.Coray
