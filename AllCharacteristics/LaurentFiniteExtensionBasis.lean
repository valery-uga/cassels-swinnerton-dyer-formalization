import Mathlib.RingTheory.LaurentSeries
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! SOURCE ONLY / UNVERIFIED. Every finite coefficient-field basis gives an
actual Laurent-series basis, with no separability or infinite-field assumption.
The public finite-extension provider chooses the coefficient basis internally. -/
noncomputable section
namespace AllCharacteristics
open scoped BigOperators
open Module HahnSeries
universe u v
variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- The actual coefficientwise k((t))→L((t)) field embedding. -/
def laurentSeriesCoefficientMap : LaurentSeries k →+* LaurentSeries L where
  toFun s := s.map (algebraMap k L)
  map_zero' := by ext n; simp
  map_one' := by ext n; simp [HahnSeries.coeff_one]
  map_add' s t := by ext n; simp
  map_mul' s t := HahnSeries.map_mul (algebraMap k L).toNonUnitalRingHom

/-- The Laurent extension has its literal coefficient-map algebra structure. -/
instance laurentSeriesCoefficientAlgebra : Algebra (LaurentSeries k) (LaurentSeries L) :=
  (laurentSeriesCoefficientMap (k := k) (L := L)).toAlgebra

theorem laurentSeriesCoefficientMap_powerSeries (s : PowerSeries k) :
    laurentSeriesCoefficientMap (k := k) (L := L)
        (algebraMap (PowerSeries k) (LaurentSeries k) s) =
      algebraMap (PowerSeries L) (LaurentSeries L)
        (algebraMap (PowerSeries k) (PowerSeries L) s) := by
  ext n
  change algebraMap k L (((s : LaurentSeries k)).coeff n) =
    ((PowerSeries.map (algebraMap k L) s : PowerSeries L) : LaurentSeries L).coeff n
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs <;> simp

/-- Actual compatibility square, used for the generic point of the SAME
L[[t]] lift over the actual k((t)) pencil fiber. -/
theorem laurentSeriesCoefficientMap_comp_powerSeries :
    (laurentSeriesCoefficientMap (k := k) (L := L)).comp
        (algebraMap (PowerSeries k) (LaurentSeries k)) =
      (algebraMap (PowerSeries L) (LaurentSeries L)).comp
        (algebraMap (PowerSeries k) (PowerSeries L)) := by
  ext s
  exact laurentSeriesCoefficientMap_powerSeries s

/-- Multiplying a basis CONSTANT by a Laurent scalar is coefficientwise
the original k-linear scalar action on that basis element. -/
theorem laurentSeries_coeff_smul_constant
    (a : LaurentSeries k) (v : L) (n : ℤ) :
    (a • (HahnSeries.C v : LaurentSeries L)).coeff n = a.coeff n • v := by
  change ((laurentSeriesCoefficientMap (k := k) (L := L) a) *
    (HahnSeries.C v : LaurentSeries L)).coeff n = _
  rw [HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero]
  exact (Algebra.smul_def (a.coeff n) v).symm

variable {ι : Type v} [Fintype ι] (b : Basis ι k L)

/-- The actual coefficientwise projection has well-founded support because
its support is contained in the support of the original Laurent series. -/
def laurentSeriesBasisCoordinate (s : LaurentSeries L) (j : ι) : LaurentSeries k :=
  s.map (b.coord j)

/-- Constants from any given finite coefficient basis remain independent. -/
theorem laurentSeries_basis_constants_linearIndependent :
    LinearIndependent (LaurentSeries k)
      (fun j : ι => (HahnSeries.C (b j) : LaurentSeries L)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  ext n
  have hc := congrArg (fun s : LaurentSeries L => s.coeff n) ha
  simp only [HahnSeries.coeff_sum, laurentSeries_coeff_smul_constant,
    HahnSeries.coeff_zero] at hc
  exact (Fintype.linearIndependent_iff.mp b.linearIndependent
    (fun i => (a i).coeff n) hc) j

/-- Every actual Laurent series is the SAME finite sum of basis constants.
The scalar series are constructed from its coefficient-basis coordinates. -/
theorem laurentSeries_basis_constants_sum (s : LaurentSeries L) :
    (∑ j : ι, laurentSeriesBasisCoordinate b s j •
      (HahnSeries.C (b j) : LaurentSeries L)) = s := by
  ext n
  simp only [HahnSeries.coeff_sum, laurentSeries_coeff_smul_constant,
    laurentSeriesBasisCoordinate, HahnSeries.map_coeff, Basis.coord_apply]
  exact b.sum_repr (s.coeff n)

def laurentSeriesBasisOfCoefficientBasis :
    Basis ι (LaurentSeries k) (LaurentSeries L) :=
  Basis.mk (laurentSeries_basis_constants_linearIndependent b) (by
    intro s _
    rw [← laurentSeries_basis_constants_sum b s]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j)))

theorem laurentSeriesBasisOfCoefficientBasis_apply (j : ι) :
    laurentSeriesBasisOfCoefficientBasis b j = (HahnSeries.C (b j) : LaurentSeries L) :=
  Basis.mk_apply _ _ j

variable [Module.Finite k L]

/-- No coefficient basis is a public input; Module.finBasis is chosen inside. -/
def finiteExtensionLaurentBasis :
    Basis (Fin (Module.finrank k L)) (LaurentSeries k) (LaurentSeries L) :=
  laurentSeriesBasisOfCoefficientBasis (Module.finBasis k L)

instance finiteExtensionLaurent_moduleFinite :
    Module.Finite (LaurentSeries k) (LaurentSeries L) :=
  Module.Finite.of_basis (finiteExtensionLaurentBasis (k := k) (L := L))

/-- Literal [L((t)):k((t))]=[L:k], including inseparable finite extensions. -/
theorem finiteExtensionLaurent_finrank :
    Module.finrank (LaurentSeries k) (LaurentSeries L) = Module.finrank k L := by
  rw [Module.finrank_eq_card_basis (finiteExtensionLaurentBasis (k := k) (L := L)),
    Fintype.card_fin]

end AllCharacteristics
