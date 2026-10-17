import PfaffianDescent.CorayLocalNormalizationDefect
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Source-only genuine affine normalization/residue rank bound. The original
R→B inclusion, original point map R→L, actual normalization residue map B→E
and original residue extension L→E are literal inputs to this generic cut.
Only the true diagram and B→E surjectivity are used, never a desired defect
bound or a residue-preserving lift. The original Scheme producer remains next. -/
noncomputable section
namespace PfaffianDescent.Coray
open Algebra Module
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Surjective normalization residue map induces an ACTUAL quotient map
B/image(R)→E/image(L). Its target dimension gives the full original-K rank
bound. R→L need not be surjective for this sufficient inequality. -/
theorem affineInclusionResidueDiagram_quotient_ground_rank_bound
    {K R B L E : Type*} [Field K] [CommRing R] [CommRing B]
    [Field L] [Field E] [Algebra K R] [Algebra K B] [Algebra R B]
    [IsScalarTower K R B] [Algebra K L] [Algebra K E]
    [Module.Finite K L] [Module.Finite K E]
    (a : R →ₐ[K] L) (j : L →ₐ[K] E) (beta : B →ₐ[K] E)
    (hbeta : Function.Surjective beta)
    (hcomm : ∀ r : R, beta (algebraMap R B r) = j (a r))
    [Module.Finite K (B ⧸ LinearMap.range (Algebra.linearMap R B))] :
    Module.finrank K E ≤
      Module.finrank K (B ⧸ LinearMap.range (Algebra.linearMap R B)) + Module.finrank K L := by
  classical
  let p : Submodule R B := LinearMap.range (Algebra.linearMap R B)
  let S : Submodule K B := p.restrictScalars K
  let T : Submodule K E := LinearMap.range j.toLinearMap
  let eD : (B ⧸ S) ≃ₗ[K] (B ⧸ p) := Submodule.Quotient.restrictScalarsEquiv K p
  letI : Module.Finite K (B ⧸ S) := Module.Finite.equiv eD.symm
  have hST : S ≤ T.comap beta.toLinearMap := by
    intro b hb
    obtain ⟨r, hr⟩ := hb
    change beta b ∈ LinearMap.range j.toLinearMap
    refine ⟨a r, ?_⟩
    exact (hcomm r).symm.trans (congrArg beta hr)
  let f : (B ⧸ S) →ₗ[K] (E ⧸ T) := S.mapQ T beta.toLinearMap hST
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨e, rfl⟩ := T.mkQ_surjective y
    obtain ⟨b, rfl⟩ := hbeta e
    exact ⟨S.mkQ b, rfl⟩
  have htarget := LinearMap.finrank_le_finrank_of_surjective (f := f) hf
  have htotal := T.finrank_quotient_add_finrank
  have hT : Module.finrank K T = Module.finrank K L :=
    LinearMap.finrank_range_of_inj j.injective
  have hD := eD.finrank_eq
  change Module.finrank K E ≤ Module.finrank K (B ⧸ p) + Module.finrank K L
  omega


/-- Genuine residue extension with original ground degree prime to three:
if the ACTUAL upper residue field's original-K degree has a factor three,
then its relative residue degree is at least three. No equal-residue lift. -/
theorem actualResidueExtension_ground_rank_ge_three_mul
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Module.Finite K L] [Module.Finite K E]
    (j : L →ₐ[K] E)
    (hcop : Nat.Coprime (Module.finrank K L) 3)
    (hthree : 3 ∣ Module.finrank K E) :
    3 * Module.finrank K L ≤ Module.finrank K E := by
  letI : Algebra L E := j.toRingHom.toAlgebra
  letI : IsScalarTower K L E :=
    IsScalarTower.of_algebraMap_eq (fun c => (j.commutes c).symm)
  have htower := Module.finrank_mul_finrank K L E
  have hEpos : 0 < Module.finrank K E := Module.finrank_pos
  have hepos : 0 < Module.finrank L E := by
    by_contra h
    have hezero : Module.finrank L E = 0 := by omega
    rw [hezero, mul_zero] at htower
    omega
  have hthreeProduct : 3 ∣ Module.finrank K L * Module.finrank L E :=
    htower.symm ▸ hthree
  have hrelative : 3 ∣ Module.finrank L E := hcop.symm.dvd_of_dvd_mul_left hthreeProduct
  have hrelativeLower : 3 ≤ Module.finrank L E := Nat.le_of_dvd hepos hrelative
  have hmul := Nat.mul_le_mul_left (Module.finrank K L) hrelativeLower
  have hground : 3 * Module.finrank K L ≤ Module.finrank K L * Module.finrank L E := by
    simpa only [Nat.mul_comm] using hmul
  exact hground.trans_eq htower


/-- Literal affine normalization defect B/R has ground dimension at least
TWO full original point degrees, using the genuine residue extension of
relative degree divisible by three. No defect/lift/degree-one certificate. -/
theorem affineNormalizationDefect_ground_rank_ge_twice_point_degree
    {K R F L E : Type*} [Field K] [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra K R] [Algebra K F]
    [IsScalarTower K R F] [Field L] [Field E] [Algebra K L] [Algebra K E]
    [Module.Finite K L] [Module.Finite K E]
    (a : R →ₐ[K] L) (j : L →ₐ[K] E) (beta : integralClosure R F →ₐ[K] E)
    (hbeta : Function.Surjective beta)
    (hcomm : ∀ r : R, beta (algebraMap R (integralClosure R F) r) = j (a r))
    [Module.Finite K (localNormalizationDefect R F)]
    (hcop : Nat.Coprime (Module.finrank K L) 3)
    (hthree : 3 ∣ Module.finrank K E) :
    2 * Module.finrank K L ≤ Module.finrank K (localNormalizationDefect R F) := by
  have hquotient := affineInclusionResidueDiagram_quotient_ground_rank_bound a j beta hbeta hcomm
  have hresidue := actualResidueExtension_ground_rank_ge_three_mul j hcop hthree
  change Module.finrank K E ≤ Module.finrank K (localNormalizationDefect R F) +
    Module.finrank K L at hquotient
  omega

end PfaffianDescent.Coray
